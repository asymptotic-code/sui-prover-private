// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Generic, declaration-driven loop-termination threading.
//!
//! Replaces the former per-function `thread_max_heapify_termination` and
//! `thread_derive_gas_termination` passes (which hard-coded the Move function
//! names `max_heapify_recursive` / `derive_reference_gas_price.while_0`). Instead
//! this pass is driven entirely by what the CLIENT declares in its
//! `Termination/<module>.lean` files: a `def <name>.loop_hyp` header marks a
//! recursive helper as terminating under a Lean-provided invariant. The backend
//! scans those headers into `Program::lean_termination_decls` before `finalize`.
//!
//! For each such helper `f` (self-recursive, in a mutual group, and NOT already
//! threaded by `emit_while` / the nested-loop / entry-cascade passes — those
//! register `loop_inv_hyps` themselves):
//!   * `f` (and its `.aborts` companion, when it too recurses) carries
//!     `hinv : <f>.loop_hyp …`; self-calls get an entry placeholder that the
//!     renderer turns into the preservation `by`-macro.
//!   * Callers in the SAME base-family (`<base>.while_N` / `.after`) get a plain
//!     entry placeholder — the while-loop "entered from its own continuation"
//!     shape (formerly the `derive_gas` case).
//!   * EXTERNAL callers (a different base function, e.g. `pop_max` calling
//!     `max_heapify_recursive`) instead get an `hpre : <caller>.precond …`
//!     size/entry precondition that propagates up the same-module call chain and
//!     stops at the module boundary with the client's `_requires` macro
//!     (formerly the `max_heapify` case). The `precond` predicates are a client
//!     contract declared alongside the measures.
//!
//! Conservative: a helper is only touched if the client wrote a `loop_hyp` for
//! it AND it is a genuinely self-recursive mutual-group helper not already
//! threaded. Everything else is left untouched.

use crate::data::ir::IRNode;
use crate::{FunctionID, LoopInvHyp, ModuleID, Program};
use std::collections::HashSet;

/// Strip `.aborts`, then any trailing `.while_N` / `.after` loop-helper suffix,
/// to recover the root Move function name a helper belongs to.
fn base_name(name: &str) -> &str {
    let n = name.strip_suffix(".aborts").unwrap_or(name);
    let n = n.strip_suffix(".after").unwrap_or(n);
    match n.rfind(".while_") {
        Some(i) => &n[..i],
        None => n,
    }
}

/// Append an `Abort` entry placeholder onto every value-arity call to `target`.
fn entry_placeholder(body: IRNode, target: FunctionID, value_arity: usize) -> IRNode {
    body.map(&mut |node| match node {
        IRNode::Call {
            function,
            type_args,
            args,
        } if function == target && args.len() == value_arity => {
            let mut args = args;
            args.push(IRNode::Abort { code: None });
            IRNode::Call {
                function,
                type_args,
                args,
            }
        }
        other => other,
    })
}

/// Mirror the renderer's identifier escaping for the simple temp-name cases that
/// appear as loop-helper value params (`$t4` -> `t_t4`, `i#1#0` -> `i_1_0`), so
/// the `precond` hypothesis type's argument names match the emitted binders.
fn escape_param(name: &str) -> String {
    let s = if let Some(rest) = name.strip_prefix('$') {
        format!("t_{}", rest)
    } else {
        name.replace('$', "_t_")
    };
    s.replace('#', "_")
}

fn place(program: &mut Program, id: FunctionID, target: FunctionID, arity: usize) {
    let body = std::mem::replace(&mut program.functions.get_mut(id).body, IRNode::unit());
    program.functions.get_mut(id).body = entry_placeholder(body, target, arity);
}

/// Whether `id` has a discharging `<base>_spec` companion co-located in a sibling
/// `_specs` module — the principled stop for cross-module precond propagation.
/// When such a companion exists, the precondition is discharged there (via
/// `requires`/`asserts`), so propagation must not climb past `id`. Mirrors the
/// spec-boundary detection in `callee_requires_entry`.
/// Whether `id` is itself a spec function — `<base>_spec` (and its `.aborts` /
/// `.ensures` / `.requires` companions), living in a `_specs` module. A spec is
/// the discharge boundary for cross-module precond propagation: it supplies the
/// callee precondition from its own `asserts`/`requires`, so the climb stops
/// there (the spec's call site still gets an entry placeholder, but the spec
/// itself is not given a propagated `hpre` and is not climbed past).
fn is_spec_function(program: &Program, id: FunctionID) -> bool {
    let f = program.functions.get(&id);
    let mod_name = program.modules.get(&f.module_id).name.clone();
    f.name.contains("_spec") && mod_name.to_lowercase().ends_with("specs")
}

pub fn thread_lean_terminations(program: &mut Program) {
    let loop_hyp_names = program.lean_termination_decls.loop_hyp.clone();
    if loop_hyp_names.is_empty() {
        return;
    }

    // Self-recursive mutual-group helpers the client declared a `loop_hyp` for
    // that some earlier pass has NOT already threaded (`emit_while` for Move
    // `loop_inv` annotations, the nested-loop pass, the entry cascade — all
    // populate `loop_inv_hyps`).
    let targets: Vec<(FunctionID, ModuleID, String)> = program
        .functions
        .iter()
        .filter(|(id, f)| {
            loop_hyp_names.contains(&f.name)
                && f.mutual_group_id.is_some()
                && !program.loop_inv_hyps.contains_key(id)
                && f.body.calls().any(|c| c == *id)
        })
        .map(|(id, f)| (id, f.module_id, f.name.clone()))
        .collect();

    for (target_id, module, tname) in targets {
        let tbase = base_name(&tname).to_string();
        let hook = format!("{}.loop_hyp", tname);
        let arity = program.functions.get(&target_id).signature.parameters.len();

        // Part A: hinv on the value helper + self-call entry placeholder.
        program.loop_inv_hyps.insert(
            target_id,
            LoopInvHyp {
                hyp_param: "hinv".to_string(),
                hook_name: hook.clone(),
            },
        );
        program
            .loop_invariants
            .entry(tbase.clone())
            .or_insert(target_id);
        place(program, target_id, target_id, arity);

        // The `.aborts` companion, if present.
        let aborts_id: Option<FunctionID> = program
            .functions
            .iter()
            .find(|(_, f)| f.module_id == module && f.name == format!("{}.aborts", tname))
            .map(|(id, _)| id);

        let mut helper_targets = HashSet::new();
        helper_targets.insert(target_id);
        if let Some(aid) = aborts_id {
            helper_targets.insert(aid);
        }

        // Callers of {value, aborts} in the same module, split by base.
        let callers: Vec<(FunctionID, String)> = program
            .functions
            .iter()
            .filter(|(id, f)| {
                !helper_targets.contains(id)
                    && f.module_id == module
                    && f.body.calls().any(|c| helper_targets.contains(&c))
            })
            .map(|(id, f)| (id, f.name.clone()))
            .collect();
        let same_base: Vec<FunctionID> = callers
            .iter()
            .filter(|(_, n)| base_name(n) == tbase)
            .map(|(id, _)| *id)
            .collect();
        let external: Vec<FunctionID> = callers
            .iter()
            .filter(|(_, n)| base_name(n) != tbase)
            .map(|(id, _)| *id)
            .collect();

        // Same-base continuation callers (`<base>.while_N.after` …): plain entry
        // placeholder — the loop re-entered from its own continuation.
        for c in &same_base {
            place(program, *c, target_id, arity);
        }

        if external.is_empty() {
            continue;
        }

        // External callers need the entry precondition established BEFORE the
        // call (the size/normalization assumption). Thread the `.aborts`
        // companion too (it mirrors the recursion), then propagate the precond.
        if let Some(aid) = aborts_id {
            program.loop_inv_hyps.insert(
                aid,
                LoopInvHyp {
                    hyp_param: "hinv".to_string(),
                    hook_name: hook.clone(),
                },
            );
            let aborts_arity = program.functions.get(&aid).signature.parameters.len();
            place(program, aid, target_id, arity);
            place(program, aid, aid, aborts_arity);
        }

        for caller_id in &external {
            for t in helper_targets.iter().copied().collect::<Vec<_>>() {
                let t_arity = program.functions.get(&t).signature.parameters.len();
                place(program, *caller_id, t, t_arity);
            }
        }

        // Precond worklist: each external caller gets `hpre : <base>.precond …`,
        // its callers get a placeholder, and same-module callers propagate.
        let mut worklist: Vec<FunctionID> = external.clone();
        let mut processed: HashSet<FunctionID> = HashSet::new();
        while let Some(caller_id) = worklist.pop() {
            if !processed.insert(caller_id) {
                continue;
            }
            // A function already threaded with its own loop invariant (`hinv :
            // <f>.loop_hyp …`) must NOT also get a separate `hpre` — its
            // `loop_hyp` already carries the callee precondition as a conjunct
            // (e.g. `derive_reference_gas_price.while_0.loop_hyp`'s third conjunct
            // IS `pop_max.precond`). Double-threading would leave its call sites
            // expecting two proof args while only one placeholder is emitted.
            // Skip the `hpre` here; the call into the loop-threaded callee still
            // discharges its precondition from `hinv`. Still climb so the precond
            // reaches this function's own callers via any other path.
            let already_threaded = program.loop_inv_hyps.contains_key(&caller_id)
                || loop_hyp_names.contains(&program.functions.get(&caller_id).name);
            if already_threaded {
                let self_arity = program.functions.get(&caller_id).signature.parameters.len();
                let outer_callers: Vec<FunctionID> = program
                    .functions
                    .iter()
                    .filter(|(id, f)| *id != caller_id && f.body.calls().any(|c| c == caller_id))
                    .map(|(id, _)| id)
                    .collect();
                for outer in outer_callers {
                    place(program, outer, caller_id, self_arity);
                    worklist.push(outer);
                }
                continue;
            }
            let (base, params): (String, Vec<String>) = {
                let f = program.functions.get(&caller_id);
                let base = f
                    .name
                    .strip_suffix(".aborts")
                    .unwrap_or(&f.name)
                    .to_string();
                // The `<base>.precond` predicate is shared by the value def and its
                // `.aborts` companion, but dead-param elimination prunes them
                // differently (a param can be live in `.aborts`'s abort conditions
                // yet dead in the value body, e.g. `advance_epoch`'s `new_epoch`).
                // To give BOTH references the same predicate at the same arity,
                // derive the argument list from the VALUE sibling's params, keeping
                // only those its own body references (a dead param can't affect the
                // precondition). The value params are a subset present in `.aborts`
                // scope too, so the names resolve at either site.
                let value_id = if f.name.ends_with(".aborts") {
                    program
                        .functions
                        .iter()
                        .find(|(_, g)| g.module_id == f.module_id && g.name == base)
                        .map(|(id, _)| id)
                        .unwrap_or(caller_id)
                } else {
                    caller_id
                };
                let vf = program.functions.get(&value_id);
                let used = vf.body.all_var_refs();
                let params = vf
                    .signature
                    .parameters
                    .iter()
                    .filter(|p| used.contains(&p.ssa_value))
                    .map(|p| p.name.clone())
                    .collect();
                (base, params)
            };
            if params.is_empty() {
                continue;
            }
            let esc: Vec<String> = params.iter().map(|p| escape_param(p)).collect();
            let prop = format!("{}.precond {}", base, esc.join(" "));
            program
                .fn_proof_params
                .entry(caller_id)
                .or_default()
                .push(("hpre".to_string(), prop));
            let name = program.functions.get(&caller_id).name.clone();
            program.loop_inv_entry_impls.insert(name);

            let self_arity = program.functions.get(&caller_id).signature.parameters.len();
            place(program, caller_id, caller_id, self_arity);

            let _ = module;
            // A spec function (`<base>_spec` and companions) is a propagation SINK:
            // it receives `hpre` (so its body discharges the impl precond it calls,
            // via `exact hpre`, leaving the precond as a STATED hypothesis on the
            // spec's own `_aborts`/`_ensures` theorem — sound, axiom-free), but the
            // climb stops here. Verification roots have no further callers anyway;
            // this bounds the cross-module propagation at the spec boundary
            // (`create_spec`, `advance_epoch_conservation_spec`) rather than
            // climbing into unrelated harness code.
            if is_spec_function(program, caller_id) {
                continue;
            }
            let outer_callers: Vec<FunctionID> = program
                .functions
                .iter()
                .filter(|(id, f)| *id != caller_id && f.body.calls().any(|c| c == caller_id))
                .map(|(id, _)| id)
                .collect();
            for outer in outer_callers {
                // Place the entry placeholder on every caller so its call site
                // type-checks (`by <callee>_requires`), and propagate the precond
                // up the call chain, including ACROSS module boundaries (e.g.
                // `Priority_queue.new` -> `Validator_set` heap construction ->
                // `Sui_system_state_inner.create` -> `create_spec`).
                place(program, outer, caller_id, self_arity);
                worklist.push(outer);
            }
        }
    }
}
