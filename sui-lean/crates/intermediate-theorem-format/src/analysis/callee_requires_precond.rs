// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Callee-`requires` PRECOND cascade.
//!
//! Sibling of `callee_requires_entry`, for the cases that pass can NOT handle.
//! `callee_requires_entry` threads a callee G's `requires` directly onto a
//! caller F when F's call args to G are all F's own parameters (so an
//! `hpre : <G>_spec.requires <F params>` can name them). It deliberately bails
//! when:
//!   * F is a `.while_`/`.after_` loop helper, or
//!   * F's call args to G reference loop-body temps / rebound locals (not F's
//!     params), so no param-typed `hpre` for G can name the slot.
//! In those cases the call to G keeps an `IRNode::Abort` placeholder in the
//! `requires` slot and the renderer falls through to bare `sorry`, tainting F
//! and everything downstream.
//!
//! This pass closes that gap the advance_epoch-`precond` way (mirroring
//! `lean_termination`): when the CLIENT declares a `<F-base>.precond` predicate
//! (scanned into `lean_termination_decls.precond`), thread
//! `hpre : <F-base>.precond <F's value params>` onto F, mark F so the renderer
//! emits the client `(by <G-namespace>_<G-base>_requires)` macro at G's call
//! site (the macro discharges G's `requires` from the in-scope precond), and
//! propagate the precond up F's caller chain — placing an entry placeholder at
//! each call site and threading `<caller-base>.precond` onto each caller — until
//! it reaches a spec function, where it stops as a STATED, sound hypothesis on
//! the spec's own obligation (no axiom, no `sorry`).
//!
//! Conservative / inert-by-default: nothing happens unless the client declared a
//! `.precond` for a function that actually calls a `callee_requires_impls` callee
//! with the trailing `sorry` placeholder. Without any `.precond` declarations the
//! output is byte-identical to before.

use crate::data::ir::IRNode;
use crate::{FunctionID, Program};
use std::collections::HashSet;

/// Mirror the renderer's identifier escaping for the simple temp-name cases that
/// appear as loop-helper / impl value params (`$t4` -> `t_t4`, `i#1#0` ->
/// `i_1_0`), so a threaded `precond` hypothesis type's argument names match the
/// emitted binders.
fn escape_param(name: &str) -> String {
    let s = if let Some(rest) = name.strip_prefix('$') {
        format!("t_{}", rest)
    } else {
        name.replace('$', "_t_")
    };
    s.replace('#', "_")
}

/// The `precond` base name a function declares against: its display name minus a
/// trailing `.aborts` (the `.precond` predicate is shared by the value def and
/// its `.aborts` companion). Loop-helper suffixes (`.while_N`, `.after`) are
/// kept — the client declares e.g. `emit_validator_epoch_events.while_0.precond`.
fn precond_base(name: &str) -> &str {
    name.strip_suffix(".aborts").unwrap_or(name)
}

/// Whether `id` is a spec function — `<base>_spec` (and its companions) living
/// in a `_specs` module. The discharge boundary for cross-module precond
/// propagation: it carries the precond as a STATED hypothesis on its own
/// obligation, and the climb stops there. Mirrors `lean_termination`.
fn is_spec_function(program: &Program, id: FunctionID) -> bool {
    let f = program.functions.get(&id);
    let mod_name = program.modules.get(&f.module_id).name.clone();
    f.name.contains("_spec") && mod_name.to_lowercase().ends_with("specs")
}

/// Append an `Abort` entry placeholder onto every value-arity call to `target`.
fn place(program: &mut Program, id: FunctionID, target: FunctionID, value_arity: usize) {
    let body = std::mem::replace(&mut program.functions.get_mut(id).body, IRNode::unit());
    let rewritten = body.map(&mut |node| match node {
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
    });
    program.functions.get_mut(id).body = rewritten;
}

/// Whether `body` contains a `Call` to one of `g_ids` whose trailing arg is the
/// `sorry` placeholder (the call sites the renderer turns into a bare `sorry`).
fn calls_g_with_placeholder(body: &IRNode, g_ids: &HashSet<FunctionID>) -> bool {
    body.fold(false, |acc, n| {
        if acc {
            return true;
        }
        if let IRNode::Call { function, args, .. } = n {
            if g_ids.contains(function) && matches!(args.last(), Some(IRNode::Abort { .. })) {
                return true;
            }
        }
        acc
    })
}

/// The `<base>.precond <escaped value params>` hypothesis type for `id`. For an
/// `.aborts` companion, the params are derived from the VALUE sibling (keeping
/// only those its own body references) so both references share one predicate at
/// one arity — exactly as `lean_termination` does for the size precond.
fn precond_prop(program: &Program, id: FunctionID) -> Option<String> {
    let f = program.functions.get(&id);
    let base = precond_base(&f.name).to_string();
    let value_id = if f.name.ends_with(".aborts") {
        program
            .functions
            .iter()
            .find(|(_, g)| g.module_id == f.module_id && g.name == base)
            .map(|(id, _)| id)
            .unwrap_or(id)
    } else {
        id
    };
    let vf = program.functions.get(&value_id);
    let used = vf.body.all_var_refs();
    let params: Vec<String> = vf
        .signature
        .parameters
        .iter()
        .filter(|p| used.contains(&p.ssa_value))
        .map(|p| escape_param(&p.name))
        .collect();
    if params.is_empty() {
        return None;
    }
    Some(format!("{}.precond {}", base, params.join(" ")))
}

/// Thread `hpre : <base>.precond …` onto `id` (idempotently), recording it for
/// `materialize_proof_params`.
fn thread_hpre(program: &mut Program, id: FunctionID) -> bool {
    if program
        .fn_proof_params
        .get(&id)
        .is_some_and(|v| v.iter().any(|(n, _)| n == "hpre"))
        || program.loop_inv_hyps.contains_key(&id)
    {
        return false;
    }
    let Some(prop) = precond_prop(program, id) else {
        return false;
    };
    program
        .fn_proof_params
        .entry(id)
        .or_default()
        .push(("hpre".to_string(), prop));
    true
}

pub fn thread_callee_requires_precond(program: &mut Program) {
    if program.lean_termination_decls.precond.is_empty() || program.callee_requires_impls.is_empty()
    {
        return;
    }
    let precond_names = program.lean_termination_decls.precond.clone();
    let g_ids = program.callee_requires_impls.clone();

    // F candidates: a function NOT itself a `callee_requires_impls` callee, which
    // calls some G with the trailing `sorry` placeholder, and whose `precond`
    // base name the client declared. These are exactly the `.while_`/`.after_`
    // helpers + plain defs / `.aborts` that `callee_requires_entry` could not
    // thread.
    let f_candidates: Vec<FunctionID> = program
        .functions
        .iter()
        .filter(|(id, f)| {
            !g_ids.contains(id)
                && precond_names.contains(precond_base(&f.name))
                && calls_g_with_placeholder(&f.body, &g_ids)
        })
        .map(|(id, _)| id)
        .collect();

    for f_id in f_candidates {
        if !thread_hpre(program, f_id) {
            continue;
        }
        // F's call to G keeps its `Abort` slot; mark F so the renderer emits the
        // client `(by <G>_requires)` macro there instead of bare `sorry`.
        program.callee_requires_precond_callers.insert(f_id);

        // Propagate the precond up F's caller chain. Each threaded function X
        // gained an `hpre` param, so callers must pass an extra arg into X's
        // call: place an `Abort` entry placeholder there and insert X's NAME into
        // `loop_inv_entry_impls` so the renderer emits `(by <X>_requires)` for
        // those calls (discharged from the caller's own threaded `hpre`). The
        // climb stops at spec functions (the STATED-hypothesis boundary).
        let mut worklist: Vec<FunctionID> = vec![f_id];
        let mut processed: HashSet<FunctionID> = HashSet::new();
        while let Some(x_id) = worklist.pop() {
            if !processed.insert(x_id) {
                continue;
            }
            let x_name = program.functions.get(&x_id).name.clone();
            program.loop_inv_entry_impls.insert(x_name);
            let x_arity = program.functions.get(&x_id).signature.parameters.len();

            // A self-recursive loop helper (F1: `emit_validator_epoch_events.while_0`)
            // also calls ITSELF; that self-call now needs the extra `hpre` arg.
            // Place a placeholder there too (the renderer discharges it with the
            // client preservation macro from the in-scope `hpre`).
            if program.functions.get(&x_id).body.calls().any(|c| c == x_id) {
                place(program, x_id, x_id, x_arity);
            }

            if is_spec_function(program, x_id) {
                continue;
            }
            let callers: Vec<FunctionID> = program
                .functions
                .iter()
                .filter(|(id, f)| *id != x_id && f.body.calls().any(|c| c == x_id))
                .map(|(id, _)| id)
                .collect();
            for caller_id in callers {
                // Always place the extra-arg placeholder at the caller's call to X
                // so the renderer emits `(by <X>_requires)` there (X gained an
                // `hpre` param and needs the arg supplied).
                place(program, caller_id, x_id, x_arity);
                // Continue the climb (thread the caller's OWN precond + recurse)
                // ONLY if the client declared a `.precond` for this caller.
                // Otherwise stop here: this caller is the client-chosen boundary —
                // its `(by <X>_requires)` macro discharges X's precond from the
                // caller's OWN stated hypothesis, exactly like the `is_spec_function`
                // boundary. This lets the client cap the declaration burden at any
                // point instead of being forced to declare `.precond` for the entire
                // transitive caller tree up to `_spec`.
                if precond_names.contains(precond_base(&program.functions.get(&caller_id).name)) {
                    if thread_hpre(program, caller_id) {
                        worklist.push(caller_id);
                    }
                }
            }
        }
    }
}
