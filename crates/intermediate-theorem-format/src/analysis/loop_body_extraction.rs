// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Loop-body extraction.
//!
//! A while-loop is lowered into a self-recursive helper `<f>.while_N` that Lean
//! elaborates via well-founded recursion. Building the `WellFounded.fix` term
//! and — far more expensive — its equational lemmas requires constructing a
//! proof/congruence that spans the ENTIRE loop body. That work scales with the
//! body's term size, so a loop whose per-iteration body is heavy (deep struct
//! builders, wide `BoundedNat` arithmetic) can hang Lean for minutes and many
//! GB during BOTH type-check and `lean -c` codegen (observed on sui-system's
//! `Voting_power_tests`, which is otherwise trivial).
//!
//! The fix is purely structural and semantics-preserving: hoist the
//! per-iteration body out of the recursive function into a sibling
//! NON-recursive helper `<f>.while_N.step`, leaving the recursive function with
//! a tiny body (guard, one call to the step helper, the recursive call). The WF
//! machinery now spans almost nothing; the step helper is non-recursive, so no
//! WF machinery touches it. The loop stays a real (sorry-terminated but
//! unfoldable) `def`.
//!
//! Scope (conservative — every case not handled keeps the original WF form):
//!   * only pure value-form `<base>.while_N` helpers (never `.after`/`.aborts`),
//!   * generic loops included: the helper clones the loop's type params and
//!     inherits its `HasCode`/`BagU` instance-param entries,
//!   * only the canonical shape `<guard lets>; if g then <spine> else <spine>`
//!     where exactly one branch's top-level Let-spine contains the single
//!     self-recursive call,
//!   * only when the extracted prefix is heavy enough to be worth a helper.

use crate::data::functions::{Function, FunctionSignature, Parameter};
use crate::data::variables::VariableRegistry;
use crate::{FunctionID, IRNode, Program, TempId, Type};
use std::collections::BTreeSet;

pub fn extract_loop_bodies(program: &mut Program) {
    let loop_ids: Vec<FunctionID> = program
        .functions
        .iter()
        .filter(|(_, f)| is_extractable_loop(f, program))
        .map(|(id, _)| id)
        .collect();

    for fid in loop_ids {
        // The analysis walks the loop body building a type registry via
        // `get_type`, which panics on IR shapes it cannot type (non-linear
        // pre-`If` scopes, phi rebinds, etc.). Extraction is a best-effort
        // optimization: on any such failure, skip this loop and leave it in its
        // original — correct, if slow — WF form. Catch per loop so one awkward
        // body never aborts the whole run.
        let plan = {
            let prev = std::panic::take_hook();
            std::panic::set_hook(Box::new(|_| {}));
            let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                plan_extraction(program, fid)
            }));
            std::panic::set_hook(prev);
            r.ok().flatten()
        };
        if let Some(plan) = plan {
            apply_plan(program, fid, plan);
        }
    }
}

fn is_extractable_loop(f: &Function, program: &Program) -> bool {
    if f.is_native || f.is_uninterpreted || f.mutual_group_id.is_none() {
        return false;
    }
    // Generic loops are extractable too: the helper clones the loop's type
    // params and `apply_plan` copies the loop's `HasCode`/`BagU` instance-param
    // entries, so the call site instantiates with the loop's own params and
    // Lean forwards the in-scope instance binders. (Previously skipped; cetus
    // world-mode `swap_in_pool.while_0` — generic over the pool's coin types —
    // then hit the 8M-heartbeat whnf wall in WF eq-lemma generation.)
    // Exactly a value-form `<base>.while_<digits>` (excludes `.after`, `.aborts`,
    // `.ensures`, whose suffix after the digits is non-empty).
    let Some(idx) = f.name.rfind(".while_") else {
        return false;
    };
    let suffix = &f.name[idx + ".while_".len()..];
    if suffix.is_empty() || !suffix.chars().all(|c| c.is_ascii_digit()) {
        return false;
    }
    // Only sorry-fallback loops (rendered `decreasing_by all_goals sorry`).
    // Extraction hides the per-iteration body — including the loop variable's
    // increment — inside the opaque `.step` call, so a loop with a real
    // termination measure or a `loop_inv` (whose `decreasing_by` must SEE that
    // progress) must keep its body inline. These loops prove nothing about
    // themselves anyway (their equations rest on `sorry`), so hoisting is sound.
    let base_name = &f.name[..idx];
    let decls = &program.lean_termination_decls;
    if program.loop_invariants.contains_key(base_name)
        || decls.termination.contains(&f.name)
        || decls.loop_hyp.contains(base_name)
        || decls.precond.contains(base_name)
    {
        return false;
    }
    true
}

/// Apply a validated extraction plan: create the `.step` helper and rewrite the
/// loop to call it. Uses only cloned plan data (no `get_type`), so it never
/// panics.
fn apply_plan(program: &mut Program, fid: FunctionID, plan: Plan) {
    // Build the step helper.
    let ret_type = if plan.live_out_types.len() == 1 {
        plan.live_out_types[0].clone()
    } else {
        Type::Tuple(plan.live_out_types.clone())
    };
    let ret_expr = if plan.live_out.len() == 1 {
        IRNode::Var(plan.live_out[0].clone())
    } else {
        IRNode::Tuple(plan.live_out.iter().cloned().map(IRNode::Var).collect())
    };
    let helper_body = rebuild_lets(&plan.prefix, ret_expr);
    let loop_type_params = program.functions.get(&fid).signature.type_params.clone();
    let helper = Function {
        module_id: plan.module_id,
        name: format!("{}.step", program.functions.get(&fid).name),
        signature: FunctionSignature {
            type_params: loop_type_params.clone(),
            parameters: plan
                .live_in
                .iter()
                .map(|(name, ty)| Parameter {
                    name: name.to_string(),
                    param_type: ty.clone(),
                    ssa_value: name.clone(),
                })
                .collect(),
            proof_params: Vec::new(),
            return_type: ret_type,
        },
        body: helper_body,
        theorem: None,
        is_native: false,
        mutual_group_id: None,
        test_expectation: None,
        is_uninterpreted: false,
    };
    let helper_id = program.functions.add(helper);
    // The helper's body is a subset of the loop's, so the loop's instance-param
    // requirements (computed pre-extraction over the FULL body) are a safe
    // superset for the helper; the call site synthesizes each binder from the
    // loop's own in-scope instances.
    if let Some(set) = program.fn_hascode_params.get(&fid).cloned() {
        program.fn_hascode_params.insert(helper_id, set);
    }
    if let Some(set) = program.fn_bagu_params.get(&fid).cloned() {
        program.fn_bagu_params.insert(helper_id, set);
    }

    // Rewrite the loop: replace the extracted prefix with a single call to the
    // step helper + a destructuring bind of the live-out vars.
    let call = IRNode::Call {
        function: helper_id,
        type_args: (0..loop_type_params.len())
            .map(|i| Type::TypeParameter(i as u16))
            .collect(),
        args: plan
            .live_in
            .iter()
            .map(|(name, _)| IRNode::Var(name.clone()))
            .collect(),
    };
    let call_let = IRNode::Let {
        pattern: plan.live_out.clone(),
        value: Box::new(call),
        body: Box::new(plan.rest),
    };
    let new_body = splice_branch(
        program.functions.get(&fid).body.clone(),
        &plan.path,
        call_let,
    );
    program.functions.get_mut(fid).body = new_body;
}

struct Plan {
    module_id: crate::ModuleID,
    /// Path (branch choices) from the function body root to the recursive spine.
    path: Vec<Branch>,
    /// Extracted `(pattern, value)` bindings, in order.
    prefix: Vec<(Vec<TempId>, IRNode)>,
    /// Helper parameters: live-in vars with types.
    live_in: Vec<(TempId, Type)>,
    /// Live-out vars (prefix-defined, used by `rest`), in first-def order.
    live_out: Vec<TempId>,
    live_out_types: Vec<Type>,
    /// The self-call Let onwards, unchanged.
    rest: IRNode,
}

#[derive(Clone)]
enum Branch {
    /// Descend through a leading `Let` (guard binding etc.).
    Let,
    /// Descend into the then-branch of an `If`.
    Then,
    /// Descend into the else-branch of an `If`.
    Else,
}

fn plan_extraction(program: &Program, fid: FunctionID) -> Option<Plan> {
    let f = program.functions.get(&fid);
    let mut reg = f.param_registry(program);
    let mut node = &f.body;
    let mut path: Vec<Branch> = Vec::new();

    // Descend through leading `Let`s and any number of nested `If`s where
    // exactly ONE branch (sub)tree contains the self-call (guard aborts / early
    // exits sit in the other branch). When the current level's spine ends at
    // the recursion — a Let value calling the loop, a bare tail call, or a
    // terminal `If` recursing in BOTH branches — cut there: the spine's Lets
    // become the extracted prefix and everything from the recursion onward is
    // spliced back unchanged. Intermediate Lets between nested single-recursive
    // Ifs stay in the loop (conservative).
    let mut crossed_if = false;
    loop {
        if crossed_if {
            match classify_spine(node, fid) {
                SpineClass::Spine => {
                    return plan_from_spine(program, fid, f.module_id, &reg, node, path);
                }
                SpineClass::Descend => {}
                SpineClass::Bail => return None,
            }
        }
        match node {
            IRNode::Let { value, body, .. } => {
                // A self-call in a leading Let before any If is not the
                // canonical shape — bail rather than guess.
                if value.calls().any(|c| c == fid) {
                    return None;
                }
                reg.add_node(node);
                path.push(Branch::Let);
                node = body;
            }
            IRNode::If {
                then_branch,
                else_branch,
                ..
            } => {
                let then_rec = then_branch.calls().any(|c| c == fid);
                let else_rec = else_branch.calls().any(|c| c == fid);
                let (branch, dir) = match (then_rec, else_rec) {
                    (true, false) => (then_branch.as_ref(), Branch::Then),
                    (false, true) => (else_branch.as_ref(), Branch::Else),
                    _ => return None,
                };
                crossed_if = true;
                path.push(dir);
                node = branch;
            }
            _ => return None,
        }
    }
}

enum SpineClass {
    /// This level's top-level Let-spine reaches the recursion — cut here.
    Spine,
    /// The spine ends in an `If` with exactly one recursive branch — descend.
    Descend,
    /// No recursion reachable in the canonical shape from here.
    Bail,
}

fn classify_spine(node: &IRNode, fid: FunctionID) -> SpineClass {
    let mut cur = node;
    while let IRNode::Let { value, body, .. } = cur {
        if value.calls().any(|c| c == fid) {
            return SpineClass::Spine;
        }
        cur = body;
    }
    match cur {
        IRNode::If {
            then_branch,
            else_branch,
            ..
        } => {
            let t = then_branch.calls().any(|c| c == fid);
            let e = else_branch.calls().any(|c| c == fid);
            match (t, e) {
                (true, true) => SpineClass::Spine,
                (true, false) | (false, true) => SpineClass::Descend,
                (false, false) => SpineClass::Bail,
            }
        }
        other => {
            if other.calls().any(|c| c == fid) {
                SpineClass::Spine
            } else {
                SpineClass::Bail
            }
        }
    }
}

/// True if the top-level Let-spine of `node` contains the self-recursive call —
/// either a Let whose value calls `fid`, or a bare tail call to `fid` that
/// terminates the spine (the tail-recursive loop shape).
fn spine_has_self_call(node: &IRNode, fid: FunctionID) -> bool {
    let mut cur = node;
    while let IRNode::Let { value, body, .. } = cur {
        if value.calls().any(|c| c == fid) {
            return true;
        }
        cur = body;
    }
    cur.calls().any(|c| c == fid)
}

fn plan_from_spine(
    program: &Program,
    fid: FunctionID,
    module_id: crate::ModuleID,
    reg_at_branch: &VariableRegistry,
    branch: &IRNode,
    path: Vec<Branch>,
) -> Option<Plan> {
    // Split the spine at the self-call: either a Let whose value is the
    // self-call (result-destructured loop), or a bare tail call to `fid`
    // terminating the Let-spine (tail-recursive loop). Everything after that
    // point becomes `rest` (spliced back unchanged); the Lets before it are the
    // extractable prefix.
    let mut prefix: Vec<(Vec<TempId>, IRNode)> = Vec::new();
    let mut cur = branch;
    let rest;
    loop {
        match cur {
            IRNode::Let {
                pattern,
                value,
                body,
            } => {
                if value.calls().any(|c| c == fid) {
                    rest = cur.clone();
                    break;
                }
                prefix.push((pattern.clone(), (**value).clone()));
                cur = body;
            }
            terminal => {
                // Bare tail call, or a terminal `If` recursing in both
                // branches: splice the whole terminal back unchanged.
                if terminal.calls().any(|c| c == fid) {
                    rest = cur.clone();
                    break;
                }
                return None;
            }
        }
    }
    if prefix.is_empty() {
        return None;
    }

    // Type every prefix binding, extending a clone of the branch-entry scope.
    let mut reg = reg_at_branch.clone();
    for (pattern, value) in &prefix {
        let tmp = IRNode::Let {
            pattern: pattern.clone(),
            value: Box::new(value.clone()),
            body: Box::new(IRNode::Tuple(Vec::new())),
        };
        reg.add_node(&tmp);
    }

    // live-out: prefix-defined vars used by `rest`, in first-def order. A var is
    // "prefix-defined" if the prefix rebinds it — via a `Let` pattern OR an
    // effect node that reassigns a name without a pattern: `WriteBack{parent}`
    // (renders `let parent := …`) and `WriteRef` into a `Var`. The IR's own
    // `defined_vars` reports NEITHER (it treats `WriteBack` as use-only), so
    // missing them would silently keep a threaded value (e.g. a mutated
    // `TxContext`) bound to the STALE loop parameter instead of the updated one.
    let rest_free = rest.free_vars();
    let mut defined: Vec<TempId> = Vec::new();
    for (pattern, value) in &prefix {
        for v in pattern {
            defined.push(v.clone());
        }
        collect_effect_defines(value, &mut defined);
    }
    let mut seen: BTreeSet<TempId> = BTreeSet::new();
    let mut live_out: Vec<TempId> = Vec::new();
    for v in &defined {
        if rest_free.contains(v) && seen.insert(v.clone()) {
            live_out.push(v.clone());
        }
    }
    if live_out.is_empty() {
        return None;
    }

    // live-in: a var whose incoming (outer-scope) value is read by the prefix.
    // The IR rebinds in SSA style (`let ctx := f ctx; WriteBack(_, ctx)`), so a
    // var can be BOTH read from outside early AND redefined later — it is still
    // a live-in. Walk in order, tracking vars defined SO FAR; a value's free var
    // not yet defined comes from outside. (Set-based free/defined subtraction
    // would wrongly drop such rebound vars, yielding a helper that references an
    // undefined parameter.)
    let mut defined_so_far: BTreeSet<TempId> = BTreeSet::new();
    let mut live_in_order: Vec<TempId> = Vec::new();
    let mut live_in_seen: BTreeSet<TempId> = BTreeSet::new();
    for (pattern, value) in &prefix {
        for v in value.free_vars() {
            if !defined_so_far.contains(&v) && live_in_seen.insert(v.clone()) {
                live_in_order.push(v);
            }
        }
        for v in pattern {
            defined_so_far.insert(v.clone());
        }
        let mut effect_defs = Vec::new();
        collect_effect_defines(value, &mut effect_defs);
        defined_so_far.extend(effect_defs);
    }
    let mut live_in: Vec<(TempId, Type)> = Vec::new();
    for v in &live_in_order {
        if !reg_at_branch.contains(v) {
            return None;
        }
        live_in.push((v.clone(), reg_at_branch.get_type(v).clone()));
    }

    let live_out_types: Vec<Type> = live_out.iter().map(|v| reg.get_type(v).clone()).collect();

    Some(Plan {
        module_id,
        path,
        prefix,
        live_in,
        live_out,
        live_out_types,
        rest,
    })
}

/// Collect the variables a Let value REASSIGNS by side effect (no pattern):
/// `WriteBack{parent}` and `WriteRef` whose reference is a bare `Var`. Scans the
/// whole value subtree so nested sequencing is covered. These render as
/// `let <name> := …` rebinds, so downstream code sees the updated value; the
/// extraction must treat them as prefix definitions (candidate live-outs).
fn collect_effect_defines(value: &IRNode, out: &mut Vec<TempId>) {
    for n in value.iter() {
        match n {
            IRNode::WriteBack { parent, .. } => out.push(parent.clone()),
            IRNode::WriteRef { reference, .. } => {
                if let IRNode::Var(x) = reference.as_ref() {
                    out.push(x.clone());
                }
            }
            _ => {}
        }
    }
}

/// Rebuild a Let-spine from `(pattern, value)` bindings terminating in `tail`.
fn rebuild_lets(prefix: &[(Vec<TempId>, IRNode)], tail: IRNode) -> IRNode {
    let mut node = tail;
    for (pattern, value) in prefix.iter().rev() {
        node = IRNode::Let {
            pattern: pattern.clone(),
            value: Box::new(value.clone()),
            body: Box::new(node),
        };
    }
    node
}

/// Replace the recursive spine (reached by following `path` from `node`) with
/// `replacement`. The path leads through leading `Let`s into one `If` branch;
/// the branch's own prefix Lets are dropped and `replacement` installed.
fn splice_branch(node: IRNode, path: &[Branch], replacement: IRNode) -> IRNode {
    let mut path_iter = path.iter();
    splice_rec(node, &mut path_iter, &replacement)
}

fn splice_rec<'a>(
    node: IRNode,
    path: &mut impl Iterator<Item = &'a Branch>,
    replacement: &IRNode,
) -> IRNode {
    match path.next() {
        None => replacement.clone(),
        Some(Branch::Let) => match node {
            IRNode::Let {
                pattern,
                value,
                body,
            } => IRNode::Let {
                pattern,
                value,
                body: Box::new(splice_rec(*body, path, replacement)),
            },
            other => other,
        },
        Some(Branch::Then) => match node {
            IRNode::If {
                cond,
                then_branch,
                else_branch,
            } => IRNode::If {
                cond,
                then_branch: Box::new(splice_rec(*then_branch, path, replacement)),
                else_branch,
            },
            other => other,
        },
        Some(Branch::Else) => match node {
            IRNode::If {
                cond,
                then_branch,
                else_branch,
            } => IRNode::If {
                cond,
                then_branch,
                else_branch: Box::new(splice_rec(*else_branch, path, replacement)),
            },
            other => other,
        },
    }
}
