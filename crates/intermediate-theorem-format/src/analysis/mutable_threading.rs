// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Mutable reference pass.
//!
//! Two independent concerns:
//! - **Mutable params**: Strip `&mut` from params, augment return type with param
//!   states so callers can rebind. For non-native functions, `wrap_tail` rewrites
//!   the body to return the augmented tuple. For non-MutableReference-returning
//!   natives (e.g., `pop_back`), the hand-written Lean already returns the
//!   augmented tuple. Native MutableReference-returning functions (e.g.,
//!   `borrow_mut`) are excluded from augmentation — their Lean definitions return
//!   `Mutable` directly and write-back flows through the Mutable chain.
//! - **Mutable returns**: The renderer handles local borrow plumbing via
//!   `MutableBorrow`, `ReadRef`, `WriteRef`, and `WriteBack`.
//!
//! The renderer handles local borrow plumbing:
//! - `MutableBorrow` → `Mutable.mk val (fun p => reconstruct)`
//! - `ReadRef(expr)` → `Mutable.val expr`
//! - `WriteRef { ref, val }` → `Mutable.reconstruct ref val`

use crate::data::functions::FunctionID;
use crate::data::ir::{IRNode, WriteBackEdge};
use crate::data::types::{TempId, Type};
use crate::Program;
use std::collections::{BTreeMap, BTreeSet};
use std::rc::Rc;

fn returns_mutable_ref(fid: FunctionID, program: &Program) -> bool {
    matches!(
        &program.functions.get(&fid).signature.return_type,
        Type::MutableReference(_, _)
    )
}

#[derive(Debug, Clone)]
struct MutableParamInfo {
    param_index: usize,
    ssa_name: TempId,
    inner_type: Type,
}

#[derive(Debug, Clone)]
struct TransformInfo {
    mutable_params: Vec<MutableParamInfo>,
    original_return_type: Type,
}

#[derive(Debug, Clone)]
struct BorrowInfo {
    parent_var: TempId,
}

// ============================================================================
// Entry point
// ============================================================================

pub fn thread_mutables(program: &mut Program) {
    // Debug: dump WriteBack nodes for push_back before any transformation
    // Collect mutable param info for ALL functions (before any modification)
    let all_mutable_params: BTreeMap<FunctionID, Vec<MutableParamInfo>> = program
        .functions
        .iter()
        .filter_map(|(fid, func)| {
            let mps: Vec<MutableParamInfo> = func
                .signature
                .parameters
                .iter()
                .enumerate()
                .filter_map(|(i, p)| match &p.param_type {
                    Type::MutableReference(inner, _) => Some(MutableParamInfo {
                        param_index: i,
                        ssa_name: p.ssa_value.clone(),
                        inner_type: *inner.clone(),
                    }),
                    _ => None,
                })
                .collect();
            if mps.is_empty() {
                None
            } else {
                Some((fid, mps))
            }
        })
        .collect();

    if all_mutable_params.is_empty() {
        return;
    }

    // Transform map: all non-spec functions with mutable params.
    let transform_map: BTreeMap<FunctionID, TransformInfo> = all_mutable_params
        .iter()
        .filter(|(&fid, _)| {
            let func = program.functions.get(&fid);
            if func.name.ends_with(".aborts")
                || func.name.contains(".requires")
                || func.name.contains(".ensures")
            {
                return false;
            }
            true
        })
        .map(|(&fid, mps)| {
            let func = program.functions.get(&fid);
            (
                fid,
                TransformInfo {
                    mutable_params: mps.clone(),
                    original_return_type: func.signature.return_type.clone(),
                },
            )
        })
        .collect();

    // 1a. Strip MutableReference from params on ALL functions with mutable params
    for (&fid, _mps) in &all_mutable_params {
        let func = program.functions.get_mut(fid);
        for param in &mut func.signature.parameters {
            if let Type::MutableReference(inner, _) = &param.param_type {
                param.param_type = *inner.clone();
            }
        }
    }

    // 1b. Augment return types: append mutable param inner types to the return tuple.
    // MutableReference is preserved in the return type — stripping it would make the
    // signature lie about what the function actually returns (a Mutable wrapper).
    for (&fid, info) in &transform_map {
        let func = program.functions.get_mut(fid);
        let inner_types: Vec<Type> = info
            .mutable_params
            .iter()
            .map(|mp| mp.inner_type.clone())
            .collect();
        let is_mutref = matches!(&info.original_return_type, Type::MutableReference(_, _));
        let base_return = if is_mutref {
            func.signature.return_type.clone()
        } else {
            func.signature.return_type.clone().strip_mutable_ref()
        };
        func.signature.return_type = augmented_return(&base_return, &inner_types);
    }

    // 1c. Strip ReadRef on params that were just converted from MutableReference to plain.
    // The IR body has ReadRef(Var(param)) to read from mutable params, but now params
    // are plain so ReadRef is identity — just use the variable directly.
    for (&fid, mps) in &all_mutable_params {
        let func = program.functions.get_mut(fid);
        if func.is_native {
            continue;
        }
        let param_names: BTreeSet<TempId> = mps.iter().map(|mp| mp.ssa_name.clone()).collect();
        let body = std::mem::take(&mut func.body);
        func.body = strip_readrefs_for(body, &param_names);
    }

    // 1e. Convert WriteRef targeting direct mutable params to plain rebindings.
    // Move bytecode `*self = val` compiles to `WriteRef($tN, val)` where `$tN`
    // is a copy of the param. Trace through copies to find param targets.
    for (&fid, mps) in &all_mutable_params {
        let func = program.functions.get_mut(fid);
        if func.is_native {
            continue;
        }
        let param_names: BTreeSet<TempId> = mps.iter().map(|mp| mp.ssa_name.clone()).collect();
        let copy_to_param = build_copy_to_param_map(&func.body, &param_names);
        let body = std::mem::take(&mut func.body);
        func.body = strip_param_writerefs(body, &param_names, &copy_to_param);
    }

    // Augmented mutref functions: all functions that originally returned MutableReference
    // and also have mutable params (thus got augmented in step 1b). Their augmented return
    // type is Tuple([MutableReference(...), param_types...]), so returns_mutable_ref()
    // returns false post-augmentation. We track them here so downstream logic can identify
    // that their .1 result still holds a real Mutable value.
    let augmented_mutref_fns: BTreeSet<FunctionID> = transform_map
        .iter()
        .filter(|(&_fid, info)| matches!(&info.original_return_type, Type::MutableReference(_, _)))
        .map(|(&fid, _)| fid)
        .collect();

    // Pre-compute composable mutref functions (needs immutable borrow of program)
    let composable_fns: BTreeSet<FunctionID> = program
        .functions
        .iter()
        .filter(|(fid, _)| returns_mutable_ref(*fid, program) || augmented_mutref_fns.contains(fid))
        .filter(|(fid, _)| is_composable_mutref_fn(*fid, &program))
        .map(|(fid, _)| fid)
        .collect();

    // Transform bodies
    let func_ids: Vec<FunctionID> = program.functions.iter_ids().collect();
    for func_id in &func_ids {
        let is_native = program.functions.get(func_id).is_native;
        if is_native {
            continue;
        }

        // 2. Destructure augmented returns at call sites
        {
            let mutable_param_names: BTreeSet<TempId> =
                if let Some(mps) = all_mutable_params.get(func_id) {
                    mps.iter().map(|mp| mp.ssa_name.clone()).collect()
                } else {
                    BTreeSet::new()
                };
            let func = program.functions.get_mut(*func_id);
            let body = std::mem::take(&mut func.body);
            func.body = fix_call_sites(body, &transform_map, &mutable_param_names);
        }

        // 3. Wrap tail to return mutable params
        if let Some(info) = transform_map.get(func_id) {
            if !composable_fns.is_empty() {
                let func = program.functions.get_mut(*func_id);
                let body = std::mem::take(&mut func.body);
                func.body = insert_mutable_compose(body, &composable_fns);
            }

            let func = program.functions.get(func_id);
            let aliases = find_param_aliases(&func.body, info);
            let same_shape: BTreeSet<FunctionID> = transform_map
                .iter()
                .filter(|(_, ti)| {
                    ti.original_return_type == info.original_return_type
                        && ti.mutable_params.len() == info.mutable_params.len()
                        && ti
                            .mutable_params
                            .iter()
                            .zip(info.mutable_params.iter())
                            .all(|(a, b)| a.inner_type == b.inner_type)
                })
                .map(|(&fid, _)| fid)
                .collect();
            let is_mutref_fn =
                returns_mutable_ref(*func_id, program) || augmented_mutref_fns.contains(func_id);
            let body = std::mem::take(&mut program.functions.get_mut(*func_id).body);
            let new_body = wrap_tail(
                body,
                info,
                &aliases,
                &BTreeSet::new(),
                program,
                &same_shape,
                is_mutref_fn,
                &None,
                &None,
                &BTreeMap::new(),
                &augmented_mutref_fns,
            );
            program.functions.get_mut(*func_id).body = new_body;
        }
    }

    // 4. Unwrap mutref_fn results in return expressions of non-native functions.
    // When a non-native function calls a mutref_fn (e.g., borrow_mut) and returns
    // the Mutable result in its own return tuple, the caller would receive a Mutable
    // value it can't handle. Insert ReadRef to unwrap it to the plain value.
    //
    // Track which functions have been demoted (had their mutref returns wrapped).
    let mut demoted_mutref_fns: BTreeSet<FunctionID> = BTreeSet::new();
    let all_func_ids2: Vec<FunctionID> = program.functions.iter_ids().collect();
    for func_id in &all_func_ids2 {
        if augmented_mutref_fns.contains(func_id) || returns_mutable_ref(*func_id, program) {
            continue;
        }
        let func = program.functions.get(func_id);
        if func.is_native {
            continue;
        }
        let mutref_results = collect_mutref_fn_results(
            &func.body,
            program,
            &demoted_mutref_fns,
            &augmented_mutref_fns,
        );
        if mutref_results.is_empty() {
            continue;
        }
        let body = std::mem::take(&mut program.functions.get_mut(*func_id).body);
        let (new_body, _did_wrap) = wrap_mutref_returns(body, &mutref_results);
        program.functions.get_mut(*func_id).body = new_body;
    }

    // 4b. Propagate demotion through call chains. When a function's mutref-returning
    // callees have all been demoted, its .1 results are now plain values — demote it too.
    let initial_mutref_fns: BTreeSet<FunctionID> = program
        .functions
        .iter()
        .filter(|(fid, _)| returns_mutable_ref(*fid, program) || augmented_mutref_fns.contains(fid))
        .map(|(fid, _)| fid)
        .collect();
    loop {
        let mut changed = false;
        for func_id in &all_func_ids2 {
            if !initial_mutref_fns.contains(func_id) {
                continue;
            }
            if demoted_mutref_fns.contains(func_id) {
                continue;
            }
            let func = program.functions.get(func_id);
            if func.is_native {
                continue;
            }
            let mutref_results = collect_mutref_fn_results(
                &func.body,
                program,
                &demoted_mutref_fns,
                &augmented_mutref_fns,
            );
            if mutref_results.is_empty() && !has_returned_borrow(&func.body) {
                demoted_mutref_fns.insert(*func_id);
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }

    // 4b'. For each function whose mutref return was demoted in step 4b,
    // demote the corresponding slot in its signature's return type. Without
    // this, callers' VariableRegistry continues to type the destructured
    // first-pattern element as `MutableReference(...)` even though the
    // function's body now returns plain values, so the renderer wraps later
    // uses with `Mutable.val` and Lean rejects with "Application type
    // mismatch". Affects functions that take `&mut X` and return `&mut X`
    // by passing the same parameter through (Test_runner::set_sender and
    // friends) — they have no MutableBorrow in their body for the wrap_tail
    // / compose_return chain to latch onto, so the body-level rebinding is
    // already plain TestRunner; only the signature was lying.
    for func_id in &demoted_mutref_fns {
        let func = program.functions.get_mut(*func_id);
        let new_return_type = match &func.signature.return_type {
            Type::Tuple(elems) if !elems.is_empty() => {
                let mut new_elems = elems.clone();
                if let Type::MutableReference(inner, _) = &new_elems[0] {
                    new_elems[0] = (**inner).clone();
                }
                Type::Tuple(new_elems)
            }
            Type::MutableReference(inner, _) => (**inner).clone(),
            other => other.clone(),
        };
        func.signature.return_type = new_return_type;
    }

    // 4c. Functions demoted in step 4b may still call native mutref functions.
    // Those .1 results are Mutable but the function no longer passes them through — insert ReadRef.
    for func_id in &all_func_ids2 {
        let is_active_mutref =
            initial_mutref_fns.contains(func_id) && !demoted_mutref_fns.contains(func_id);
        if is_active_mutref {
            continue;
        }
        if !initial_mutref_fns.contains(func_id) {
            continue;
        }
        let func = program.functions.get(func_id);
        if func.is_native {
            continue;
        }
        let mutref_results = collect_mutref_fn_results(
            &func.body,
            program,
            &demoted_mutref_fns,
            &augmented_mutref_fns,
        );
        if mutref_results.is_empty() {
            continue;
        }
        let body = std::mem::take(&mut program.functions.get_mut(*func_id).body);
        let (new_body, _did_wrap) = wrap_mutref_returns(body, &mutref_results);
        program.functions.get_mut(*func_id).body = new_body;
    }

    // 5. Sweep: demote remaining MutableReference types in variable registries,
    // EXCEPT for variables that are WriteBack children (they must stay as Mutable
    // for Mutable.set/Mutable.apply to work) or mutref-returning fn result holders
    // (they hold Mutable values from calls to functions like borrow_mut).
    let all_func_ids: Vec<FunctionID> = program.functions.iter_ids().collect();
    for func_id in &all_func_ids {
        let func = program.functions.get(func_id);
        if func.is_native {
            continue;
        }
        let is_active_mutref = (returns_mutable_ref(*func_id, program)
            || augmented_mutref_fns.contains(func_id))
            && !demoted_mutref_fns.contains(func_id);
        let mutref_results = collect_mutref_fn_results(
            &func.body,
            program,
            &demoted_mutref_fns,
            &augmented_mutref_fns,
        );
        let mutable_borrow_bindings = collect_mutable_borrow_bindings(&func.body);
        let compose_vars = collect_mutable_compose_vars(&func.body);
        let stripped_params: BTreeSet<TempId> = all_mutable_params
            .get(func_id)
            .map(|mps| mps.iter().map(|mp| mp.ssa_name.clone()).collect())
            .unwrap_or_default();

        let rebound_borrows = collect_rebound_borrow_bindings(&func.body);

        let mut keep: BTreeSet<TempId> = BTreeSet::new();
        keep.extend(mutref_results.iter().cloned());
        keep.extend(compose_vars.iter().cloned());
        if is_active_mutref {
            keep.extend(mutable_borrow_bindings);
        }
        for name in &stripped_params {
            keep.remove(name);
        }
        for name in &rebound_borrows {
            if !compose_vars.contains(name) {
                keep.remove(name);
            }
        }
        propagate_keep_through_copies(&func.body, &mut keep);

        let mut demoted: BTreeSet<TempId> = collect_mutable_borrow_bindings(&func.body)
            .difference(&keep)
            .cloned()
            .collect();
        demoted.extend(stripped_params.iter().cloned());
        propagate_keep_through_copies(&func.body, &mut demoted);
        for name in &keep {
            demoted.remove(name);
        }
        if !demoted.is_empty() {
            let borrow_info = collect_mutable_borrow_reconstruct_info(&func.body);
            let (to_source, to_last_copy) = build_copy_chains(&func.body);
            let param_names: BTreeSet<TempId> = func
                .signature
                .parameters
                .iter()
                .map(|p| p.ssa_value.clone())
                .collect();
            let body = std::mem::take(&mut program.functions.get_mut(*func_id).body);
            let body = strip_readrefs_for(body, &demoted);
            let body = strip_writerefs_for_demoted(
                body,
                &demoted,
                &keep,
                &borrow_info,
                &to_source,
                &to_last_copy,
                &param_names,
            );
            let body = strip_mutable_borrows_except(body, &keep);
            program.functions.get_mut(*func_id).body =
                strip_writebacks_for_demoted(body, &demoted, &keep, &borrow_info, &param_names);
        }
    }
}

/// Collect variables that appear as `child` in WriteBack nodes.
fn collect_writeback_children(node: &IRNode) -> BTreeSet<TempId> {
    let mut children = BTreeSet::new();
    for n in node.iter() {
        if let IRNode::WriteBack { child, .. } = n {
            children.insert(child.clone());
        }
    }
    children
}

/// Collect variables referenced by MutableCompose nodes (inner and outer).
/// These must be kept as Mutable so the compose is well-typed.
fn collect_mutable_compose_vars(node: &IRNode) -> BTreeSet<TempId> {
    let mut vars = BTreeSet::new();
    for n in node.iter() {
        if let IRNode::MutableCompose { inner, outer } = n {
            vars.insert(inner.clone());
            vars.insert(outer.clone());
        }
    }
    vars
}

/// Check if any WriteBack node's parent is a variable in `mutref_results`.
/// This indicates the function chains mutref call results through write-back
/// (multi-level borrow pattern), which can't be handled by single-level compose.
/// Such functions should be demoted to struct-update write-back semantics.
fn has_writeback_through_mutref_results(node: &IRNode, mutref_results: &BTreeSet<TempId>) -> bool {
    for n in node.iter() {
        if let IRNode::WriteBack { parent, .. } = n {
            if mutref_results.contains(parent) {
                return true;
            }
        }
    }
    false
}

/// Check if any MutableBorrow binding is referenced in the function's tail
/// (return) expression. If a borrow is returned, the function produces Mutable
/// values and the function still returns MutableReference. If all borrows are consumed
/// internally (e.g., via Mutable.set + Mutable.apply), the function returns
/// plain values and can be removed.
///
/// Also resolves through `MutableCompose` chains: when `wrap_tail` introduces
/// `let __compose_N := MutableCompose { inner, outer }` to thread a multi-
/// level borrow back to the caller's parent type, the tail variable is the
/// `__compose_N` name rather than the underlying MutableBorrow. We follow
/// the compose chain back to its root MutableBorrow / MutableCompose
/// references and check whether any of them is itself a MutableBorrow
/// binding — that's what makes the function's return "still a borrow".
fn has_returned_borrow(node: &IRNode) -> bool {
    let borrow_bindings = collect_mutable_borrow_bindings(node);
    if borrow_bindings.is_empty() {
        return false;
    }
    let compose_inner_outer = collect_mutable_compose_bindings(node);
    let tail = get_tail_expr(node);
    let tail_vars = tail.free_vars();
    let mut to_check: Vec<TempId> = tail_vars.into_iter().collect();
    let mut seen: BTreeSet<TempId> = to_check.iter().cloned().collect();
    while let Some(v) = to_check.pop() {
        if borrow_bindings.contains(&v) {
            return true;
        }
        if let Some((inner, outer)) = compose_inner_outer.get(&v) {
            for child in [inner, outer] {
                if seen.insert(child.clone()) {
                    to_check.push(child.clone());
                }
            }
        }
    }
    false
}

/// Collect `let var := MutableCompose { inner, outer }` bindings into a
/// `var -> (inner, outer)` map. Used by `has_returned_borrow` to walk
/// compose chains back to their underlying MutableBorrow operands when
/// deciding whether a function's return type is still a Mutable wrapper.
fn collect_mutable_compose_bindings(node: &IRNode) -> BTreeMap<TempId, (TempId, TempId)> {
    let mut bindings = BTreeMap::new();
    for n in node.iter() {
        if let IRNode::Let { pattern, value, .. } = n {
            if pattern.len() == 1 {
                if let IRNode::MutableCompose { inner, outer } = value.as_ref() {
                    bindings.insert(pattern[0].clone(), (inner.clone(), outer.clone()));
                }
            }
        }
    }
    bindings
}

/// Get the tail (return) expression of a function body by unwinding through
/// Let bindings. For If/Match, returns the node itself since both branches
/// could be return expressions.
fn get_tail_expr(node: &IRNode) -> &IRNode {
    match node {
        IRNode::Let { body, .. } => get_tail_expr(body),
        other => other,
    }
}

/// Collect variables bound to MutableBorrow nodes.
/// These hold Mutable values with reconstruction functions and must not be demoted.
fn collect_mutable_borrow_bindings(node: &IRNode) -> BTreeSet<TempId> {
    let mut bindings = BTreeSet::new();
    for n in node.iter() {
        if let IRNode::Let { pattern, value, .. } = n {
            if pattern.len() == 1 {
                if let IRNode::MutableBorrow { .. } = value.as_ref() {
                    bindings.insert(pattern[0].clone());
                }
            }
        }
    }
    bindings
}

/// Collect MutableBorrow bindings that are subsequently rebound to a plain value.
/// These occur when fix_call_sites inserts `let $tN := __mut_ret` to propagate
/// the write-back state from an augmented function call. The rebinding makes the
/// variable plain, so it should NOT be kept as Mutable.
fn collect_rebound_borrow_bindings(node: &IRNode) -> BTreeSet<TempId> {
    let borrow_bindings = collect_mutable_borrow_bindings(node);
    let mut rebound = BTreeSet::new();
    for n in node.iter() {
        if let IRNode::Let { pattern, value, .. } = n {
            if pattern.len() == 1 && borrow_bindings.contains(&pattern[0]) {
                match value.as_ref() {
                    IRNode::MutableBorrow { .. } => {}
                    IRNode::MutableCompose { .. } => {}
                    _ => {
                        rebound.insert(pattern[0].clone());
                    }
                }
            }
        }
    }
    rebound
}

/// Info about a MutableBorrow binding for inlining reconstruction.
#[derive(Debug, Clone)]
struct MutableBorrowReconstructInfo {
    reconstruct_param: TempId,
    reconstruct_expr: IRNode,
}

/// Collect MutableBorrow bindings with their reconstruction info.
/// Used to inline field updates when WriteRef targets a demoted MutableBorrow variable
/// that has no WriteBack (e.g., `table.size = table.size + 1` at end of function).
fn collect_mutable_borrow_reconstruct_info(
    node: &IRNode,
) -> BTreeMap<TempId, MutableBorrowReconstructInfo> {
    let mut info = BTreeMap::new();
    for n in node.iter() {
        if let IRNode::Let { pattern, value, .. } = n {
            if pattern.len() == 1 {
                if let IRNode::MutableBorrow {
                    reconstruct_param,
                    reconstruct_expr,
                    ..
                } = value.as_ref()
                {
                    info.insert(
                        pattern[0].clone(),
                        MutableBorrowReconstructInfo {
                            reconstruct_param: reconstruct_param.clone(),
                            reconstruct_expr: (**reconstruct_expr).clone(),
                        },
                    );
                }
            }
        }
    }
    info
}

/// Collect variables that hold Mutable values from `mutref_fn` call returns.
///
/// After `fix_call_sites`, a call to a `mutref_fn` (e.g., `borrow_mut`) produces:
///   `Let([result, __mut_ret], Call(mutref_fn, ...), body)`
/// The first pattern element (`result`) holds a `Mutable` value at the Lean level.
/// These variables must NOT be demoted by the sweep, and their ReadRef wrappers
/// must be preserved so the renderer emits `Mutable.val`.
fn collect_mutref_fn_results(
    node: &IRNode,
    program: &Program,
    demoted: &BTreeSet<FunctionID>,
    augmented_mutref: &BTreeSet<FunctionID>,
) -> BTreeSet<TempId> {
    let mut results = BTreeSet::new();
    for n in node.iter() {
        if let IRNode::Let { pattern, value, .. } = n {
            if let IRNode::Call { function, .. } = value.as_ref() {
                let is_mutref =
                    returns_mutable_ref(*function, program) || augmented_mutref.contains(function);
                if is_mutref && !demoted.contains(function) {
                    if pattern.len() >= 2 {
                        results.insert(pattern[0].clone());
                    } else if pattern.len() == 1 && augmented_mutref.contains(function) {
                        // Augmented mutref: Let([__pair], Call(...), ...)
                        // Mark so propagation finds the .1 result variable.
                        results.insert(pattern[0].clone());
                    }
                }
            }
        }
    }
    // Propagate through destructuring: Let([x, ...], Var(y), ...) where y is
    // a mutref result. The first element x holds the Mutable value from the
    // nested tuple (original_result, mut_ret) → (t_t5, t_t6) destructure.
    loop {
        let mut changed = false;
        for n in node.iter() {
            if let IRNode::Let { pattern, value, .. } = n {
                if let IRNode::Var(source) = value.as_ref() {
                    if results.contains(source)
                        && !pattern.is_empty()
                        && !results.contains(&pattern[0])
                    {
                        results.insert(pattern[0].clone());
                        changed = true;
                    }
                }
            }
        }
        if !changed {
            break;
        }
    }
    results
}

/// Propagate a keep set through simple copy chains: `Let([x], Var(y), ...)`
/// where `y` is in keep → add `x` to keep too. Iterates to fixpoint.
fn propagate_keep_through_copies(node: &IRNode, keep: &mut BTreeSet<TempId>) {
    // Build copy map: x → y for Let([x], Var(y), ...)
    let mut copies: Vec<(TempId, TempId)> = Vec::new();
    for n in node.iter() {
        if let IRNode::Let { pattern, value, .. } = n {
            if pattern.len() == 1 {
                if let IRNode::Var(source) = value.as_ref() {
                    copies.push((pattern[0].clone(), source.clone()));
                }
            }
        }
    }
    // Fixpoint propagation
    loop {
        let mut changed = false;
        for (target, source) in &copies {
            if keep.contains(source) && !keep.contains(target) {
                keep.insert(target.clone());
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
}

/// Strip MutableBorrow bindings to plain value assignments,
/// EXCEPT for variables in the `keep` set (WriteBack children).
/// `let x = MutableBorrow { val_expr, ... }` → `let x = val_expr`
fn strip_mutable_borrows_except(node: IRNode, keep: &BTreeSet<TempId>) -> IRNode {
    match node {
        IRNode::Let {
            pattern,
            value,
            body,
        } => {
            let value = match *value {
                IRNode::MutableBorrow { val_expr, .. }
                    if pattern.len() == 1 && !keep.contains(&pattern[0]) =>
                {
                    val_expr
                }
                other => Box::new(strip_mutable_borrows_except(other, keep)),
            };
            IRNode::Let {
                pattern,
                value,
                body: Box::new(strip_mutable_borrows_except(*body, keep)),
            }
        }
        IRNode::If {
            cond,
            then_branch,
            else_branch,
        } => IRNode::If {
            cond,
            then_branch: Box::new(strip_mutable_borrows_except(*then_branch, keep)),
            else_branch: Box::new(strip_mutable_borrows_except(*else_branch, keep)),
        },
        other => other,
    }
}

pub fn relift_phis(node: IRNode, _scope: &BTreeSet<TempId>) -> IRNode {
    node
}

// ============================================================================
// Augmented return type
// ============================================================================

fn augmented_return(original: &Type, mutable_inner_types: &[Type]) -> Type {
    let is_unit = matches!(original, Type::Tuple(v) if v.is_empty());
    if is_unit && mutable_inner_types.len() == 1 {
        mutable_inner_types[0].clone()
    } else if is_unit {
        Type::Tuple(mutable_inner_types.to_vec())
    } else {
        let mut v = vec![original.clone()];
        v.extend_from_slice(mutable_inner_types);
        Type::Tuple(v)
    }
}

// ============================================================================
// Collect borrow bindings
// ============================================================================

fn collect_borrows(node: &IRNode) -> BTreeMap<TempId, BorrowInfo> {
    let mut map = BTreeMap::new();
    for n in node.iter() {
        if let IRNode::Let { pattern, value, .. } = n {
            if pattern.len() == 1 {
                match value.as_ref() {
                    IRNode::MutableBorrow { val_expr, .. } => {
                        map.insert(
                            pattern[0].clone(),
                            BorrowInfo {
                                parent_var: find_base_var(val_expr),
                            },
                        );
                    }
                    IRNode::Call { args, .. } => {
                        for arg in args {
                            let parent = match arg {
                                IRNode::Var(name) if map.contains_key(name) => Some(name.clone()),
                                IRNode::ReadRef(inner) => {
                                    if let IRNode::Var(name) = inner.as_ref() {
                                        if map.contains_key(name) {
                                            Some(name.clone())
                                        } else {
                                            None
                                        }
                                    } else {
                                        None
                                    }
                                }
                                _ => None,
                            };
                            if let Some(p) = parent {
                                map.insert(pattern[0].clone(), BorrowInfo { parent_var: p });
                                break;
                            }
                        }
                    }
                    _ => {}
                }
            }
        }
    }
    map
}

fn find_base_var(expr: &IRNode) -> TempId {
    match expr {
        IRNode::Var(n) => n.clone(),
        IRNode::Field { base, .. } | IRNode::ReadRef(base) | IRNode::UpdateField { base, .. } => {
            find_base_var(base)
        }
        _ => Rc::from("_"),
    }
}

// ============================================================================
// ============================================================================
// Wrap tail positions
// ============================================================================

/// Find the best alias for each mutable param by tracing forward through
/// copy chains at the TOP LEVEL of the function body (not inside branches).
/// Prefers the last non-`$` user variable in the chain, falling back to
/// the param name itself.
fn find_param_aliases(body: &IRNode, info: &TransformInfo) -> BTreeMap<TempId, TempId> {
    let mut aliases: BTreeMap<TempId, TempId> = BTreeMap::new();
    for mp in &info.mutable_params {
        // Build forward chain from top-level Let bindings only
        let mut forward: BTreeMap<TempId, Vec<TempId>> = BTreeMap::new();
        let mut current = body;
        loop {
            match current {
                IRNode::Let {
                    pattern,
                    value,
                    body,
                } => {
                    if pattern.len() == 1 {
                        if let IRNode::Var(src) = value.as_ref() {
                            forward
                                .entry(src.clone())
                                .or_default()
                                .push(pattern[0].clone());
                        }
                    }
                    current = body;
                }
                _ => break,
            }
        }
        // BFS from param to find the last non-$ name in the copy chain
        let mut best = mp.ssa_name.clone();
        let mut queue = vec![mp.ssa_name.clone()];
        while let Some(current) = queue.pop() {
            if !current.starts_with('$') && current != mp.ssa_name {
                best = current.clone();
            }
            if let Some(targets) = forward.get(&current) {
                for t in targets {
                    queue.push(t.clone());
                }
            }
        }
        if best != mp.ssa_name {
            aliases.insert(mp.ssa_name.clone(), best);
        }
    }
    aliases
}

fn wrap_tail(
    node: IRNode,
    info: &TransformInfo,
    aliases: &BTreeMap<TempId, TempId>,
    mutable_bound: &BTreeSet<TempId>,
    program: &Program,
    same_shape_fids: &BTreeSet<FunctionID>,
    is_mutref_fn: bool,
    last_borrow: &Option<TempId>,
    last_mutref_result: &Option<TempId>,
    parent_of: &BTreeMap<TempId, TempId>,
    augmented_mutref_fns: &BTreeSet<FunctionID>,
) -> IRNode {
    match node {
        IRNode::Let {
            ref pattern,
            ref value,
            ..
        } => {
            let mut mb = mutable_bound.clone();
            let mut lb = last_borrow.clone();
            let mut lmr = last_mutref_result.clone();
            let mut po = parent_of.clone();
            // Helper: pick the parent borrow from a Call's args. Returns the
            // first arg variable that's already in `mb` (i.e. it's a borrow
            // chain we can extend). Used to record `parent_of[result] = parent`.
            let parent_from_call_args = |call: &IRNode, mb: &BTreeSet<TempId>| -> Option<TempId> {
                if let IRNode::Call { args, .. } = call {
                    for arg in args {
                        for v in arg.free_vars() {
                            if mb.contains(&v) {
                                return Some(v);
                            }
                        }
                    }
                }
                None
            };
            // Helper: pick the parent borrow from a MutableBorrow's val_expr.
            // Mirrors `parent_from_call_args` for `Mutable.mk` constructions —
            // when a `MutableBorrow { val_expr: (Mutable.val parent).field, .. }`
            // builds a sub-Mutable on a field of an existing Mutable, the
            // composed return chain has to thread through `parent` to lift
            // the result's outer all the way back to the caller's Mutable.
            // Without this, multi-level borrows like
            // `vec_map::get_mut(&mut self, k): &mut V` end up
            // `Mutable<V, List<Entry>>` (stops at the inner level) instead
            // of `Mutable<V, VecMap>` and consumers see a type mismatch.
            let parent_from_borrow_val = |val: &IRNode, mb: &BTreeSet<TempId>| -> Option<TempId> {
                for v in val.free_vars() {
                    if mb.contains(&v) {
                        return Some(v);
                    }
                }
                None
            };
            if pattern.len() == 1 {
                match value.as_ref() {
                    IRNode::MutableBorrow { val_expr, .. } => {
                        mb.insert(pattern[0].clone());
                        lb = Some(pattern[0].clone());
                        if let Some(parent) =
                            parent_from_borrow_val(val_expr.as_ref(), &mutable_bound)
                        {
                            po.insert(pattern[0].clone(), parent);
                        }
                    }
                    IRNode::MutableCompose { .. } => {
                        mb.insert(pattern[0].clone());
                        lb = Some(pattern[0].clone());
                    }
                    IRNode::Call { function, .. }
                        if returns_mutable_ref(*function, program)
                            || augmented_mutref_fns.contains(function) =>
                    {
                        mb.insert(pattern[0].clone());
                        lmr = Some(pattern[0].clone());
                        if let Some(parent) = parent_from_call_args(value.as_ref(), &mutable_bound)
                        {
                            po.insert(pattern[0].clone(), parent);
                        }
                    }
                    _ => {
                        mb.remove(&pattern[0]);
                    }
                }
            } else if pattern.len() >= 2 {
                match value.as_ref() {
                    IRNode::Call { function, .. }
                        if returns_mutable_ref(*function, program)
                            || augmented_mutref_fns.contains(function) =>
                    {
                        mb.insert(pattern[0].clone());
                        lmr = Some(pattern[0].clone());
                        if let Some(parent) = parent_from_call_args(value.as_ref(), &mutable_bound)
                        {
                            po.insert(pattern[0].clone(), parent);
                        }
                    }
                    IRNode::Var(name) if mb.contains(name) => {
                        mb.insert(pattern[0].clone());
                        if lmr.as_ref() == Some(name) {
                            lmr = Some(pattern[0].clone());
                        }
                        if let Some(parent) = po.get(name).cloned() {
                            po.insert(pattern[0].clone(), parent);
                        }
                    }
                    _ => {}
                }
            }
            if let IRNode::Let {
                pattern,
                value,
                body,
            } = node
            {
                IRNode::Let {
                    pattern,
                    value,
                    body: Box::new(wrap_tail(
                        *body,
                        info,
                        aliases,
                        &mb,
                        program,
                        same_shape_fids,
                        is_mutref_fn,
                        &lb,
                        &lmr,
                        &po,
                        augmented_mutref_fns,
                    )),
                }
            } else {
                unreachable!()
            }
        }
        IRNode::If {
            cond,
            then_branch,
            else_branch,
        } => IRNode::If {
            cond,
            then_branch: Box::new(wrap_tail(
                *then_branch,
                info,
                aliases,
                mutable_bound,
                program,
                same_shape_fids,
                is_mutref_fn,
                last_borrow,
                last_mutref_result,
                parent_of,
                augmented_mutref_fns,
            )),
            else_branch: Box::new(wrap_tail(
                *else_branch,
                info,
                aliases,
                mutable_bound,
                program,
                same_shape_fids,
                is_mutref_fn,
                last_borrow,
                last_mutref_result,
                parent_of,
                augmented_mutref_fns,
            )),
        },
        other => {
            // If the tail is a call to a function with the same augmented return shape
            // (self-recursive or mutual-recursive), it already returns the correct type.
            if let IRNode::Call { function, .. } = &other {
                if same_shape_fids.contains(function) {
                    return other;
                }
            }

            // If the tail is an Abort, the function never returns normally.
            // The threaded-back tuple slots can't reference the mutref params
            // meaningfully — and trying to (via `Var(ssa_name)`) hits a real
            // edge case: when the Move source has multiple `_`-named
            // parameters, move-model collapses them to a single interned
            // symbol, so two different params share the same `ssa_name`.
            // The `mutable_params` iteration then emits `Var(shared_name)`
            // which resolves to the WRONG parameter (typically the one with
            // the higher index, since both share an entry in `param_index`).
            // Concrete failure: `update_borrow_fee_recipient(_admin_cap,
            // _: &mut Market, _: address) { abort 0 }` ended up with the
            // mutref's threaded-back slot rendered as `Var("param2")` —
            // which is the Address parameter, not the Market mutref.
            //
            // Emit `Inhabited` (`default`) for the mutref slots when the
            // tail is an Abort. The function never returns at runtime,
            // and Lean accepts `default : Self` for any `Inhabited Self`,
            // so type-checking succeeds without picking ambiguous params.
            // Capture the abort code BEFORE consuming `other` so the
            // collapsed-to-Abort tuple keeps the original `code` (the
            // Move `assert!(cond, CODE)` operand). Test-mode rendering
            // uses it to report `code = CODE` instead of `code = 0`.
            let tail_abort_code = if let IRNode::Abort { code } = &other {
                Some(code.clone())
            } else {
                None
            };
            let tail_is_abort = tail_abort_code.is_some();

            let is_unit = matches!(&info.original_return_type, Type::Tuple(v) if v.is_empty());

            let (chain_lets, return_expr) = if is_mutref_fn {
                compose_return_chain(
                    other,
                    mutable_bound,
                    last_borrow,
                    last_mutref_result,
                    parent_of,
                )
            } else {
                (Vec::new(), other)
            };

            // When the tail is `Abort`, the entire return-tuple is
            // unreachable. Emit a single `Abort` for the whole expression
            // rather than `(Abort, Abort, ...)` — `sorry` already
            // inhabits any tuple type, so one is enough. Preserve the
            // original abort code (captured above) so test-mode reports
            // `code = CODE` instead of `code = 0`.
            let tuple = if tail_is_abort {
                IRNode::Abort {
                    code: tail_abort_code.unwrap(),
                }
            } else {
                let params: Vec<IRNode> = info
                    .mutable_params
                    .iter()
                    .map(|mp| {
                        let name = aliases.get(&mp.ssa_name).unwrap_or(&mp.ssa_name);
                        if mutable_bound.contains(name) {
                            // Variable was rebound to MutableBorrow — extract plain value
                            IRNode::ReadRef(Box::new(IRNode::Var(name.clone())))
                        } else {
                            IRNode::Var(name.clone())
                        }
                    })
                    .collect();
                if is_unit && params.len() == 1 {
                    params.into_iter().next().unwrap()
                } else if is_unit {
                    IRNode::Tuple(params)
                } else {
                    let mut v = vec![return_expr];
                    v.extend(params);
                    IRNode::Tuple(v)
                }
            };
            // Wrap tuple in chain_lets (innermost compose first; tuple is in the
            // body of the outermost Let).
            chain_lets
                .into_iter()
                .rev()
                .fold(tuple, |body, (pattern, value)| IRNode::Let {
                    pattern: vec![pattern],
                    value: Box::new(value),
                    body: Box::new(body),
                })
        }
    }
}

/// Build a chain of MutableCompose Lets when the return value is a multi-level
/// borrow (e.g. `borrow_mut` on a Table inside a struct field — three levels
/// of Mutable wrappers need to nest). Returns `(let_bindings, final_var_expr)`
/// where each let_binding is `(name, MutableCompose value)` and the final
/// expression refers to the outermost composed var.
fn compose_return_chain(
    return_expr: IRNode,
    mutable_bound: &BTreeSet<TempId>,
    last_borrow: &Option<TempId>,
    last_mutref_result: &Option<TempId>,
    parent_of: &BTreeMap<TempId, TempId>,
) -> (Vec<(TempId, IRNode)>, IRNode) {
    let var = match &return_expr {
        IRNode::Var(name) if mutable_bound.contains(name) => name.clone(),
        _ => return (Vec::new(), return_expr),
    };
    // Walk parent_of from `var` to collect the chain of borrow vars.
    let mut chain: Vec<TempId> = vec![var.clone()];
    let mut current = var.clone();
    while let Some(parent) = parent_of.get(&current).cloned() {
        chain.push(parent.clone());
        current = parent;
    }
    if chain.len() < 2 {
        // No multi-level chain. Fall back to the legacy single-level compose.
        let single = compose_return(return_expr, mutable_bound, last_borrow, last_mutref_result);
        return (Vec::new(), single);
    }
    // Build nested compose: first compose chain[0] with chain[1], then result
    // with chain[2], etc. Each intermediate gets a fresh `__compose_N` name.
    let mut lets: Vec<(TempId, IRNode)> = Vec::new();
    let mut current_var = chain[0].clone();
    for (idx, parent) in chain.iter().enumerate().skip(1) {
        let name: TempId = std::rc::Rc::from(format!("__compose_{}", idx).as_str());
        lets.push((
            name.clone(),
            IRNode::MutableCompose {
                inner: current_var.clone(),
                outer: parent.clone(),
            },
        ));
        current_var = name;
    }
    (lets, IRNode::Var(current_var))
}

/// Compose the return expression of a mutref-returning function with the
/// nearest MutableBorrow in scope. This chains write-back reconstruction
/// so the returned Mutable writes all the way back to the top-level struct.
fn compose_return(
    return_expr: IRNode,
    mutable_bound: &BTreeSet<TempId>,
    last_borrow: &Option<TempId>,
    last_mutref_result: &Option<TempId>,
) -> IRNode {
    match &return_expr {
        IRNode::Var(name) if mutable_bound.contains(name) => {
            // Case A: Return is a mutref_fn result — compose with the nearest
            // MutableBorrow (last_borrow).
            if let Some(borrow_var) = last_borrow {
                if name != borrow_var {
                    return IRNode::MutableCompose {
                        inner: name.clone(),
                        outer: borrow_var.clone(),
                    };
                }
            }
            // Case C: Return is a MutableBorrow-bound variable that equals
            // last_borrow — compose with last_mutref_result (the Mutable from
            // an inner mutref call). E.g., Dynamic_field.borrow_mut returns a
            // field borrow of borrow_child_object_mut's Mutable result.
            if let Some(mutref_var) = last_mutref_result {
                if name != mutref_var && last_borrow.as_ref() == Some(name) {
                    return IRNode::MutableCompose {
                        inner: name.clone(),
                        outer: mutref_var.clone(),
                    };
                }
            }
            return_expr
        }
        _ => return_expr,
    }
}

// ============================================================================
// Destructure augmented returns at call sites
// ============================================================================

fn fix_call_sites(
    node: IRNode,
    transform_map: &BTreeMap<FunctionID, TransformInfo>,
    mutable_names: &BTreeSet<TempId>,
) -> IRNode {
    let mut expanded = mutable_names.clone();
    find_copies(&node, &mut expanded);
    let copy_sources = build_copy_sources(&node, mutable_names);
    let counter = std::cell::Cell::new(0usize);
    fix_call_sites_rec(node, transform_map, &expanded, &copy_sources, &counter)
}

/// Extract the variable name from an argument at a mutable param position.
fn extract_arg_var(arg: &IRNode) -> Option<TempId> {
    match arg {
        IRNode::Var(name) => Some(name.clone()),
        IRNode::ReadRef(inner) => {
            if let IRNode::Var(name) = inner.as_ref() {
                Some(name.clone())
            } else {
                None
            }
        }
        IRNode::MutableBorrow { val_expr, .. } => {
            let base = find_base_var(val_expr);
            if &*base != "_" {
                Some(base)
            } else {
                None
            }
        }
        _ => None,
    }
}

/// For each mutable param position in a call, find the argument variable to rebind.
fn get_rebind_targets(
    call_node: &IRNode,
    func_id: FunctionID,
    transform_map: &BTreeMap<FunctionID, TransformInfo>,
    expanded: &BTreeSet<TempId>,
    copy_sources: &BTreeMap<TempId, TempId>,
) -> Vec<TempId> {
    let args = match call_node {
        IRNode::Let { ref value, .. } => {
            if let IRNode::Call { ref args, .. } = value.as_ref() {
                Some(args)
            } else {
                None
            }
        }
        IRNode::Call { ref args, .. } => Some(args),
        _ => None,
    };
    let args = match args {
        Some(a) => a,
        None => return vec![],
    };
    let ti = match transform_map.get(&func_id) {
        Some(ti) => ti,
        None => return vec![],
    };
    ti.mutable_params
        .iter()
        .filter_map(|mp| {
            args.get(mp.param_index).and_then(|arg| {
                let var = extract_arg_var(arg)?;
                Some(trace_to_root(&var, copy_sources))
            })
        })
        .collect()
}

fn fix_call_sites_rec(
    node: IRNode,
    transform_map: &BTreeMap<FunctionID, TransformInfo>,
    expanded: &BTreeSet<TempId>,
    copy_sources: &BTreeMap<TempId, TempId>,
    counter: &std::cell::Cell<usize>,
) -> IRNode {
    match node {
        IRNode::Let {
            pattern,
            value,
            body,
        } => {
            let should_transform = if let IRNode::Call { function, .. } = value.as_ref() {
                get_call_void_info(*function, transform_map).map(|is_void| (*function, is_void))
            } else {
                None
            };

            if let Some((func_id, is_void)) = should_transform {
                let dummy = IRNode::Let {
                    pattern: pattern.clone(),
                    value: value.clone(),
                    body: Box::new(IRNode::Tuple(vec![])),
                };
                let targets =
                    get_rebind_targets(&dummy, func_id, transform_map, expanded, copy_sources);

                if targets.is_empty() {
                    let rec_body =
                        fix_call_sites_rec(*body, transform_map, expanded, copy_sources, counter);
                    return IRNode::Let {
                        pattern,
                        value,
                        body: Box::new(rec_body),
                    };
                }

                let rec_body =
                    fix_call_sites_rec(*body, transform_map, expanded, copy_sources, counter);
                let id = counter.get();
                counter.set(id + 1);
                let suffix = if id == 0 {
                    String::new()
                } else {
                    format!("_{}", id)
                };
                let mut_rets: Vec<TempId> = (0..targets.len())
                    .map(|i| {
                        if targets.len() == 1 {
                            Rc::from(format!("__mut_ret{}", suffix).as_str())
                        } else {
                            Rc::from(format!("__mut_ret{}_{}", suffix, i).as_str())
                        }
                    })
                    .collect();

                // Build rebinding chain: WriteBack { child: __mut_ret, parent: target }
                let mut inner = Box::new(rec_body);
                for (target, mut_ret) in targets.into_iter().zip(mut_rets.iter()).rev() {
                    inner = Box::new(IRNode::Let {
                        pattern: vec![],
                        value: Box::new(IRNode::WriteBack {
                            child: mut_ret.clone(),
                            parent: target,
                            edge: WriteBackEdge::Direct,
                        }),
                        body: inner,
                    });
                }

                if is_void {
                    return IRNode::Let {
                        pattern: mut_rets,
                        value,
                        body: inner,
                    };
                }

                // Non-void: augmented return is (result, mutable_params...)
                if pattern.len() <= 1 {
                    let result: TempId = if !pattern.is_empty() {
                        pattern[0].clone()
                    } else {
                        Rc::from("_")
                    };
                    let mut pat = vec![result];
                    pat.extend(mut_rets);
                    return IRNode::Let {
                        pattern: pat,
                        value,
                        body: inner,
                    };
                }

                let orig_temp: TempId = Rc::from(format!("__orig_ret{}", suffix).as_str());
                let destructure = IRNode::Let {
                    pattern,
                    value: Box::new(IRNode::Var(orig_temp.clone())),
                    body: inner,
                };
                let mut pat = vec![orig_temp];
                pat.extend(mut_rets);
                return IRNode::Let {
                    pattern: pat,
                    value,
                    body: Box::new(destructure),
                };
            }

            IRNode::Let {
                pattern,
                value: Box::new(fix_call_sites_rec(
                    *value,
                    transform_map,
                    expanded,
                    copy_sources,
                    counter,
                )),
                body: Box::new(fix_call_sites_rec(
                    *body,
                    transform_map,
                    expanded,
                    copy_sources,
                    counter,
                )),
            }
        }
        IRNode::If {
            cond,
            then_branch,
            else_branch,
        } => IRNode::If {
            cond,
            then_branch: Box::new(fix_call_sites_rec(
                *then_branch,
                transform_map,
                expanded,
                copy_sources,
                counter,
            )),
            else_branch: Box::new(fix_call_sites_rec(
                *else_branch,
                transform_map,
                expanded,
                copy_sources,
                counter,
            )),
        },
        bare_call @ IRNode::Call { .. } => {
            let function = if let IRNode::Call { function, .. } = &bare_call {
                *function
            } else {
                unreachable!()
            };
            if let Some(is_void) = get_call_void_info(function, transform_map) {
                let targets =
                    get_rebind_targets(&bare_call, function, transform_map, expanded, copy_sources);

                if targets.is_empty() {
                    return bare_call;
                }

                let id = counter.get();
                counter.set(id + 1);
                let suffix = if id == 0 {
                    String::new()
                } else {
                    format!("_{}", id)
                };
                let mut_rets: Vec<TempId> = (0..targets.len())
                    .map(|i| {
                        if targets.len() == 1 {
                            Rc::from(format!("__mut_ret{}", suffix).as_str())
                        } else {
                            Rc::from(format!("__mut_ret{}_{}", suffix, i).as_str())
                        }
                    })
                    .collect();

                let mut inner: Box<IRNode> = if is_void {
                    Box::new(IRNode::Tuple(vec![]))
                } else {
                    let result_temp: TempId = Rc::from(format!("__call_result{}", suffix).as_str());
                    let tail = Box::new(IRNode::Var(result_temp.clone()));
                    // For non-void, we need result_temp in the pattern
                    let mut pat = vec![result_temp];
                    pat.extend(mut_rets.clone());
                    let mut rebind_inner = tail;
                    for (target, mut_ret) in targets.into_iter().zip(mut_rets.iter()).rev() {
                        rebind_inner = Box::new(IRNode::Let {
                            pattern: vec![],
                            value: Box::new(IRNode::WriteBack {
                                child: mut_ret.clone(),
                                parent: target,
                                edge: WriteBackEdge::Direct,
                            }),
                            body: rebind_inner,
                        });
                    }
                    return IRNode::Let {
                        pattern: pat,
                        value: Box::new(bare_call),
                        body: rebind_inner,
                    };
                };

                for (target, mut_ret) in targets.into_iter().zip(mut_rets.iter()).rev() {
                    inner = Box::new(IRNode::Let {
                        pattern: vec![],
                        value: Box::new(IRNode::WriteBack {
                            child: mut_ret.clone(),
                            parent: target,
                            edge: WriteBackEdge::Direct,
                        }),
                        body: inner,
                    });
                }

                return IRNode::Let {
                    pattern: mut_rets,
                    value: Box::new(bare_call),
                    body: inner,
                };
            }
            bare_call
        }
        IRNode::Match { scrutinee, cases } => IRNode::Match {
            scrutinee,
            cases: cases
                .into_iter()
                .map(|(idx, vars, body)| {
                    (
                        idx,
                        vars,
                        fix_call_sites_rec(body, transform_map, expanded, copy_sources, counter),
                    )
                })
                .collect(),
        },
        IRNode::MatchOption {
            scrutinee,
            none_branch,
            binding,
            some_branch,
        } => IRNode::MatchOption {
            scrutinee,
            none_branch: Box::new(fix_call_sites_rec(
                *none_branch,
                transform_map,
                expanded,
                copy_sources,
                counter,
            )),
            binding,
            some_branch: Box::new(fix_call_sites_rec(
                *some_branch,
                transform_map,
                expanded,
                copy_sources,
                counter,
            )),
        },
        other => other,
    }
}

// ============================================================================
// Helpers
// ============================================================================

/// Build a map from copy variables to the mutable param they originate from.
/// Traces `let $t7 := self; let $t12 := $t7` → {$t7 → self, $t12 → self}.
fn build_copy_to_param_map(
    body: &IRNode,
    param_names: &BTreeSet<TempId>,
) -> BTreeMap<TempId, TempId> {
    let mut map = BTreeMap::new();
    loop {
        let mut added = false;
        for n in body.iter() {
            if let IRNode::Let { pattern, value, .. } = n {
                if pattern.len() == 1 && &*pattern[0] != "_" {
                    let src = match value.as_ref() {
                        IRNode::Var(s) => Some(s.clone()),
                        IRNode::ReadRef(inner) => {
                            if let IRNode::Var(s) = inner.as_ref() {
                                Some(s.clone())
                            } else {
                                None
                            }
                        }
                        _ => None,
                    };
                    if let Some(src) = src {
                        if !map.contains_key(&pattern[0]) {
                            if param_names.contains(&src) {
                                map.insert(pattern[0].clone(), src.clone());
                                added = true;
                            } else if let Some(root) = map.get(&src) {
                                map.insert(pattern[0].clone(), root.clone());
                                added = true;
                            }
                        }
                    }
                }
            }
        }
        if !added {
            break;
        }
    }
    map
}

/// Convert `let [] := WriteRef { Var(copy), val }` to `let [param] := val`
/// when the WriteRef targets a copy of a mutable param.
fn strip_param_writerefs(
    node: IRNode,
    param_names: &BTreeSet<TempId>,
    copy_to_param: &BTreeMap<TempId, TempId>,
) -> IRNode {
    match node {
        IRNode::Let {
            pattern,
            value,
            body,
        } => {
            if let IRNode::WriteRef {
                reference,
                value: wval,
            } = *value
            {
                let target = match reference.as_ref() {
                    IRNode::Var(name) => Some(name.clone()),
                    IRNode::ReadRef(inner) => {
                        if let IRNode::Var(name) = inner.as_ref() {
                            Some(name.clone())
                        } else {
                            None
                        }
                    }
                    _ => None,
                };
                if let Some(name) = target {
                    // Direct param
                    if param_names.contains(&name) {
                        return IRNode::Let {
                            pattern: vec![name],
                            value: wval,
                            body: Box::new(strip_param_writerefs(
                                *body,
                                param_names,
                                copy_to_param,
                            )),
                        };
                    }
                    // Copy of param — rebind the original param
                    if let Some(param) = copy_to_param.get(&name) {
                        return IRNode::Let {
                            pattern: vec![param.clone()],
                            value: wval,
                            body: Box::new(strip_param_writerefs(
                                *body,
                                param_names,
                                copy_to_param,
                            )),
                        };
                    }
                }
                // Not a param target — put the WriteRef back and recurse
                return IRNode::Let {
                    pattern,
                    value: Box::new(IRNode::WriteRef {
                        reference,
                        value: wval,
                    }),
                    body: Box::new(strip_param_writerefs(*body, param_names, copy_to_param)),
                };
            }
            IRNode::Let {
                pattern,
                value: Box::new(strip_param_writerefs(*value, param_names, copy_to_param)),
                body: Box::new(strip_param_writerefs(*body, param_names, copy_to_param)),
            }
        }
        IRNode::If {
            cond,
            then_branch,
            else_branch,
        } => IRNode::If {
            cond,
            then_branch: Box::new(strip_param_writerefs(
                *then_branch,
                param_names,
                copy_to_param,
            )),
            else_branch: Box::new(strip_param_writerefs(
                *else_branch,
                param_names,
                copy_to_param,
            )),
        },
        other => other,
    }
}

fn strip_readrefs_for(node: IRNode, param_names: &BTreeSet<TempId>) -> IRNode {
    node.map(&mut |n| match n {
        IRNode::ReadRef(inner) => {
            if let IRNode::Var(name) = inner.as_ref() {
                if param_names.contains(name) {
                    return *inner;
                }
            }
            IRNode::ReadRef(inner)
        }
        other => other,
    })
}

/// Strip WriteRef nodes targeting demoted variables, converting them to plain rebindings.
/// `WriteRef { ref: Var(name), val: expr }` → `Let([name], expr, body)` when name is demoted.
///
/// When the target is a demoted MutableBorrow variable (field borrow with no WriteBack),
/// inlines the reconstruction to propagate the mutation back to the parent struct.
/// E.g., `WriteRef { ref: Var($t47), val: new_size }` where $t47 borrows `table.size`
/// becomes `let table := { table with size := new_size }`.
///
/// Tracks variable scope to skip reconstructions whose parent variable isn't
/// defined in the current branch (orphaned write-refs from previous loop iterations).
fn strip_writerefs_for_demoted(
    node: IRNode,
    demoted: &BTreeSet<TempId>,
    keep: &BTreeSet<TempId>,
    borrow_info: &BTreeMap<TempId, MutableBorrowReconstructInfo>,
    to_source: &BTreeMap<TempId, TempId>,
    to_last_copy: &BTreeMap<TempId, TempId>,
    in_scope: &BTreeSet<TempId>,
) -> IRNode {
    match node {
        IRNode::Let {
            pattern,
            value,
            body,
        } => {
            if let IRNode::WriteRef {
                reference,
                value: wval,
            } = *value
            {
                let target = match reference.as_ref() {
                    IRNode::Var(name) => Some(name.clone()),
                    IRNode::ReadRef(inner) => {
                        if let IRNode::Var(name) = inner.as_ref() {
                            Some(name.clone())
                        } else {
                            None
                        }
                    }
                    _ => None,
                };
                if let Some(name) = target {
                    if demoted.contains(&name) {
                        if let Some(info) = borrow_info.get(&name) {
                            let mut reconstructed = substitute_var(
                                info.reconstruct_expr.clone(),
                                &info.reconstruct_param,
                                &*wval,
                            );
                            // Prefer the structural parent (base of the outer
                            // UpdateField) over a free-vars heuristic. Multi-DF
                            // reconstruct_exprs from `dynamic_field_rewriting`
                            // carry extra free vars (typically the key) that
                            // would otherwise compete with the actual parent.
                            let parent_var = extract_parent_var(&info.reconstruct_expr)
                                .unwrap_or_else(|| {
                                    let parent_vars = info.reconstruct_expr.free_vars();
                                    parent_vars.into_iter()
                                        .find(|v| v.as_ref() != info.reconstruct_param.as_ref())
                                        .expect("MutableBorrow reconstruct_expr must reference a parent variable")
                                });
                            // Resolve parent to its canonical name, but only if
                            // that name is in scope. Fall back through the chain
                            // to find the most specific in-scope name.
                            let canonical = resolve_canonical_in_scope(
                                &parent_var,
                                to_source,
                                to_last_copy,
                                in_scope,
                            );
                            // If neither the parent nor any canonical form is in scope,
                            // this is an orphaned reconstruction — drop it.
                            if !in_scope.contains(&canonical) {
                                return strip_writerefs_for_demoted(
                                    *body,
                                    demoted,
                                    keep,
                                    borrow_info,
                                    to_source,
                                    to_last_copy,
                                    in_scope,
                                );
                            }
                            if canonical != parent_var {
                                reconstructed = substitute_var(
                                    reconstructed,
                                    &parent_var,
                                    &IRNode::Var(canonical.clone()),
                                );
                            }
                            let mut new_scope = in_scope.clone();
                            new_scope.insert(canonical.clone());
                            if keep.contains(&canonical) {
                                return IRNode::Let {
                                    pattern: vec![canonical.clone()],
                                    value: Box::new(IRNode::WriteRef {
                                        reference: Box::new(IRNode::Var(canonical)),
                                        value: Box::new(reconstructed),
                                    }),
                                    body: Box::new(strip_writerefs_for_demoted(
                                        *body,
                                        demoted,
                                        keep,
                                        borrow_info,
                                        to_source,
                                        to_last_copy,
                                        &new_scope,
                                    )),
                                };
                            }
                            let value = Box::new(reconstructed);
                            return IRNode::Let {
                                pattern: vec![canonical],
                                value,
                                body: Box::new(strip_writerefs_for_demoted(
                                    *body,
                                    demoted,
                                    keep,
                                    borrow_info,
                                    to_source,
                                    to_last_copy,
                                    &new_scope,
                                )),
                            };
                        }
                        let mut new_scope = in_scope.clone();
                        new_scope.insert(name.clone());
                        return IRNode::Let {
                            pattern: vec![name],
                            value: wval,
                            body: Box::new(strip_writerefs_for_demoted(
                                *body,
                                demoted,
                                keep,
                                borrow_info,
                                to_source,
                                to_last_copy,
                                &new_scope,
                            )),
                        };
                    }
                }
                let mut new_scope = in_scope.clone();
                for p in &pattern {
                    new_scope.insert(p.clone());
                }
                return IRNode::Let {
                    pattern,
                    value: Box::new(IRNode::WriteRef {
                        reference,
                        value: wval,
                    }),
                    body: Box::new(strip_writerefs_for_demoted(
                        *body,
                        demoted,
                        keep,
                        borrow_info,
                        to_source,
                        to_last_copy,
                        &new_scope,
                    )),
                };
            }
            let mut new_scope = in_scope.clone();
            for p in &pattern {
                new_scope.insert(p.clone());
            }
            IRNode::Let {
                pattern,
                value: Box::new(strip_writerefs_for_demoted(
                    *value,
                    demoted,
                    keep,
                    borrow_info,
                    to_source,
                    to_last_copy,
                    in_scope,
                )),
                body: Box::new(strip_writerefs_for_demoted(
                    *body,
                    demoted,
                    keep,
                    borrow_info,
                    to_source,
                    to_last_copy,
                    &new_scope,
                )),
            }
        }
        IRNode::If {
            cond,
            then_branch,
            else_branch,
        } => IRNode::If {
            cond,
            then_branch: Box::new(strip_writerefs_for_demoted(
                *then_branch,
                demoted,
                keep,
                borrow_info,
                to_source,
                to_last_copy,
                in_scope,
            )),
            else_branch: Box::new(strip_writerefs_for_demoted(
                *else_branch,
                demoted,
                keep,
                borrow_info,
                to_source,
                to_last_copy,
                in_scope,
            )),
        },
        other => other,
    }
}

/// Resolve a parent variable to its canonical name, preferring names that are in scope.
fn resolve_canonical_in_scope(
    parent_var: &TempId,
    to_source: &BTreeMap<TempId, TempId>,
    to_last_copy: &BTreeMap<TempId, TempId>,
    in_scope: &BTreeSet<TempId>,
) -> TempId {
    // First try the standard resolution
    let canonical = if let Some(root) = to_source.get(parent_var) {
        root.clone()
    } else {
        to_last_copy
            .get(parent_var)
            .cloned()
            .unwrap_or_else(|| parent_var.clone())
    };
    // If the canonical name is in scope, use it
    if in_scope.contains(&canonical) {
        return canonical;
    }
    // If parent_var itself is in scope, use it directly
    if in_scope.contains(parent_var) {
        return parent_var.clone();
    }
    // Try the source of canonical
    if let Some(root) = to_source.get(parent_var) {
        if in_scope.contains(root) {
            return root.clone();
        }
    }
    // Last resort: return the canonical (caller will check scope)
    canonical
}

/// Identify the "parent struct" variable that a MutableBorrow's
/// `reconstruct_expr` reconstructs.
///
/// The pre-threading IR builds reconstruct_expr as
/// `UpdateField { base: Var(parent), .. , value: <something with __v> }`,
/// so the parent is structurally the base of the outermost UpdateField.
///
/// Free-vars heuristics ("any var that isn't the reconstruct_param") fail
/// when the rewriter (`dynamic_field_rewriting`) builds a more elaborate
/// reconstruct_expr that references additional variables — typically the
/// dynamic-field key. Concretely, `Phase 1` produces
/// `UpdateField { base: Var(self), df_idx,
///    value: Call(TypedMap.set, [Field(self, df_idx), Var($t5_key), Var(__v)]) }`,
/// whose free vars are `{self, $t5_key, __v}`; picking `$t5_key`
/// instead of `self` rebinds the key variable to a parent-struct
/// reconstruction, breaking subsequent references to the key.
///
/// Returns the parent var name when reconstruct_expr is a recognized
/// UpdateField shape; callers fall back to free-vars filtering for any
/// other shape.
fn extract_parent_var(reconstruct_expr: &IRNode) -> Option<TempId> {
    match reconstruct_expr {
        IRNode::UpdateField { base, .. } => {
            if let IRNode::Var(name) = base.as_ref() {
                Some(name.clone())
            } else {
                None
            }
        }
        _ => None,
    }
}

/// Substitute all occurrences of `Var(param)` with `replacement` in the given IR node.
///
/// Recurses into the container types that the rewriter actually
/// produces inside `MutableBorrow.reconstruct_expr`. Originally this
/// only handled `Var`, `UpdateField`, and `Field` — silently leaving
/// `Var(param)` buried inside `Call` args (e.g. `TypedMap.set(parent.df,
/// key, Var("__v"))` from `dynamic_field_rewriting`). The leaked
/// reference then surfaced as `In remove: Undefined variable: __v`
/// in cetus-stl Skip_list::remove. Adding the `Call` arm fixes that
/// concrete shape.
fn substitute_var(node: IRNode, param: &TempId, replacement: &IRNode) -> IRNode {
    match node {
        IRNode::Var(name) if name == *param => replacement.clone(),
        IRNode::UpdateField {
            base,
            struct_id,
            field_index,
            value,
        } => IRNode::UpdateField {
            base: Box::new(substitute_var(*base, param, replacement)),
            struct_id,
            field_index,
            value: Box::new(substitute_var(*value, param, replacement)),
        },
        IRNode::Field {
            struct_id,
            field_index,
            base,
        } => IRNode::Field {
            struct_id,
            field_index,
            base: Box::new(substitute_var(*base, param, replacement)),
        },
        IRNode::Call {
            function,
            type_args,
            args,
        } => IRNode::Call {
            function,
            type_args,
            args: args
                .into_iter()
                .map(|a| substitute_var(a, param, replacement))
                .collect(),
        },
        other => other,
    }
}

/// Build two one-level copy maps from `let x := Var(y)` patterns:
/// - `to_source`: x → y (direct copy source, NOT chained)
/// - `to_last_copy`: y → last x (last variable copied FROM y)
/// Not chained because variables may be rebound, making transitive resolution unsound.
fn build_copy_chains(node: &IRNode) -> (BTreeMap<TempId, TempId>, BTreeMap<TempId, TempId>) {
    let mut to_source = BTreeMap::new();
    let mut to_last_copy = BTreeMap::new();
    for n in node.iter() {
        if let IRNode::Let { pattern, value, .. } = n {
            if pattern.len() == 1 {
                if let IRNode::Var(src) = value.as_ref() {
                    to_source.insert(pattern[0].clone(), src.clone());
                    to_last_copy.insert(src.clone(), pattern[0].clone());
                }
            }
        }
    }
    (to_source, to_last_copy)
}

/// Insert MutableCompose nodes to compose write-back chains.
///
/// When a function returns a Mutable value (from calling a mutref_fn like borrow_mut)
/// AND the Mutable writes back to an intermediate state (e.g., List V), but the function
/// also has mutable params that need the state to be the top-level struct (e.g., ValidatorSet),
/// we need to compose the write-back chains.
///
/// Pattern detected:
///   Let([borrow_var], MutableBorrow { ... },
///     ...
///     Let([result, __mut_ret], Call(mutref_fn, ...), body))
///
/// Transforms to:
///   Let([borrow_var], MutableBorrow { ... },
///     ...
///     Let([result, __mut_ret], Call(mutref_fn, ...),
///       Let([result], MutableCompose { inner: result, outer: borrow_var }, body)))
/// Check if a function's borrow_mut return has a state type that can be composed
/// with an outer MutableBorrow. Dynamic_field.borrow_mut and Dynamic_object_field.borrow_mut
/// return Mutable with a state type (Dynamic_field.Field) that doesn't match the
/// outer borrow's value type (UID), so composing them is type-incorrect.
fn is_composable_mutref_fn(function: FunctionID, program: &Program) -> bool {
    let func = program.functions.get(&function);
    let module = program.modules.get(&func.module_id);
    if func.is_native {
        return (module.name == "vector" || module.name == "table") && func.name == "borrow_mut";
    }
    // A non-native mutref function is composable if its RETURNED MutableBorrow
    // has a state_type matching the function's first struct parameter type.
    // This ensures compose telescopes correctly: Mutable V ParentStruct ∘ Mutable ParentStruct CallerState.
    // Functions like Table.borrow_mut (state=Table) are composable.
    // Functions like Linked_table.borrow_mut (state=Node ≠ LinkedTable) are not.
    let first_struct_param = func
        .signature
        .parameters
        .iter()
        .find(|p| matches!(&p.param_type, Type::Struct { .. }));
    let first_struct_type = match first_struct_param {
        Some(p) => &p.param_type,
        None => return false,
    };
    let tail = get_tail_expr(&func.body);
    let tail_vars = tail.free_vars();
    for n in func.body.iter() {
        if let IRNode::Let { pattern, value, .. } = n {
            if pattern.len() == 1 && tail_vars.contains(&pattern[0]) {
                if let IRNode::MutableBorrow { state_type, .. } = value.as_ref() {
                    if state_type == first_struct_type {
                        return true;
                    }
                }
            }
        }
    }
    false
}

/// Info about an active MutableBorrow in scope.
#[derive(Debug, Clone)]
struct ActiveBorrow {
    borrow_var: TempId,
    parent_vars: BTreeSet<TempId>,
}

fn insert_mutable_compose(node: IRNode, composable_fns: &BTreeSet<FunctionID>) -> IRNode {
    insert_mutable_compose_rec(node, composable_fns, &None)
}

fn insert_mutable_compose_rec(
    node: IRNode,
    composable_fns: &BTreeSet<FunctionID>,
    current_borrow: &Option<ActiveBorrow>,
) -> IRNode {
    match node {
        IRNode::Let {
            pattern,
            value,
            body,
        } => {
            let new_borrow = if pattern.len() == 1 {
                if let IRNode::MutableBorrow { val_expr, .. } = value.as_ref() {
                    let raw_vars = val_expr.free_vars();
                    Some(ActiveBorrow {
                        borrow_var: pattern[0].clone(),
                        parent_vars: raw_vars,
                    })
                } else if let Some(ref ab) = current_borrow {
                    if pattern[0] == ab.borrow_var {
                        match value.as_ref() {
                            IRNode::WriteRef { .. } => None,
                            _ => current_borrow.clone(),
                        }
                    } else {
                        current_borrow.clone()
                    }
                } else {
                    current_borrow.clone()
                }
            } else {
                current_borrow.clone()
            };

            if pattern.len() >= 2 {
                if let IRNode::Call { function, args, .. } = value.as_ref() {
                    if composable_fns.contains(function) {
                        if let Some(ref ab) = new_borrow {
                            let call_arg_vars: BTreeSet<TempId> = args
                                .iter()
                                .flat_map(|arg: &IRNode| arg.free_vars())
                                .collect();
                            let matches =
                                ab.parent_vars.iter().any(|pv| call_arg_vars.contains(pv));
                            if matches {
                                let result_var = pattern[0].clone();
                                let body = insert_mutable_compose_rec(*body, composable_fns, &None);
                                return IRNode::Let {
                                    pattern,
                                    value,
                                    body: Box::new(IRNode::Let {
                                        pattern: vec![result_var.clone()],
                                        value: Box::new(IRNode::MutableCompose {
                                            inner: result_var,
                                            outer: ab.borrow_var.clone(),
                                        }),
                                        body: Box::new(body),
                                    }),
                                };
                            }
                        }
                    }
                }
            }

            IRNode::Let {
                pattern,
                value,
                body: Box::new(insert_mutable_compose_rec(
                    *body,
                    composable_fns,
                    &new_borrow,
                )),
            }
        }
        IRNode::If {
            cond,
            then_branch,
            else_branch,
        } => IRNode::If {
            cond,
            then_branch: Box::new(insert_mutable_compose_rec(
                *then_branch,
                composable_fns,
                current_borrow,
            )),
            else_branch: Box::new(insert_mutable_compose_rec(
                *else_branch,
                composable_fns,
                current_borrow,
            )),
        },
        other => other,
    }
}

/// Strip WriteBack nodes where the child variable was demoted or both parent
/// is demoted and child is not a kept Mutable.
/// When a child is in `keep`, it's a field-level borrow that stayed as Mutable.
/// Its WriteBack propagates the field update to the (demoted, plain) parent via
/// `let parent := Mutable.apply child` — this must be KEPT.
/// When both parent is demoted and child is not kept, the WriteBack is orphaned —
/// UNLESS it has reconstruction info, in which case it becomes a struct update.
///
/// Also drops WriteBack/reconstruction nodes that reference variables not yet
/// in scope (orphaned write-backs from previous loop iterations in recursive
/// while-function representations).
fn strip_writebacks_for_demoted(
    node: IRNode,
    demoted: &BTreeSet<TempId>,
    keep: &BTreeSet<TempId>,
    borrow_info: &BTreeMap<TempId, MutableBorrowReconstructInfo>,
    in_scope: &BTreeSet<TempId>,
) -> IRNode {
    match node {
        IRNode::Let {
            pattern,
            value,
            body,
        } => {
            if let IRNode::WriteBack { child, parent, .. } = value.as_ref() {
                // Drop WriteBack nodes whose child or parent variable isn't in scope.
                // These are orphaned write-backs from previous loop iterations
                // in recursive while-function representations, or from branches
                // where the parent was defined in a different execution path.
                if !in_scope.contains(child) || !in_scope.contains(parent) {
                    return strip_writebacks_for_demoted(
                        *body,
                        demoted,
                        keep,
                        borrow_info,
                        in_scope,
                    );
                }
                let is_augmented_writeback = child.starts_with("__mut_ret");
                let should_strip = !is_augmented_writeback
                    && (demoted.contains(child)
                        || (demoted.contains(parent) && !keep.contains(child)));
                if should_strip {
                    if let Some(info) = borrow_info.get(child) {
                        // Check that reconstruction's parent var is in scope
                        let parent_vars = info.reconstruct_expr.free_vars();
                        let parent_in_scope = parent_vars.iter().all(|v| {
                            v.as_ref() == info.reconstruct_param.as_ref() || in_scope.contains(v)
                        });
                        if !parent_in_scope {
                            return strip_writebacks_for_demoted(
                                *body,
                                demoted,
                                keep,
                                borrow_info,
                                in_scope,
                            );
                        }
                        let reconstructed = substitute_var(
                            info.reconstruct_expr.clone(),
                            &info.reconstruct_param,
                            &IRNode::Var(child.clone()),
                        );
                        // When the parent is Mutable (in keep), wrap in WriteRef
                        // to preserve the Mutable wrapper.
                        let value = if keep.contains(parent) {
                            Box::new(IRNode::WriteRef {
                                reference: Box::new(IRNode::Var(parent.clone())),
                                value: Box::new(reconstructed),
                            })
                        } else {
                            Box::new(reconstructed)
                        };
                        let mut new_scope = in_scope.clone();
                        new_scope.insert(parent.clone());
                        return IRNode::Let {
                            pattern: vec![parent.clone()],
                            value,
                            body: Box::new(strip_writebacks_for_demoted(
                                *body,
                                demoted,
                                keep,
                                borrow_info,
                                &new_scope,
                            )),
                        };
                    }
                    return strip_writebacks_for_demoted(
                        *body,
                        demoted,
                        keep,
                        borrow_info,
                        in_scope,
                    );
                }
            }
            let mut new_scope = in_scope.clone();
            for name in &pattern {
                new_scope.insert(name.clone());
            }
            IRNode::Let {
                pattern,
                value: Box::new(strip_writebacks_for_demoted(
                    *value,
                    demoted,
                    keep,
                    borrow_info,
                    in_scope,
                )),
                body: Box::new(strip_writebacks_for_demoted(
                    *body,
                    demoted,
                    keep,
                    borrow_info,
                    &new_scope,
                )),
            }
        }
        IRNode::If {
            cond,
            then_branch,
            else_branch,
        } => IRNode::If {
            cond,
            then_branch: Box::new(strip_writebacks_for_demoted(
                *then_branch,
                demoted,
                keep,
                borrow_info,
                in_scope,
            )),
            else_branch: Box::new(strip_writebacks_for_demoted(
                *else_branch,
                demoted,
                keep,
                borrow_info,
                in_scope,
            )),
        },
        other => other,
    }
}

/// Walk to tail positions of the IR and wrap any Var references to `mutref_results`
/// with ReadRef, so that Mutable values from native mutref_fn calls get unwrapped
/// before being returned from non-native wrapper functions.
fn wrap_mutref_returns(node: IRNode, mutref_results: &BTreeSet<TempId>) -> (IRNode, bool) {
    match node {
        IRNode::Let {
            pattern,
            value,
            body,
        } => {
            let (new_body, did_wrap) = wrap_mutref_returns(*body, mutref_results);
            (
                IRNode::Let {
                    pattern,
                    value,
                    body: Box::new(new_body),
                },
                did_wrap,
            )
        }
        IRNode::If {
            cond,
            then_branch,
            else_branch,
        } => {
            let (new_then, then_wrapped) = wrap_mutref_returns(*then_branch, mutref_results);
            let (new_else, else_wrapped) = wrap_mutref_returns(*else_branch, mutref_results);
            (
                IRNode::If {
                    cond,
                    then_branch: Box::new(new_then),
                    else_branch: Box::new(new_else),
                },
                then_wrapped || else_wrapped,
            )
        }
        IRNode::Tuple(elems) => {
            let mut did_wrap = false;
            let wrapped = elems
                .into_iter()
                .map(|e| {
                    if let IRNode::Var(ref name) = e {
                        if mutref_results.contains(name) {
                            did_wrap = true;
                            return IRNode::ReadRef(Box::new(e));
                        }
                    }
                    e
                })
                .collect();
            (IRNode::Tuple(wrapped), did_wrap)
        }
        IRNode::Var(ref name) if mutref_results.contains(name) => {
            (IRNode::ReadRef(Box::new(node)), true)
        }
        other => (other, false),
    }
}

fn extract_var_name(node: &IRNode) -> Option<TempId> {
    match node {
        IRNode::Var(name) => Some(name.clone()),
        IRNode::ReadRef(inner) => {
            if let IRNode::Var(name) = inner.as_ref() {
                Some(name.clone())
            } else {
                None
            }
        }
        IRNode::MutableBorrow { val_expr, .. } => {
            let base = find_base_var(val_expr);
            if &*base != "_" {
                Some(base)
            } else {
                None
            }
        }
        _ => None,
    }
}

fn build_copy_sources(node: &IRNode, seeds: &BTreeSet<TempId>) -> BTreeMap<TempId, TempId> {
    let mut sources: BTreeMap<TempId, TempId> = BTreeMap::new();
    let mut current_seeds = seeds.clone();
    loop {
        let mut added = false;
        for n in node.iter() {
            if let IRNode::Let { pattern, value, .. } = n {
                if pattern.len() == 1 {
                    if let IRNode::Var(src) = value.as_ref() {
                        if current_seeds.contains(src) && !current_seeds.contains(&pattern[0]) {
                            sources.insert(pattern[0].clone(), src.clone());
                            current_seeds.insert(pattern[0].clone());
                            added = true;
                        }
                    }
                }
            }
        }
        if !added {
            break;
        }
    }
    sources
}

/// Trace a variable through copy_sources to find the rebinding target.
/// Traces through `$`-prefixed compiler temps (which will be inlined away),
/// but stops at the first non-`$` user-named variable. This ensures the
/// rebinding targets the variable that subsequent code actually references.
fn trace_to_root(name: &TempId, copy_sources: &BTreeMap<TempId, TempId>) -> TempId {
    let mut current = name.clone();
    while let Some(src) = copy_sources.get(&current) {
        // Stop if we've reached a non-temp user variable — this is the
        // "live" name that code after the call site references.
        if !current.starts_with('$') {
            break;
        }
        current = src.clone();
    }
    current
}

fn find_copies(node: &IRNode, seeds: &mut BTreeSet<TempId>) {
    loop {
        let mut added = false;
        for n in node.iter() {
            if let IRNode::Let { pattern, value, .. } = n {
                if pattern.len() == 1 {
                    if let IRNode::Var(src) = value.as_ref() {
                        if seeds.contains(src) && !seeds.contains(&pattern[0]) {
                            seeds.insert(pattern[0].clone());
                            added = true;
                        }
                    }
                }
            }
        }
        if !added {
            break;
        }
    }
}

/// Build directed copy map: dest → [src1, src2, ...].
/// Multiple sources means the variable is a phi (assigned in different if-branches).
fn build_directed_copies(node: &IRNode) -> BTreeMap<TempId, Vec<TempId>> {
    let mut map: BTreeMap<TempId, Vec<TempId>> = BTreeMap::new();
    for n in node.iter() {
        if let IRNode::Let { pattern, value, .. } = n {
            if pattern.len() == 1 {
                if let IRNode::Var(src) = value.as_ref() {
                    let sources = map.entry(pattern[0].clone()).or_default();
                    if !sources.contains(src) {
                        sources.push(src.clone());
                    }
                }
            }
        }
    }
    map
}

fn get_call_void_info(
    function: FunctionID,
    transform_map: &BTreeMap<FunctionID, TransformInfo>,
) -> Option<bool> {
    if let Some(ti) = transform_map.get(&function) {
        Some(matches!(&ti.original_return_type, Type::Tuple(v) if v.is_empty()))
    } else {
        None
    }
}
