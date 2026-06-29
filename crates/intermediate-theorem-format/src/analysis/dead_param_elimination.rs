// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Dead parameter elimination pass
//!
//! Removes unused parameters from functions and updates all call sites.
//! For mutual recursion groups, a parameter is only removed if it is unused
//! across ALL functions in the group. A "passthrough" parameter — one that is
//! only forwarded to other functions in the same group at the same position —
//! is considered unused.

use crate::data::functions::FunctionID;
use crate::data::types::TempId;
use crate::data::Program;
use crate::IRNode;
use std::collections::{BTreeMap, BTreeSet};

/// Run dead parameter elimination across the entire program.
/// Iterates to fixpoint: eliminating params from one function may make
/// params in callers dead too (since the call args are no longer needed).
pub fn eliminate_dead_params(program: &mut Program) {
    for _ in 0..20 {
        if !eliminate_dead_params_once(program) {
            break;
        }
    }
}

/// Run one round of dead parameter elimination. Returns true if any params were removed.
fn eliminate_dead_params_once(program: &mut Program) -> bool {
    // Build mutual group membership
    let mut group_members: BTreeMap<usize, Vec<FunctionID>> = BTreeMap::new();
    let mut func_to_group: BTreeMap<FunctionID, usize> = BTreeMap::new();

    for (fid, func) in program.functions.iter() {
        if let Some(gid) = func.mutual_group_id {
            group_members.entry(gid).or_default().push(fid);
            func_to_group.insert(fid, gid);
        }
    }

    // Phase 1: For each function, compute which param indices are "truly used" —
    // used in any way OTHER than being forwarded at the same position to a
    // function in the same mutual group.
    let mut truly_used: BTreeMap<FunctionID, BTreeSet<usize>> = BTreeMap::new();

    for (fid, func) in program.functions.iter() {
        if func.is_native || func.signature.parameters.is_empty() {
            continue;
        }

        // Skip spec functions — their signatures are part of the proof API
        if is_spec_function(&func.name) {
            continue;
        }

        // Skip .aborts functions — their parameters must match the base
        // function's parameters since callee abort composition copies args
        // from the main call to the .aborts call. Removing params would
        // cause argument count mismatches with native .lean .aborts defs.
        if func.name.ends_with(".aborts") {
            continue;
        }

        let group_id = func.mutual_group_id;
        let group_member_set: BTreeSet<FunctionID> = group_id
            .and_then(|gid| group_members.get(&gid))
            .map(|members| members.iter().copied().collect())
            .unwrap_or_default();

        // Build param_name -> index mapping
        let param_index: BTreeMap<TempId, usize> = func
            .signature
            .parameters
            .iter()
            .enumerate()
            .map(|(i, p)| (p.ssa_value.clone(), i))
            .collect();

        // Collect all Var references, then subtract the ones that are only
        // used as same-position args to intra-group calls.
        let all_used_vars: BTreeSet<TempId> = func.body.used_vars().cloned().collect();

        // Start with all params that have any Var reference as "used"
        let mut used_indices: BTreeSet<usize> = BTreeSet::new();
        for var in &all_used_vars {
            if let Some(&idx) = param_index.get(var) {
                used_indices.insert(idx);
            }
        }

        // For mutual group functions, check if params are only passthroughs.
        // Collect which param indices appear ONLY as same-position args to
        // intra-group calls (and nowhere else).
        if group_id.is_some() && !group_member_set.is_empty() {
            // Count total Var occurrences per param
            let mut total_var_count: BTreeMap<usize, usize> = BTreeMap::new();
            for node in func.body.iter() {
                if let IRNode::Var(name) = node {
                    if let Some(&idx) = param_index.get(name) {
                        *total_var_count.entry(idx).or_insert(0) += 1;
                    }
                }
            }

            // Count how many times each param appears as a same-position arg
            // to an intra-group call
            let mut passthrough_count: BTreeMap<usize, usize> = BTreeMap::new();
            for node in func.body.iter() {
                if let IRNode::Call {
                    function: callee,
                    args,
                    ..
                } = node
                {
                    if group_member_set.contains(callee) {
                        for (arg_pos, arg) in args.iter().enumerate() {
                            if let IRNode::Var(name) = arg {
                                if let Some(&param_idx) = param_index.get(name) {
                                    if param_idx == arg_pos {
                                        *passthrough_count.entry(param_idx).or_insert(0) += 1;
                                    }
                                }
                            }
                        }
                    }
                }
            }

            // A param is a pure passthrough if every Var occurrence is accounted
            // for by same-position intra-group forwarding
            for &idx in &used_indices.clone() {
                let total = total_var_count.get(&idx).copied().unwrap_or(0);
                let passthrough = passthrough_count.get(&idx).copied().unwrap_or(0);
                if total > 0 && total == passthrough {
                    used_indices.remove(&idx);
                }
            }
        }

        truly_used.insert(fid, used_indices);
    }

    // Phase 2: For mutual groups, take the union — keep any param that ANY
    // member truly uses.
    let mut group_used: BTreeMap<usize, BTreeSet<usize>> = BTreeMap::new();
    for (fid, gid) in &func_to_group {
        if let Some(used) = truly_used.get(fid) {
            group_used.entry(*gid).or_default().extend(used);
        }
    }
    for (fid, gid) in &func_to_group {
        // Only apply group union to functions that were analyzed in Phase 1.
        // Functions skipped by is_spec_function must NOT get entries here,
        // otherwise an empty set would mark all their params as dead.
        if truly_used.contains_key(fid) {
            if let Some(group) = group_used.get(gid) {
                truly_used.insert(*fid, group.clone());
            }
        }
    }

    // Phase 3: Compute which parameter indices to remove for each function.
    let mut removals: BTreeMap<FunctionID, Vec<usize>> = BTreeMap::new();

    for (fid, used) in &truly_used {
        let func = program.functions.get(fid);
        let param_count = func.signature.parameters.len();
        let dead: Vec<usize> = (0..param_count).filter(|i| !used.contains(i)).collect();
        if !dead.is_empty() {
            removals.insert(*fid, dead);
        }
    }

    if removals.is_empty() {
        return false;
    }

    // Phase 4: Rewrite all function bodies — update Call nodes to remove dead args
    let removals_ref = &removals;
    for (_, func) in program.functions.iter_mut() {
        if !func.is_native {
            func.body = remove_dead_args(std::mem::take(&mut func.body), removals_ref);
        }
    }

    // Phase 5: Remove dead parameters from function signatures
    for (fid, dead_indices) in &removals {
        let func = program.functions.get_mut(*fid);
        // Remove in reverse order to preserve indices
        for &i in dead_indices.iter().rev() {
            func.signature.parameters.remove(i);
        }
    }

    true
}

/// Check if a function is a spec function whose signature should be preserved.
/// Spec functions are generated from Move spec blocks and have names like:
///   foo_spec, foo_spec.aborts, foo_spec.requires, foo_spec.ensures, foo_spec.ensures_1
/// We do NOT want to skip implementation functions like:
///   foo.aborts, foo.while_0.aborts, foo.ensures
fn is_spec_function(name: &str) -> bool {
    name.contains("_spec")
}

/// Rewrite Call nodes to remove dead arguments.
fn remove_dead_args(node: IRNode, removals: &BTreeMap<FunctionID, Vec<usize>>) -> IRNode {
    node.map(&mut |n| match n {
        IRNode::Call {
            function,
            type_args,
            args,
        } => {
            if let Some(dead_indices) = removals.get(&function) {
                let dead_set: BTreeSet<usize> = dead_indices.iter().copied().collect();
                let new_args: Vec<IRNode> = args
                    .into_iter()
                    .enumerate()
                    .filter(|(i, _)| !dead_set.contains(i))
                    .map(|(_, arg)| arg)
                    .collect();
                IRNode::Call {
                    function,
                    type_args,
                    args: new_args,
                }
            } else {
                IRNode::Call {
                    function,
                    type_args,
                    args,
                }
            }
        }
        other => other,
    })
}
