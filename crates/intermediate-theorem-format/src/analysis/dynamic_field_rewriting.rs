// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Rewrite dynamic field operations to use TypedMap on the struct's ghost `dynamic_fields` field.
//!
//! This pass runs in two phases:
//!
//! ## Phase 1 (pre-threading): `rewrite_df_borrow_mut_pre_threading`
//!
//! Before mutable threading, rewrites `Dynamic_field.borrow_mut` calls into a `MutableBorrow`
//! node so that mutable threading can track write-backs correctly.
//!
//! Before:
//!   let (node, __mut_ret) := Dynamic_field.borrow_mut K V (MutableBorrow(parent.id, ...), key)
//!   let parent := { parent with id := __mut_ret }  -- no-op reconstruction
//!
//! After:
//!   let node := MutableBorrow {
//!       val_expr: TypedMap.get(parent.dynamic_fields, key),
//!       reconstruct_expr: { parent with dynamic_fields := TypedMap.set(parent.dynamic_fields, key, __v) }
//!   }
//!   -- no-op reconstruction stripped from body
//!
//! ## Phase 2 (post-threading): `rewrite_dynamic_fields`
//!
//! After mutable threading, rewrites all other dynamic field operations
//! (Dynamic_field.add/remove/borrow/exists_with_type) to TypedMap operations.
//! `BorrowMut` is already handled by phase 1 and is skipped here.

use crate::data::functions::{Function, FunctionID, FunctionSignature};
use crate::data::structure::StructID;
use crate::data::types::{TempId, Type};
use crate::data::{Module, Program};
use crate::IRNode;
use std::collections::HashMap;

/// Entry for a ghost dynamic_fields field on a struct.
/// For single-field structs: one entry with key_type from the field's `List (K × V)`.
/// For multi-field structs: one entry per ghost field, each with distinct key_type.
#[derive(Debug, Clone)]
struct DfFieldEntry {
    field_index: usize,
    key_type: Type,
    value_type: Type,
}

/// Build the mapping from struct IDs to their dynamic_fields ghost field entries.
/// Scans all struct fields named "dynamic_fields" or "dynamic_fields_N" and
/// extracts the (K, V) types from the `List (K × V)` field type.
fn build_df_field_map(program: &Program) -> HashMap<StructID, Vec<DfFieldEntry>> {
    let mut map: HashMap<StructID, Vec<DfFieldEntry>> = HashMap::new();
    for (&sid, s) in program.structs.iter() {
        for (idx, field) in s.fields.iter().enumerate() {
            if field.name == "dynamic_fields" || field.name.starts_with("dynamic_fields_") {
                // Extract key type from List (K × V) = Vector(Tuple([K, V]))
                if let Type::Vector(inner) = &field.field_type {
                    if let Type::Tuple(pair) = inner.as_ref() {
                        if pair.len() == 2 {
                            map.entry(sid).or_default().push(DfFieldEntry {
                                field_index: idx,
                                key_type: pair[0].clone(),
                                value_type: pair[1].clone(),
                            });
                        }
                    }
                }
            }
        }
    }
    map
}

/// Look up the dynamic_fields field entry for a struct, optionally matching by key type.
/// For single-field structs, returns the one entry regardless of key type.
/// For multi-field structs, matches by key type.
fn lookup_df_entry<'a>(
    df_map: &'a HashMap<StructID, Vec<DfFieldEntry>>,
    struct_id: StructID,
    call_key_type: Option<&Type>,
    call_value_type: Option<&Type>,
) -> Option<&'a DfFieldEntry> {
    let entries = df_map.get(&struct_id)?;
    if entries.len() == 1 {
        return Some(&entries[0]);
    }
    // Multi-field: match by key type and value type.
    // Both are needed because the same key type can appear with different value types
    // (e.g., String → Address and String → Bag.Bag on the same struct).
    if let Some(key_type) = call_key_type {
        if let Some(value_type) = call_value_type {
            for entry in entries {
                if &entry.key_type == key_type && &entry.value_type == value_type {
                    return Some(entry);
                }
            }
        }
        // Fall back to key-only match if value type not available
        for entry in entries {
            if &entry.key_type == key_type {
                return Some(entry);
            }
        }
    }
    None
}

/// Dynamic field function kinds we recognize and rewrite
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum DynFieldOp {
    Add,            // dynamic_field::add -> TypedMap.set
    Remove,         // dynamic_field::remove -> TypedMap.erase
    RemoveIfExists, // dynamic_field::remove_if_exists -> TypedMap.erase_if_exists
    Borrow,         // dynamic_field::borrow -> TypedMap.get
    BorrowMut,      // dynamic_field::borrow_mut -> handled pre-threading (skipped in post pass)
    Exists,         // dynamic_field::exists_with_type -> TypedMap.has
}

/// IDs for the synthetic TypedMap functions
#[derive(Debug, Clone)]
pub struct TypedMapFunctions {
    pub module_id: usize,
    pub get_id: FunctionID,
    pub set_id: FunctionID,
    pub erase_id: FunctionID,
    pub erase_if_exists_id: FunctionID,
    pub has_id: FunctionID,
    pub get_aborts_id: Option<FunctionID>,
    pub set_aborts_id: Option<FunctionID>,
    pub erase_aborts_id: Option<FunctionID>,
    pub erase_if_exists_aborts_id: Option<FunctionID>,
    pub has_aborts_id: Option<FunctionID>,
}

/// Phase 1 (pre-threading): rewrite `Dynamic_field.borrow_mut` calls into `MutableBorrow` nodes.
///
/// This runs BEFORE `thread_mutables` so that mutable threading can track node write-backs.
/// The `MutableBorrow` node produced here has:
///   val_expr: TypedMap.get(parent.dynamic_fields, key)
///   reconstruct_expr: { parent with dynamic_fields := TypedMap.set(parent.dynamic_fields, key, __v) }
///
/// Mutable threading will then emit the TypedMap.set write-back when the node variable is
/// mutated through a subsequent `WriteRef` or passed as a mutable argument.
pub fn rewrite_df_borrow_mut_pre_threading(program: &mut Program) {
    let dyn_field_fns = find_dynamic_field_functions(program);
    if dyn_field_fns.is_empty() {
        return;
    }

    // Check if there is actually a borrow_mut function
    let borrow_mut_id = match dyn_field_fns
        .iter()
        .find(|(_, op)| *op == DynFieldOp::BorrowMut)
    {
        Some((id, _)) => *id,
        None => return,
    };

    // Create TypedMap module early — the post-threading pass will reuse the same IDs
    let typed_map = create_typed_map_module(program);

    // Build df_field map
    let df_field_map = build_df_field_map(program);

    // Rewrite all function bodies
    let func_ids: Vec<usize> = program.functions.iter().map(|(id, _)| id).collect();
    for func_id in func_ids {
        let func = program.functions.get_mut(func_id);
        if func.is_native {
            continue;
        }
        // Seed borrow_bindings from parameters of DF parent struct type, so
        // `Phase 1` recognizes `Var(parent_param)` as a substitute for
        // `MutableBorrow(parent_param.id, ...)`. The IR translator's
        // BorrowField-then-call substitution passes the parent slot directly
        // to dyn-field calls when the source borrowed `&mut p.id` and then
        // immediately called `dynamic_field::borrow_mut(id, k)`; without this
        // seeding Phase 1 abstains and the call stays as a raw
        // `Dynamic_field.borrow_mut`.
        let mut seed: PreBorrowBindings = HashMap::new();
        for p in &func.signature.parameters {
            if let Some((sid, type_args)) = struct_id_of(&p.param_type) {
                if df_field_map.contains_key(&sid) {
                    let name: TempId = std::rc::Rc::from(p.name.as_str());
                    let state_type = Type::Struct {
                        struct_id: sid,
                        type_args,
                    };
                    seed.insert(name.clone(), (sid, IRNode::Var(name), state_type));
                }
            }
        }
        let body = std::mem::take(&mut func.body);
        func.body =
            rewrite_borrow_mut_pre_with_seed(body, borrow_mut_id, &df_field_map, &typed_map, seed);
    }

    // Store TypedMap so post-threading pass can reuse the same IDs
    program.typed_map_functions = Some(typed_map);
}

/// Binding context for pre-threading borrow_mut rewriting.
/// Maps variable names to (struct_id, parent_expr, state_type) for MutableBorrow(parent.id, ..) bindings.
type PreBorrowBindings = HashMap<TempId, (StructID, IRNode, Type)>;

/// Recursively rewrite `borrow_mut` calls into `MutableBorrow` nodes (pre-threading).
fn rewrite_borrow_mut_pre(
    node: IRNode,
    borrow_mut_id: usize,
    df_indices: &HashMap<StructID, Vec<DfFieldEntry>>,
    typed_map: &TypedMapFunctions,
) -> IRNode {
    rewrite_borrow_mut_pre_ctx(
        node,
        borrow_mut_id,
        df_indices,
        typed_map,
        &mut HashMap::new(),
    )
}

/// Same as `rewrite_borrow_mut_pre` but starts with a pre-populated
/// `PreBorrowBindings`. Used to seed parameter-shaped parent structs so the
/// IR translator's BorrowField-then-call substitution (which passes the
/// parent slot directly to dyn-field calls) is recognized as a valid
/// borrow_mut argument.
fn rewrite_borrow_mut_pre_with_seed(
    node: IRNode,
    borrow_mut_id: usize,
    df_indices: &HashMap<StructID, Vec<DfFieldEntry>>,
    typed_map: &TypedMapFunctions,
    mut seed: PreBorrowBindings,
) -> IRNode {
    rewrite_borrow_mut_pre_ctx(node, borrow_mut_id, df_indices, typed_map, &mut seed)
}

fn rewrite_borrow_mut_pre_ctx(
    node: IRNode,
    borrow_mut_id: usize,
    df_indices: &HashMap<StructID, Vec<DfFieldEntry>>,
    typed_map: &TypedMapFunctions,
    borrow_bindings: &mut PreBorrowBindings,
) -> IRNode {
    match node {
        IRNode::Let {
            pattern,
            value,
            body,
        } => {
            // Track MutableBorrow(parent.id, ...) bindings so we can resolve Var references later
            if pattern.len() == 1 {
                if let IRNode::MutableBorrow {
                    val_expr,
                    state_type,
                    ..
                } = value.as_ref()
                {
                    if let IRNode::Field {
                        struct_id,
                        field_index: 0,
                        base,
                    } = val_expr.as_ref()
                    {
                        if df_indices.contains_key(struct_id) {
                            // Only track borrow bindings if this struct has ghost fields
                            borrow_bindings.insert(
                                pattern[0].clone(),
                                (*struct_id, *base.clone(), state_type.clone()),
                            );
                        }
                    }
                }
            }

            // Check if value is a Dynamic_field.borrow_mut call
            if let IRNode::Call {
                function,
                args,
                type_args,
            } = &*value
            {
                if *function == borrow_mut_id && !args.is_empty() {
                    if let Some(result) = try_rewrite_borrow_mut_let(
                        &pattern,
                        args,
                        type_args,
                        *body.clone(),
                        borrow_mut_id,
                        df_indices,
                        typed_map,
                        borrow_bindings,
                    ) {
                        return result;
                    }
                }
            }

            // Recurse into children
            IRNode::Let {
                pattern,
                value: Box::new(rewrite_borrow_mut_pre_ctx(
                    *value,
                    borrow_mut_id,
                    df_indices,
                    typed_map,
                    borrow_bindings,
                )),
                body: Box::new(rewrite_borrow_mut_pre_ctx(
                    *body,
                    borrow_mut_id,
                    df_indices,
                    typed_map,
                    borrow_bindings,
                )),
            }
        }
        IRNode::If {
            cond,
            then_branch,
            else_branch,
        } => IRNode::If {
            cond: Box::new(rewrite_borrow_mut_pre_ctx(
                *cond,
                borrow_mut_id,
                df_indices,
                typed_map,
                borrow_bindings,
            )),
            then_branch: Box::new(rewrite_borrow_mut_pre_ctx(
                *then_branch,
                borrow_mut_id,
                df_indices,
                typed_map,
                borrow_bindings,
            )),
            else_branch: Box::new(rewrite_borrow_mut_pre_ctx(
                *else_branch,
                borrow_mut_id,
                df_indices,
                typed_map,
                borrow_bindings,
            )),
        },
        IRNode::Match { scrutinee, cases } => IRNode::Match {
            scrutinee: Box::new(rewrite_borrow_mut_pre_ctx(
                *scrutinee,
                borrow_mut_id,
                df_indices,
                typed_map,
                borrow_bindings,
            )),
            cases: cases
                .into_iter()
                .map(|(tag, binds, body)| {
                    (
                        tag,
                        binds,
                        rewrite_borrow_mut_pre_ctx(
                            body,
                            borrow_mut_id,
                            df_indices,
                            typed_map,
                            borrow_bindings,
                        ),
                    )
                })
                .collect(),
        },
        other => other,
    }
}

/// Attempt to rewrite a `Let { pattern, value: Call(borrow_mut, [arg0, key]), body }`
/// where arg0 is a MutableBorrow(parent.id, ..) or a Var bound to one.
fn try_rewrite_borrow_mut_let(
    pattern: &[TempId],
    args: &[IRNode],
    type_args: &[Type],
    body: IRNode,
    borrow_mut_id: usize,
    df_indices: &HashMap<StructID, Vec<DfFieldEntry>>,
    typed_map: &TypedMapFunctions,
    borrow_bindings: &PreBorrowBindings,
) -> Option<IRNode> {
    // First arg must resolve to a MutableBorrow wrapping parent.id (field_index 0)
    let (struct_id, parent_expr, state_type) =
        extract_mutable_borrow_uid(&args[0], borrow_bindings)?;

    // Match the call's [K, V] type_args against the parent struct's ghost
    // dynamic_fields entries. Multi-DF structs (e.g. Vault with both
    // `dynamic_fields_0 : List(K, Address)` and
    // `dynamic_fields_1 : List(K, Bag)`) need this disambiguation;
    // single-DF structs ignore it and return their only entry.
    let call_key_type = type_args.first();
    let call_value_type = type_args.get(1);
    let entry = lookup_df_entry(df_indices, struct_id, call_key_type, call_value_type)?;
    let df_idx = entry.field_index;
    // Prefer the call's own type_args over the entry's recorded K / V.
    // The entry's types may be a structural placeholder when the
    // ghost field was synthesised by
    // `native_ghost_fields::augment_structs_with_native_ghost_fields`
    // (which runs when upstream's accessibility-gated
    // `DynamicFieldAnalysisProcessor` failed to record the actual K / V).
    let tm_type_args = vec![
        call_key_type
            .cloned()
            .unwrap_or_else(|| entry.key_type.clone()),
        call_value_type
            .cloned()
            .unwrap_or_else(|| entry.value_type.clone()),
    ];

    let key = args.get(1)?.clone();

    // Build dynamic_fields access
    let df_access = IRNode::Field {
        struct_id,
        field_index: df_idx,
        base: Box::new(parent_expr.clone()),
    };

    // val_expr: TypedMap.get(parent.dynamic_fields, key)
    let val_expr = IRNode::Call {
        function: typed_map.get_id,
        type_args: tm_type_args.clone(),
        args: vec![df_access.clone(), key.clone()],
    };

    // reconstruct_expr: { parent with dynamic_fields := TypedMap.set(parent.dynamic_fields, key, __v) }
    let reconstruct_param: TempId = std::rc::Rc::from("__v");
    let set_call = IRNode::Call {
        function: typed_map.set_id,
        type_args: tm_type_args,
        args: vec![df_access, key, IRNode::Var(reconstruct_param.clone())],
    };
    let reconstruct_expr = IRNode::UpdateField {
        base: Box::new(parent_expr),
        struct_id,
        field_index: df_idx,
        value: Box::new(set_call),
    };

    // The node var is pattern[0]; pattern[1] is the __mut_ret for the old UID reconstruction
    let node_var = pattern[0].clone();
    let mut_ret_var = pattern.get(1).cloned();

    // Strip the no-op UID reconstruction from body: `let parent := { parent with id := __mut_ret }`
    let stripped_body = if let Some(ref mr) = mut_ret_var {
        strip_uid_reconstruction(body, mr, struct_id)
    } else {
        body
    };

    let new_mutable_borrow = IRNode::MutableBorrow {
        val_expr: Box::new(val_expr),
        reconstruct_param,
        reconstruct_expr: Box::new(reconstruct_expr),
        state_type,
    };

    let result = IRNode::Let {
        pattern: vec![node_var],
        value: Box::new(new_mutable_borrow),
        body: Box::new(rewrite_borrow_mut_pre_ctx(
            stripped_body,
            borrow_mut_id,
            df_indices,
            typed_map,
            &mut borrow_bindings.clone(),
        )),
    };

    Some(result)
}

/// Extract (struct_id, parent_expr, state_type) from a MutableBorrow(parent.id, ..) node or
/// a Var that was previously bound to such a MutableBorrow.
fn extract_mutable_borrow_uid(
    arg: &IRNode,
    borrow_bindings: &PreBorrowBindings,
) -> Option<(StructID, IRNode, Type)> {
    match arg {
        IRNode::MutableBorrow {
            val_expr,
            state_type,
            ..
        } => {
            if let IRNode::Field {
                struct_id,
                field_index: 0,
                base,
            } = val_expr.as_ref()
            {
                return Some((*struct_id, *base.clone(), state_type.clone()));
            }
            None
        }
        IRNode::Var(name) => borrow_bindings.get(name).cloned(),
        _ => None,
    }
}

/// Strip `let parent := { parent with id := mut_ret_var }` (field_index 0 UID reconstruction).
/// This is the no-op write-back that mutable threading inserted for the old UID borrow.
fn strip_uid_reconstruction(
    node: IRNode,
    mut_ret_var: &TempId,
    target_struct_id: StructID,
) -> IRNode {
    match node {
        IRNode::Let {
            pattern,
            value,
            body,
        } => {
            // Check if this is `let _ := UpdateField { struct_id, field_index: 0, value: Var(mut_ret_var) }`
            let is_uid_recon = matches!(
                value.as_ref(),
                IRNode::UpdateField { struct_id, field_index: 0, value: v, .. }
                    if *struct_id == target_struct_id
                        && matches!(v.as_ref(), IRNode::Var(name) if name == mut_ret_var)
            );
            if is_uid_recon {
                strip_uid_reconstruction(*body, mut_ret_var, target_struct_id)
            } else {
                IRNode::Let {
                    pattern,
                    value,
                    body: Box::new(strip_uid_reconstruction(
                        *body,
                        mut_ret_var,
                        target_struct_id,
                    )),
                }
            }
        }
        IRNode::If {
            cond,
            then_branch,
            else_branch,
        } => IRNode::If {
            cond,
            then_branch: Box::new(strip_uid_reconstruction(
                *then_branch,
                mut_ret_var,
                target_struct_id,
            )),
            else_branch: Box::new(strip_uid_reconstruction(
                *else_branch,
                mut_ret_var,
                target_struct_id,
            )),
        },
        other => other,
    }
}

pub fn rewrite_dynamic_fields(program: &mut Program) {
    // Step 1: Find the dynamic_field module and collect function IDs
    let dyn_field_fns = find_dynamic_field_functions(program);
    if dyn_field_fns.is_empty() {
        return; // No dynamic field functions found — nothing to rewrite
    }

    // Step 2: Get or create the synthetic TypedMap module and functions.
    // If pre-threading already created it, reuse the existing IDs.
    let typed_map = if let Some(existing) = program.typed_map_functions.take() {
        existing
    } else {
        create_typed_map_module(program)
    };

    // Step 3: Build a mapping from dynamic_field function IDs to their operation kind
    let mut dyn_field_ops: HashMap<FunctionID, DynFieldOp> = HashMap::new();
    for (func_id, op) in &dyn_field_fns {
        dyn_field_ops.insert(*func_id, *op);
    }

    // Step 4: Build a mapping from struct IDs to their dynamic_fields field entries
    let df_field_indices = build_df_field_map(program);

    // Step 5: Rewrite all function bodies
    let func_ids: Vec<usize> = program.functions.iter().map(|(id, _)| id).collect();
    for func_id in func_ids {
        let func = program.functions.get_mut(func_id);
        if func.is_native {
            continue;
        }
        let body = std::mem::take(&mut func.body);
        let params = func.signature.parameters.clone();
        func.body = rewrite_body(body, &dyn_field_ops, &df_field_indices, &typed_map, &params);
    }

    // Step 6: post-rewrite cleanup. After Phase 1 + mutable_threading,
    // bodies that go through `try_rewrite_borrow_mut_let` for a
    // borrow_mut whose IR pattern has a single element (`pattern.len()
    // == 1`, no explicit mut_ret_var) leave a stale UID writeback in
    // place: `let X := UpdateField(struct, df_idx, …)` (the rewritten
    // Phase 1 reconstruct, where X holds the new parent struct value)
    // followed by `let Y := UpdateField(struct, 0, Var(X))` (the
    // pre-Phase-1 mutref's UID writeback, now type-incorrect because
    // `X` is no longer a UID). `strip_uid_reconstruction` doesn't
    // catch this — the original strip logic keys off pattern[1] which
    // is missing. Walk every body once more, look for the exact
    // adjacent-Let shape, and replace the second's value with `Var(X)`
    // so the parent struct is propagated whole instead of via a
    // type-incorrect `id` field update.
    let func_ids: Vec<usize> = program.functions.iter().map(|(id, _)| id).collect();
    for func_id in func_ids {
        let func = program.functions.get_mut(func_id);
        if func.is_native {
            continue;
        }
        let body = std::mem::take(&mut func.body);
        func.body = strip_stale_uid_writeback_post_threading(body, &df_field_indices);
    }

    // Store the TypedMap function IDs on the program for the renderer
    program.typed_map_functions = Some(typed_map);
}

/// Walk a function body and rewrite the post-Phase-1 + mutable_threading
/// stale-UID-writeback pattern:
///   let X := UpdateField(struct, df_idx, ...)
///   let Y := UpdateField(struct, 0, Var(X))     <-- bug
/// into:
///   let X := UpdateField(struct, df_idx, ...)
///   let Y := Var(X)                              <-- propagate whole struct
///
/// `df_field_indices` tells us which `(struct_id, field_idx)` pairs
/// represent ghost dynamic_fields slots — we only touch let chains
/// where the first UpdateField targets a ghost field on a struct that
/// has at least one ghost field. Plain UID writebacks on structs
/// without ghost fields aren't affected.
fn strip_stale_uid_writeback_post_threading(
    node: IRNode,
    df_field_indices: &HashMap<StructID, Vec<DfFieldEntry>>,
) -> IRNode {
    match node {
        IRNode::Let {
            pattern,
            value,
            body,
        } => {
            // First, recursively process the value subtree.
            let value = Box::new(strip_stale_uid_writeback_post_threading(
                *value,
                df_field_indices,
            ));
            // Look for the buggy adjacent shape:
            //   self == let X := UpdateField(struct, df_idx, …)
            //   *body == let Y := UpdateField(struct, 0, Var(X)); rest
            let bug_match = if let IRNode::UpdateField {
                struct_id: outer_sid,
                field_index: outer_field,
                ..
            } = value.as_ref()
            {
                if pattern.len() == 1
                    && df_field_indices
                        .get(outer_sid)
                        .map(|entries| entries.iter().any(|e| e.field_index == *outer_field))
                        .unwrap_or(false)
                {
                    let outer_var = pattern[0].clone();
                    if let IRNode::Let {
                        pattern: inner_pattern,
                        value: inner_value,
                        body: inner_body,
                    } = body.as_ref()
                    {
                        if let IRNode::UpdateField {
                            struct_id: inner_sid,
                            field_index: 0,
                            value: inner_v,
                            ..
                        } = inner_value.as_ref()
                        {
                            let var_match = matches!(
                                inner_v.as_ref(),
                                IRNode::Var(name) if *name == outer_var
                            );
                            if inner_sid == outer_sid && var_match {
                                Some((inner_pattern.clone(), outer_var, inner_body.clone()))
                            } else {
                                None
                            }
                        } else {
                            None
                        }
                    } else {
                        None
                    }
                } else {
                    None
                }
            } else {
                None
            };
            if let Some((inner_pattern, outer_var, inner_body)) = bug_match {
                let new_inner = IRNode::Let {
                    pattern: inner_pattern,
                    value: Box::new(IRNode::Var(outer_var)),
                    body: Box::new(strip_stale_uid_writeback_post_threading(
                        *inner_body,
                        df_field_indices,
                    )),
                };
                return IRNode::Let {
                    pattern,
                    value,
                    body: Box::new(new_inner),
                };
            }
            IRNode::Let {
                pattern,
                value,
                body: Box::new(strip_stale_uid_writeback_post_threading(
                    *body,
                    df_field_indices,
                )),
            }
        }
        IRNode::If {
            cond,
            then_branch,
            else_branch,
        } => IRNode::If {
            cond: Box::new(strip_stale_uid_writeback_post_threading(
                *cond,
                df_field_indices,
            )),
            then_branch: Box::new(strip_stale_uid_writeback_post_threading(
                *then_branch,
                df_field_indices,
            )),
            else_branch: Box::new(strip_stale_uid_writeback_post_threading(
                *else_branch,
                df_field_indices,
            )),
        },
        IRNode::Match { scrutinee, cases } => IRNode::Match {
            scrutinee: Box::new(strip_stale_uid_writeback_post_threading(
                *scrutinee,
                df_field_indices,
            )),
            cases: cases
                .into_iter()
                .map(|(tag, binds, body)| {
                    (
                        tag,
                        binds,
                        strip_stale_uid_writeback_post_threading(body, df_field_indices),
                    )
                })
                .collect(),
        },
        other => other,
    }
}

/// Find all dynamic_field functions by scanning modules and functions
fn find_dynamic_field_functions(program: &Program) -> Vec<(FunctionID, DynFieldOp)> {
    let mut result = Vec::new();

    // Find the dynamic_field module
    let dyn_field_module_id = program
        .modules
        .iter()
        .find(|(_, m)| m.name == "dynamic_field")
        .map(|(&id, _)| id);

    let Some(module_id) = dyn_field_module_id else {
        return result;
    };

    // Find function IDs for the operations we care about
    for (func_id, func) in program.functions.iter() {
        if func.module_id != module_id {
            continue;
        }
        let op = match func.name.as_str() {
            "add" => DynFieldOp::Add,
            "remove" => DynFieldOp::Remove,
            "remove_if_exists" => DynFieldOp::RemoveIfExists,
            "borrow" => DynFieldOp::Borrow,
            "borrow_mut" => DynFieldOp::BorrowMut,
            // Both `exists_with_type<K, V>(uid, k)` and the type-erased
            // `exists_<K>(uid, k)` map to `TypedMap.has`. The latter only
            // carries a key type-arg; lookup_df_entry's key-only fallback
            // resolves it against single-DF parents (and against multi-DF
            // parents whose only ghost field with this key happens to be
            // unique, which is the common case).
            "exists_with_type" | "exists_" => DynFieldOp::Exists,
            _ => continue,
        };
        result.push((func_id, op));
    }

    result
}

/// Create a synthetic TypedMap module with get/set/erase/has functions
fn create_typed_map_module(program: &mut Program) -> TypedMapFunctions {
    // Create module with a high ID that won't collide
    let module_id = program.modules.items.keys().copied().max().unwrap_or(0) + 1000;
    program.modules.items.insert(
        module_id,
        Module {
            name: "TypedMap".to_string(),
            package_name: "Prelude".to_string(),
            required_imports: vec![],
            is_native: true,
        },
    );

    let make_func = |name: &str, return_type: Type| -> Function {
        Function {
            module_id,
            name: name.to_string(),
            signature: FunctionSignature {
                type_params: vec!["K".to_string(), "V".to_string()],
                parameters: vec![],
                proof_params: Vec::new(),
                return_type,
            },
            body: IRNode::default(),

            theorem: None,
            is_native: true,
            mutual_group_id: None,
            test_expectation: None,
        }
    };

    // Type parameter slots: K = TypeParameter(0), V = TypeParameter(1)
    // List(K × V) = Vector(Tuple([K, V]))
    let k = Type::TypeParameter(0);
    let v = Type::TypeParameter(1);
    let kv_list = Type::Vector(Box::new(Type::Tuple(vec![k.clone(), v.clone()])));

    // TypedMap.get(List(K×V), K) -> V
    let get_id = program.functions.add(make_func("get", v.clone()));
    // TypedMap.set(List(K×V), K, V) -> List(K×V)
    let set_id = program.functions.add(make_func("set", kv_list.clone()));
    // TypedMap.erase(List(K×V), K) -> (V, List(K×V))
    let erase_id = program.functions.add(make_func(
        "erase",
        Type::Tuple(vec![v.clone(), kv_list.clone()]),
    ));
    // TypedMap.erase_if_exists(List(K×V), K) -> (List V, List(K×V))
    // Mirrors Move's `dynamic_field::remove_if_exists<K, V>(uid, k) -> Option<V>`.
    // The first tuple element is the inner-vec representation of the
    // resulting Option — empty for `None`, singleton for `Some` — matching
    // `MoveOption.MoveOption V`'s `{ vec : List V }` layout. The renderer
    // wraps it with `MoveOption.mk` at sites that need `MoveOption V`
    // directly. Returning `List V` here keeps `Prelude` from importing
    // `MoveStdlib.MoveOption` and avoids the cycle.
    let erase_if_exists_id = program.functions.add(make_func(
        "erase_if_exists",
        Type::Tuple(vec![Type::Vector(Box::new(v.clone())), kv_list.clone()]),
    ));
    // TypedMap.has(List(K×V), K) -> Bool
    let has_id = program.functions.add(make_func("has", Type::Bool));

    let make_aborts_func = |name: &str| -> Function {
        Function {
            module_id,
            name: name.to_string(),
            signature: FunctionSignature {
                type_params: vec!["K".to_string(), "V".to_string()],
                parameters: vec![],
                proof_params: Vec::new(),
                return_type: Type::Bool,
            },
            body: IRNode::default(),

            theorem: None,
            is_native: true,
            mutual_group_id: None,
            test_expectation: None,
        }
    };

    let get_aborts_id = Some(program.functions.add(make_aborts_func("get.aborts")));
    let set_aborts_id = Some(program.functions.add(make_aborts_func("set.aborts")));
    let erase_aborts_id = Some(program.functions.add(make_aborts_func("erase.aborts")));
    let erase_if_exists_aborts_id = Some(
        program
            .functions
            .add(make_aborts_func("erase_if_exists.aborts")),
    );
    let has_aborts_id = Some(program.functions.add(make_aborts_func("has.aborts")));

    TypedMapFunctions {
        module_id,
        get_id,
        set_id,
        erase_id,
        erase_if_exists_id,
        has_id,
        get_aborts_id,
        set_aborts_id,
        erase_aborts_id,
        erase_if_exists_aborts_id,
        has_aborts_id,
    }
}

/// Context for tracking variable bindings during rewriting.
/// Maps variable names to their known UID field access info (struct_id, parent_var).
type UidBindings = HashMap<TempId, (StructID, IRNode)>;

/// Rewrite the body of a function, replacing dynamic field operations with TypedMap operations.
/// `params` carries the function's parameter list so `extract_parent_info_ctx` can recognize
/// `Var(parent)` arguments where `parent` is itself a DF parent struct (the
/// "BorrowField-then-call" pattern that ir_translator collapses by passing the parent slot
/// directly to the dyn-field call instead of a UID temp).
fn rewrite_body(
    node: IRNode,
    dyn_ops: &HashMap<FunctionID, DynFieldOp>,
    df_indices: &HashMap<StructID, Vec<DfFieldEntry>>,
    typed_map: &TypedMapFunctions,
    params: &[crate::data::functions::Parameter],
) -> IRNode {
    let mut bindings: UidBindings = HashMap::new();
    // Seed bindings from the function's parameters: any param whose type is a
    // DF parent struct can serve as the `parent` when passed directly to a
    // dyn-field call. The "parent expression" is just `Var(name)` itself, so
    // Phase 2's rewrite produces `{ parent with dynamic_fields_N := ... }` and
    // the call's `parent.id` arg gets swapped for `parent.dynamic_fields_N`.
    for p in params {
        if let Some((sid, _type_args)) = struct_id_of(&p.param_type) {
            if df_indices.contains_key(&sid) {
                bindings.insert(
                    std::rc::Rc::from(p.name.as_str()),
                    (sid, IRNode::Var(std::rc::Rc::from(p.name.as_str()))),
                );
            }
        }
    }
    rewrite_body_ctx(node, dyn_ops, df_indices, typed_map, &mut bindings)
}

/// Extract `(struct_id, type_args)` from a `Type::Struct`, peeling through
/// `Reference`/`MutableReference` wrappers — function parameters of type
/// `&Vault<...>` land here as `Reference(Struct { struct_id, .. })`.
fn struct_id_of(ty: &Type) -> Option<(StructID, Vec<Type>)> {
    match ty {
        Type::Struct {
            struct_id,
            type_args,
        } => Some((*struct_id, type_args.clone())),
        Type::Reference(inner) => struct_id_of(inner),
        Type::MutableReference(inner, _state) => struct_id_of(inner),
        _ => None,
    }
}

fn rewrite_body_ctx(
    node: IRNode,
    dyn_ops: &HashMap<FunctionID, DynFieldOp>,
    df_indices: &HashMap<StructID, Vec<DfFieldEntry>>,
    typed_map: &TypedMapFunctions,
    uid_bindings: &mut UidBindings,
) -> IRNode {
    match node {
        IRNode::Let {
            pattern,
            value,
            body,
        } => {
            // Track UID field accesses: if value is `parent.id` (field 0), record
            // that this variable holds the UID of that parent struct.
            //
            // Also propagate through plain copies (`let $tN := Var(other)`):
            // if `other` is in `uid_bindings`, alias `$tN` to the same
            // entry. The IR translator collapses Move's
            // `let id = vault.get_vault_uid()` followed by
            // `dynamic_field::exists_(id, key)` into a `let $t12 := vault`
            // copy and a call `Function(exists_, [$t12, key])` (the
            // BorrowField-then-call substitution that passes the parent
            // slot directly to the dyn-field op). Phase 2's
            // `extract_parent_info_ctx` then needs `$t12` mapped back
            // to the parent struct so the rewrite fires.
            if pattern.len() == 1 {
                match &*value {
                    IRNode::Field {
                        struct_id,
                        field_index: 0,
                        base,
                    } => {
                        if df_indices.contains_key(struct_id) {
                            uid_bindings.insert(pattern[0].clone(), (*struct_id, *base.clone()));
                        }
                    }
                    IRNode::Var(other) => {
                        if let Some(entry) = uid_bindings.get(other).cloned() {
                            uid_bindings.insert(pattern[0].clone(), entry);
                        }
                    }
                    _ => {}
                }
            }

            // Check if the value is a dynamic field call (BorrowMut excluded — handled pre-threading)
            let should_rewrite = if let IRNode::Call { function, args, .. } = &*value {
                if let Some(&op) = dyn_ops.get(function) {
                    if op != DynFieldOp::BorrowMut {
                        args.first()
                            .and_then(|a| extract_parent_info_ctx(a, uid_bindings))
                            .and_then(|(sid, _)| df_indices.get(&sid))
                            .map(|_| op)
                    } else {
                        None
                    }
                } else {
                    None
                }
            } else {
                None
            };

            if let Some(op) = should_rewrite {
                if let IRNode::Call {
                    type_args, args, ..
                } = &*value
                {
                    if let Some(rewritten) = try_rewrite_dyn_field_call_ctx(
                        op,
                        &pattern,
                        type_args,
                        args,
                        (*body).clone(),
                        dyn_ops,
                        df_indices,
                        typed_map,
                        uid_bindings,
                    ) {
                        return rewrite_body_ctx(
                            rewritten,
                            dyn_ops,
                            df_indices,
                            typed_map,
                            uid_bindings,
                        );
                    }
                }
                // should_rewrite checked df_indices.get(&sid).is_some(); lookup_df_entry
                // is stricter (also matches key/value types). When the type
                // instantiations don't match any registered ghost field, fall back to
                // leaving the call unchanged.
                let _ = op;
            }

            // No rewrite — recurse into children
            IRNode::Let {
                pattern,
                value: Box::new(rewrite_body_ctx(
                    *value,
                    dyn_ops,
                    df_indices,
                    typed_map,
                    uid_bindings,
                )),
                body: Box::new(rewrite_body_ctx(
                    *body,
                    dyn_ops,
                    df_indices,
                    typed_map,
                    uid_bindings,
                )),
            }
        }

        // Recurse into other node types
        IRNode::If {
            cond,
            then_branch,
            else_branch,
        } => IRNode::If {
            cond: Box::new(rewrite_body_ctx(
                *cond,
                dyn_ops,
                df_indices,
                typed_map,
                uid_bindings,
            )),
            then_branch: Box::new(rewrite_body_ctx(
                *then_branch,
                dyn_ops,
                df_indices,
                typed_map,
                uid_bindings,
            )),
            else_branch: Box::new(rewrite_body_ctx(
                *else_branch,
                dyn_ops,
                df_indices,
                typed_map,
                uid_bindings,
            )),
        },
        IRNode::Match { scrutinee, cases } => IRNode::Match {
            scrutinee: Box::new(rewrite_body_ctx(
                *scrutinee,
                dyn_ops,
                df_indices,
                typed_map,
                uid_bindings,
            )),
            cases: cases
                .into_iter()
                .map(|(tag, binds, body)| {
                    (
                        tag,
                        binds,
                        rewrite_body_ctx(body, dyn_ops, df_indices, typed_map, uid_bindings),
                    )
                })
                .collect(),
        },
        // Recurse into Call args. Without this, dyn-field calls embedded
        // inside other calls (e.g. `Prover.asserts(dynamic_field::exists_(...))`)
        // never get rewritten to `TypedMap.has(...)`. This pattern is
        // ubiquitous in extracted spec functions (`.requires` / `.ensures` /
        // `.asserts_cond_*`) where the original Move source had
        // `asserts(dynamic_field::exists_with_type<...>(uid, key))`.
        //
        // We can rewrite directly here only when the call IS the dyn-field
        // op (single-arg position, no Let pattern to thread); for that case
        // we pretend the call is the value of a synthetic empty-pattern Let
        // and recurse, which lets the existing `should_rewrite` branch in
        // the Let arm catch it. For other arg shapes, we just recurse into
        // the args.
        IRNode::Call {
            function,
            type_args,
            args,
        } => {
            // If THIS call is a dyn-field op, wrap it in an empty-pattern
            // Let so the existing rewrite path picks it up. The Let body
            // is `()` since the caller didn't capture a result here.
            if let Some(&op) = dyn_ops.get(&function) {
                if op != DynFieldOp::BorrowMut {
                    if let Some(rewritten) = try_rewrite_dyn_field_call_ctx(
                        op,
                        &[],
                        &type_args,
                        &args,
                        IRNode::Tuple(vec![]),
                        dyn_ops,
                        df_indices,
                        typed_map,
                        uid_bindings,
                    ) {
                        // The rewriter produces a Let-shape; we need its
                        // value (the rewritten call) to substitute for our
                        // original Call. Pull out the value if possible,
                        // otherwise fall back to the wrapped form.
                        if let IRNode::Let { value, .. } = rewritten {
                            return *value;
                        }
                        return rewritten;
                    }
                }
            }
            IRNode::Call {
                function,
                type_args,
                args: args
                    .into_iter()
                    .map(|a| rewrite_body_ctx(a, dyn_ops, df_indices, typed_map, uid_bindings))
                    .collect(),
            }
        }

        // Fix MutableBorrow nodes that wrap field 0 (id) of a DF struct.
        // After mutable threading, Dynamic_field.add/remove calls produce MutableBorrow
        // wrapping parent.id with reconstruction { parent with id := __v }.
        // Phase 2 rewrites the call to TypedMap.set/erase (returning List, not UID),
        // so the MutableBorrow must target dynamic_fields instead.
        IRNode::MutableBorrow {
            val_expr,
            reconstruct_param,
            reconstruct_expr,
            state_type,
        } => {
            if let IRNode::Field {
                struct_id,
                field_index: 0,
                ref base,
            } = *val_expr
            {
                if let Some(entries) = df_indices.get(&struct_id) {
                    if entries.len() == 1 {
                        let df_idx = entries[0].field_index;
                        let new_val_expr = IRNode::Field {
                            struct_id,
                            field_index: df_idx,
                            base: base.clone(),
                        };
                        let new_reconstruct = fix_update_field(
                            *reconstruct_expr,
                            &[reconstruct_param.clone()],
                            struct_id,
                            df_idx,
                        );
                        return IRNode::MutableBorrow {
                            val_expr: Box::new(new_val_expr),
                            reconstruct_param,
                            reconstruct_expr: Box::new(new_reconstruct),
                            state_type,
                        };
                    }
                }
            }
            IRNode::MutableBorrow {
                val_expr,
                reconstruct_param,
                reconstruct_expr,
                state_type,
            }
        }

        // Leaf nodes — return as-is
        other => other,
    }
}

/// Try to rewrite a single dynamic field call.
/// Returns Some(rewritten_node) on success, None if the pattern doesn't match.
fn try_rewrite_dyn_field_call_ctx(
    op: DynFieldOp,
    let_pattern: &[TempId],
    type_args: &[Type],
    args: &[IRNode],
    body: IRNode,
    dyn_ops: &HashMap<FunctionID, DynFieldOp>,
    df_indices: &HashMap<StructID, Vec<DfFieldEntry>>,
    typed_map: &TypedMapFunctions,
    uid_bindings: &UidBindings,
) -> Option<IRNode> {
    // Extract the parent struct info, resolving through variable bindings if needed
    let (struct_id, parent_expr) = extract_parent_info_ctx(&args[0], uid_bindings)?;
    // Match key type from call's type_args to find the correct ghost field
    let call_key_type = type_args.first();
    let call_value_type = type_args.get(1);
    let entry = lookup_df_entry(df_indices, struct_id, call_key_type, call_value_type)?;
    let df_idx = entry.field_index;
    // Type args for the synthetic TypedMap function: [K, V] — prefer
    // the call's own `type_args` over the ghost field's declared K / V.
    // The call's `type_args` are the actual types at the use site
    // (e.g. `Dynamic_field.borrow<u64, Node<V>>` carries `[u64, Node<V>]`),
    // whereas the ghost field's declared types may be a structural
    // placeholder when the field was synthesised by
    // `native_ghost_fields::augment_structs_with_native_ghost_fields`
    // (which runs when upstream's accessibility-gated
    // `DynamicFieldAnalysisProcessor` failed to record the actual K / V
    // for this struct). Falling back to the entry only matters when a
    // call somehow lacks `type_args`, which doesn't happen for any of
    // the dynamic-field operations we rewrite here.
    let tm_type_args = vec![
        call_key_type
            .cloned()
            .unwrap_or_else(|| entry.key_type.clone()),
        call_value_type
            .cloned()
            .unwrap_or_else(|| entry.value_type.clone()),
    ];

    // Build the dynamic_fields field access
    let df_access = IRNode::Field {
        struct_id,
        field_index: df_idx,
        base: Box::new(parent_expr.clone()),
    };

    // If the call's first arg was `Var(slot)` (i.e. the parent's UID was
    // extracted into a temp before the call), capture the slot name so we
    // can strip the post-call WriteBack that mutable_threading inserted to
    // thread the new UID back into that slot. After rewriting, the
    // threaded-back value is a `dynamic_fields` list, not a UID, and
    // re-binding it to the (UID-typed) slot would shadow with the wrong
    // type — exactly the Skip_list `t_t21` regression. Once the
    // reconstruction is patched into `parent.dynamic_fields` via
    // `fix_update_field`, the slot rebinding is redundant.
    let uid_slot_name: Option<TempId> = match &args[0] {
        IRNode::Var(name) => Some(name.clone()),
        _ => None,
    };

    match op {
        DynFieldOp::Add => {
            // Dynamic_field.add K V (parent.id) key value -> returns new UID
            // We rewrite to: TypedMap.set (parent.dynamic_fields) key value -> returns new df list
            // Then fix the reconstruction: { parent with id := result } -> { parent with dynamic_fields := result }
            assert!(args.len() >= 3, "Dynamic_field.add needs at least 3 args");
            let key = args[1].clone();
            let value = args[2].clone();

            let new_call = IRNode::Call {
                function: typed_map.set_id,
                type_args: tm_type_args,
                args: vec![df_access, key, value],
            };

            // Fix the body: replace { parent with id := __mut_ret } with { parent with dynamic_fields := __mut_ret }
            let fixed_body = fix_reconstruction(body, let_pattern, struct_id, df_idx);
            let fixed_body = redirect_writeback_to_df(
                fixed_body,
                let_pattern,
                uid_slot_name.as_ref(),
                &parent_expr,
                struct_id,
                df_idx,
            );

            Some(IRNode::Let {
                pattern: let_pattern.to_vec(),
                value: Box::new(new_call),
                body: Box::new(fixed_body),
            })
        }

        DynFieldOp::Remove => {
            // Dynamic_field.remove K V (parent.id) key -> returns (value, new_uid)
            // We rewrite to: TypedMap.erase (parent.dynamic_fields) key -> returns (value, new_df_list)
            // Then fix the reconstruction
            assert!(
                args.len() >= 2,
                "Dynamic_field.remove needs at least 2 args"
            );
            let key = args[1].clone();

            let new_call = IRNode::Call {
                function: typed_map.erase_id,
                type_args: tm_type_args,
                args: vec![df_access, key],
            };

            let fixed_body = fix_reconstruction(body, let_pattern, struct_id, df_idx);
            let fixed_body =
                strip_writeback_to_uid_slot(fixed_body, let_pattern, uid_slot_name.as_ref());

            Some(IRNode::Let {
                pattern: let_pattern.to_vec(),
                value: Box::new(new_call),
                body: Box::new(fixed_body),
            })
        }

        DynFieldOp::RemoveIfExists => {
            // Dynamic_field.remove_if_exists K V (parent.id) key -> returns
            //   (Option V, new_uid)   (Option V from Move's source signature;
            //                          new_uid threaded back by mutable threading)
            // Rewrite to: TypedMap.erase_if_exists (parent.dynamic_fields_N) key
            //   -> returns (MoveOption V, new_df_list)
            // Then fix the reconstruction (parent.id swap -> parent.dynamic_fields_N)
            // and strip the stale UID-slot writeback.
            assert!(
                args.len() >= 2,
                "Dynamic_field.remove_if_exists needs at least 2 args"
            );
            let key = args[1].clone();

            let new_call = IRNode::Call {
                function: typed_map.erase_if_exists_id,
                type_args: tm_type_args,
                args: vec![df_access, key],
            };

            let fixed_body = fix_reconstruction(body, let_pattern, struct_id, df_idx);
            let fixed_body =
                strip_writeback_to_uid_slot(fixed_body, let_pattern, uid_slot_name.as_ref());

            Some(IRNode::Let {
                pattern: let_pattern.to_vec(),
                value: Box::new(new_call),
                body: Box::new(fixed_body),
            })
        }

        DynFieldOp::Borrow => {
            // Dynamic_field.borrow K V (parent.id) key -> returns value
            // We rewrite to: TypedMap.get (parent.dynamic_fields) key -> returns value
            assert!(
                args.len() >= 2,
                "Dynamic_field.borrow needs at least 2 args"
            );
            let key = args[1].clone();

            let new_call = IRNode::Call {
                function: typed_map.get_id,
                type_args: tm_type_args,
                args: vec![df_access, key],
            };

            Some(IRNode::Let {
                pattern: let_pattern.to_vec(),
                value: Box::new(new_call),
                body: Box::new(body),
            })
        }

        DynFieldOp::BorrowMut => {
            // BorrowMut is handled by the pre-threading pass (`rewrite_df_borrow_mut_pre_threading`).
            // After pre-threading + mutable threading, no Call(borrow_mut, ...) nodes should remain.
            // If we reach here, it means the pre-threading pass did not run or did not match this
            // call — fall through and leave the node unchanged by returning None.
            None
        }

        DynFieldOp::Exists => {
            // Dynamic_field.exists_with_type K V (parent.id) key -> returns Prop
            // We rewrite to: TypedMap.has (parent.dynamic_fields) key -> returns Prop
            assert!(
                args.len() >= 2,
                "Dynamic_field.exists needs at least 2 args"
            );
            let key = args[1].clone();

            let new_call = IRNode::Call {
                function: typed_map.has_id,
                type_args: tm_type_args,
                args: vec![df_access, key],
            };

            Some(IRNode::Let {
                pattern: let_pattern.to_vec(),
                value: Box::new(new_call),
                body: Box::new(body),
            })
        }
    }
}

/// Extract the parent struct ID and expression from a UID field access.
/// The first arg to Dynamic_field functions is `parent.id` (field 0).
/// Returns (struct_id, parent_expr) if the pattern matches.
/// Resolves through variable bindings when the UID was extracted into a temp.
fn extract_parent_info_ctx(
    uid_arg: &IRNode,
    uid_bindings: &UidBindings,
) -> Option<(StructID, IRNode)> {
    match uid_arg {
        // Simple case: parent.id
        IRNode::Field {
            struct_id,
            field_index: 0,
            base,
        } => Some((*struct_id, *base.clone())),

        // Variable case: the UID was extracted into a temp earlier
        // (e.g., let $t3 := list.id; ... Call(dyn_borrow, $t3, key))
        IRNode::Var(name) => uid_bindings.get(name).cloned(),

        _ => None,
    }
}

/// Fix reconstruction: find `{ parent with id := result }` and change to
/// `{ parent with dynamic_fields := result }`.
/// Also handles the case where the result is a tuple (value, new_uid) for remove/borrow_mut.
fn fix_reconstruction(
    node: IRNode,
    result_pattern: &[TempId],
    target_struct_id: StructID,
    df_field_idx: usize,
) -> IRNode {
    match node {
        IRNode::Let {
            pattern,
            value,
            body,
        } => {
            let fixed_value =
                fix_update_field(*value, result_pattern, target_struct_id, df_field_idx);
            let fixed_body =
                fix_reconstruction(*body, result_pattern, target_struct_id, df_field_idx);
            IRNode::Let {
                pattern,
                value: Box::new(fixed_value),
                body: Box::new(fixed_body),
            }
        }
        IRNode::If {
            cond,
            then_branch,
            else_branch,
        } => IRNode::If {
            cond: Box::new(fix_reconstruction(
                *cond,
                result_pattern,
                target_struct_id,
                df_field_idx,
            )),
            then_branch: Box::new(fix_reconstruction(
                *then_branch,
                result_pattern,
                target_struct_id,
                df_field_idx,
            )),
            else_branch: Box::new(fix_reconstruction(
                *else_branch,
                result_pattern,
                target_struct_id,
                df_field_idx,
            )),
        },
        other => other,
    }
}

/// Strip the legacy `WriteBack { child: <__mut_ret>, parent: <slot> }` that
/// `mutable_threading::fix_call_sites` inserted to thread the call's
/// last-positional augmented return back into a UID temp slot. After the
/// call has been rewritten from `Dynamic_field.{add,remove}` to
/// `TypedMap.{set,erase}`, the threaded-back value is a `dynamic_fields`
/// list, not a UID. Re-binding it onto the original UID-typed slot would
/// shadow with the wrong type — exactly the Skip_list `t_t21` regression
/// where a pre-rewrite `BorrowField(self, id)` introduced
/// `let t_t21 := list.id : UID`, the rewriter changed the call to return
/// a list, and the WriteBack rendered as
/// `let t_t21 := __mut_ret_1 : List<...>`. Subsequent uses of `t_t21`
/// (e.g. as args to a sibling helper that was generated assuming
/// `t_t21 : UID`) failed type-check.
///
/// We strip only WriteBacks whose child is in `let_pattern` (i.e. the
/// __mut_ret produced by the destructuring of THIS call) and whose
/// parent is the captured `uid_slot`. Everything else is left untouched.
/// and fall back to stripping the now-type-incorrect write-back.
fn redirect_writeback_to_df(
    node: IRNode,
    let_pattern: &[TempId],
    uid_slot: Option<&TempId>,
    parent_expr: &IRNode,
    struct_id: StructID,
    df_field_idx: usize,
) -> IRNode {
    let uid_slot = match uid_slot {
        Some(s) => s.clone(),
        None => return node,
    };
    let parent_var = match parent_expr {
        IRNode::Var(name) => name.clone(),
        _ => return strip_writeback_to_uid_slot(node, let_pattern, Some(&uid_slot)),
    };
    let pattern_set: std::collections::BTreeSet<TempId> = let_pattern.iter().cloned().collect();
    redirect_writeback_inner(
        node,
        &uid_slot,
        &pattern_set,
        &parent_var,
        parent_expr,
        struct_id,
        df_field_idx,
    )
}

fn redirect_writeback_inner(
    node: IRNode,
    uid_slot: &TempId,
    pattern_set: &std::collections::BTreeSet<TempId>,
    parent_var: &TempId,
    parent_expr: &IRNode,
    struct_id: StructID,
    df_field_idx: usize,
) -> IRNode {
    match node {
        IRNode::Let {
            pattern,
            value,
            body,
        } => {
            if pattern.is_empty() {
                if let IRNode::WriteBack { child, parent, .. } = value.as_ref() {
                    if parent == uid_slot && pattern_set.contains(child) {
                        let update = IRNode::UpdateField {
                            base: Box::new(parent_expr.clone()),
                            struct_id,
                            field_index: df_field_idx,
                            value: Box::new(IRNode::Var(child.clone())),
                        };
                        return IRNode::Let {
                            pattern: vec![parent_var.clone()],
                            value: Box::new(update),
                            body: Box::new(redirect_writeback_inner(
                                *body,
                                uid_slot,
                                pattern_set,
                                parent_var,
                                parent_expr,
                                struct_id,
                                df_field_idx,
                            )),
                        };
                    }
                }
            }
            IRNode::Let {
                pattern,
                value,
                body: Box::new(redirect_writeback_inner(
                    *body,
                    uid_slot,
                    pattern_set,
                    parent_var,
                    parent_expr,
                    struct_id,
                    df_field_idx,
                )),
            }
        }
        IRNode::If {
            cond,
            then_branch,
            else_branch,
        } => IRNode::If {
            cond,
            then_branch: Box::new(redirect_writeback_inner(
                *then_branch,
                uid_slot,
                pattern_set,
                parent_var,
                parent_expr,
                struct_id,
                df_field_idx,
            )),
            else_branch: Box::new(redirect_writeback_inner(
                *else_branch,
                uid_slot,
                pattern_set,
                parent_var,
                parent_expr,
                struct_id,
                df_field_idx,
            )),
        },
        other => other,
    }
}

fn strip_writeback_to_uid_slot(
    node: IRNode,
    let_pattern: &[TempId],
    uid_slot: Option<&TempId>,
) -> IRNode {
    let uid_slot = match uid_slot {
        Some(s) => s.clone(),
        None => return node,
    };
    let pattern_set: std::collections::BTreeSet<TempId> = let_pattern.iter().cloned().collect();
    strip_writeback_inner(node, &uid_slot, &pattern_set)
}

fn strip_writeback_inner(
    node: IRNode,
    uid_slot: &TempId,
    pattern_set: &std::collections::BTreeSet<TempId>,
) -> IRNode {
    match node {
        IRNode::Let {
            pattern,
            value,
            body,
        } => {
            // Drop empty-pattern Lets whose value is a WriteBack threading
            // a let-pattern child back onto the UID slot.
            if pattern.is_empty() {
                if let IRNode::WriteBack { child, parent, .. } = value.as_ref() {
                    if parent == uid_slot && pattern_set.contains(child) {
                        return strip_writeback_inner(*body, uid_slot, pattern_set);
                    }
                }
            }
            IRNode::Let {
                pattern,
                value,
                body: Box::new(strip_writeback_inner(*body, uid_slot, pattern_set)),
            }
        }
        IRNode::If {
            cond,
            then_branch,
            else_branch,
        } => IRNode::If {
            cond,
            then_branch: Box::new(strip_writeback_inner(*then_branch, uid_slot, pattern_set)),
            else_branch: Box::new(strip_writeback_inner(*else_branch, uid_slot, pattern_set)),
        },
        other => other,
    }
}

/// Fix a single UpdateField node: if it updates field 0 (id) of the target struct
/// with the result of our rewritten call, change it to update dynamic_fields instead.
fn fix_update_field(
    node: IRNode,
    result_pattern: &[TempId],
    target_struct_id: StructID,
    df_field_idx: usize,
) -> IRNode {
    match node {
        IRNode::UpdateField {
            base,
            struct_id,
            field_index: 0,
            value,
        } if struct_id == target_struct_id => {
            // Check if the value references our result variable
            if references_any_of(&value, result_pattern) {
                IRNode::UpdateField {
                    base,
                    struct_id,
                    field_index: df_field_idx,
                    value,
                }
            } else {
                IRNode::UpdateField {
                    base,
                    struct_id,
                    field_index: 0,
                    value,
                }
            }
        }
        other => other,
    }
}

/// Check if a node references any of the given variable names
fn references_any_of(node: &IRNode, names: &[TempId]) -> bool {
    match node {
        IRNode::Var(name) => names.iter().any(|n| n == name),
        _ => node
            .iter_children()
            .any(|child| references_any_of(child, names)),
    }
}
