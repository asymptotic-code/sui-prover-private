// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Stored-value data invariants (the legacy pipeline's assume/assert
//! discipline for values stored in Tables / dynamic fields).
//!
//! The client declares a Lean predicate per container slot (or per value
//! type) as `def <Module>.<Struct>.<field>.data_inv (v : V) : Prop` (slot-
//! scoped) or `def <Module>.<Struct>.data_inv (v : V) : Prop` (type-wide),
//! scanned from `sources/lean/**/*.lean` into
//! `lean_termination_decls.data_inv` (same sweep as the termination hooks).
//!
//! This pass then:
//!   1. resolves each declared stem against the struct table and the ghost
//!      `dynamic_fields*` slot registry (hard error on a typo — a bad stem
//!      must not silently produce an inert invariant);
//!   2. computes the set of functions whose bodies touch a declared slot and
//!      closes it over the caller graph;
//!   3. threads `hdinv_* : TypedMap.all K V <pred> (<param-path>.dynamic_fields)`
//!      hypotheses onto the SPEC functions (`<base>_spec.aborts`) in that
//!      closure — the assume half. Because this backend's proofs unfold impl
//!      bodies wholesale, the hypothesis is only ever consumed at the spec
//!      boundary, so no def-level threading / call-site discharge macros are
//!      needed (deviation from the original design doc, which mirrored the
//!      callee_requires_precond def-level cascade);
//!   4. records `_data_inv` preservation goals — the assert half — for each
//!      threaded spec whose impl returns the updated container root. The
//!      Correctness renderer emits them beside the spec's own obligation.
//!
//! Inert-by-default: without `def <stem>.data_inv` declarations the pass
//! returns immediately and output is byte-identical.

use crate::data::functions::{ProofParam, ProofParamType};
use crate::data::types::Type;
use crate::data::{DataInvGoal, Program};
use crate::{FunctionID, IRNode, StructID};
use std::collections::{BTreeMap, HashMap, HashSet};

/// Mirror the renderer's identifier escaping for the simple param-name cases
/// (same as `callee_requires_precond::escape_param`).
fn escape_param(name: &str) -> String {
    let s = if let Some(rest) = name.strip_prefix('$') {
        format!("t_{}", rest)
    } else {
        name.replace('$', "_t_")
    };
    s.replace('#', "_")
}

/// One resolved container slot covered by a declared invariant.
#[derive(Debug, Clone)]
struct InvSlot {
    owner_sid: StructID,
    owner_field_idx: usize,
    /// Path tail from an owner-struct expression to the ghost map, including
    /// the leading dot (e.g. `.validator_candidates.dynamic_fields`).
    map_tail: String,
    key_type: Type,
    value_type: Type,
    pred: String,
}

fn is_ghost_df_field(name: &str) -> bool {
    name == "dynamic_fields" || name.starts_with("dynamic_fields_")
}

/// Extract `(K, V)` from a ghost field type `List (K × V)`.
fn ghost_kv(field_type: &Type) -> Option<(Type, Type)> {
    if let Type::Vector(inner) = field_type {
        if let Type::Tuple(pair) = inner.as_ref() {
            if pair.len() == 2 {
                return Some((pair[0].clone(), pair[1].clone()));
            }
        }
    }
    None
}

/// Resolve the slot(s) reached through struct `owner`'s field `idx`:
/// either the field is itself a ghost `dynamic_fields*` map, or it is a
/// container struct (Table & co.) carrying exactly one ghost map.
fn slots_through_field(program: &Program, owner_sid: StructID, idx: usize) -> Vec<InvSlot> {
    let owner = program.structs.get(&owner_sid);
    let field = &owner.fields[idx];
    if let Some((k, v)) = ghost_kv(&field.field_type) {
        return vec![InvSlot {
            owner_sid,
            owner_field_idx: idx,
            map_tail: format!(".{}", field.name),
            key_type: k,
            value_type: v,
            pred: String::new(),
        }];
    }
    if let Type::Struct {
        struct_id: c_sid,
        type_args,
    } = &field.field_type
    {
        let container = program.structs.get(c_sid);
        let ghosts: Vec<(usize, (Type, Type))> = container
            .fields
            .iter()
            .enumerate()
            .filter(|(_, f)| is_ghost_df_field(&f.name))
            .filter_map(|(i, f)| ghost_kv(&f.field_type).map(|kv| (i, kv)))
            .collect();
        if ghosts.len() == 1 {
            let (gidx, (k, v)) = &ghosts[0];
            let gname = &container.fields[*gidx].name;
            return vec![InvSlot {
                owner_sid,
                owner_field_idx: idx,
                map_tail: format!(".{}.{}", field.name, gname),
                key_type: k.substitute_type_params(type_args),
                value_type: v.substitute_type_params(type_args),
                pred: String::new(),
            }];
        }
    }
    Vec::new()
}

/// Resolve a declared stem into slots. Panics (no-fallbacks rule) when the
/// stem does not name a known struct / field with a registered ghost map.
fn resolve_stem(program: &Program, stem: &str) -> Vec<InvSlot> {
    let segs: Vec<&str> = stem.split('.').collect();
    let find_struct = |mod_seg: &str, struct_seg: &str| -> StructID {
        let matches: Vec<StructID> = program
            .structs
            .iter()
            .filter(|(_, s)| {
                s.name == struct_seg
                    && program
                        .modules
                        .get(&s.module_id)
                        .name
                        .eq_ignore_ascii_case(mod_seg)
            })
            .map(|(sid, _)| *sid)
            .collect();
        assert!(
            !matches.is_empty(),
            "stored_value_invariants: declaration `{}.data_inv` does not resolve: no struct `{}` in module `{}`",
            stem, struct_seg, mod_seg
        );
        assert!(
            matches.len() == 1,
            "stored_value_invariants: declaration `{}.data_inv` is ambiguous ({} structs match)",
            stem,
            matches.len()
        );
        matches[0]
    };
    let pred = format!("{}.data_inv", stem);
    match segs.len() {
        3 => {
            let owner_sid = find_struct(segs[0], segs[1]);
            let owner = program.structs.get(&owner_sid);
            let idx = owner
                .fields
                .iter()
                .position(|f| f.name == segs[2])
                .unwrap_or_else(|| {
                    panic!(
                        "stored_value_invariants: declaration `{}.data_inv` does not resolve: struct `{}` has no field `{}`",
                        stem, segs[1], segs[2]
                    )
                });
            let mut slots = slots_through_field(program, owner_sid, idx);
            assert!(
                !slots.is_empty(),
                "stored_value_invariants: declaration `{}.data_inv` does not resolve: field `{}` of `{}` is not a dynamic-field container slot",
                stem, segs[2], segs[1]
            );
            for s in &mut slots {
                s.pred = pred.clone();
            }
            slots
        }
        2 => {
            // Type-wide: every registered slot whose VALUE type is this struct.
            let value_sid = find_struct(segs[0], segs[1]);
            let mut slots = Vec::new();
            let owner_ids: Vec<StructID> = program.structs.iter().map(|(sid, _)| *sid).collect();
            for owner_sid in owner_ids {
                let n_fields = program.structs.get(&owner_sid).fields.len();
                for idx in 0..n_fields {
                    for mut slot in slots_through_field(program, owner_sid, idx) {
                        if matches!(&slot.value_type, Type::Struct { struct_id, .. } if *struct_id == value_sid)
                        {
                            slot.pred = pred.clone();
                            slots.push(slot);
                        }
                    }
                }
            }
            assert!(
                !slots.is_empty(),
                "stored_value_invariants: declaration `{}.data_inv` does not resolve: no container slot stores `{}` values",
                stem, segs[1]
            );
            slots
        }
        _ => panic!(
            "stored_value_invariants: declaration `{}.data_inv` must have a `<Module>.<Struct>` or `<Module>.<Struct>.<field>` stem",
            stem
        ),
    }
}

/// Whether `body` touches the slot: a `Field` projection of the owner's slot
/// field, or a call to a field-accessor function reading it.
fn touches_slot(program: &Program, body: &IRNode, slot: &InvSlot) -> bool {
    body.iter().any(|n| match n {
        IRNode::Field {
            struct_id,
            field_index,
            ..
        } => *struct_id == slot.owner_sid && *field_index == slot.owner_field_idx,
        IRNode::UpdateField {
            struct_id,
            field_index,
            ..
        } => *struct_id == slot.owner_sid && *field_index == slot.owner_field_idx,
        IRNode::Call { function, .. } => {
            let f = program.functions.get(function);
            f.is_field_accessor()
                .is_some_and(|(sid, idx)| sid == slot.owner_sid && idx == slot.owner_field_idx)
        }
        _ => false,
    })
}

/// All field-name chains (max depth 3) from `ty` to the owner struct.
fn chains_to_owner(program: &Program, ty: &Type, owner_sid: StructID) -> Vec<Vec<String>> {
    fn go(
        program: &Program,
        ty: &Type,
        owner_sid: StructID,
        depth: usize,
        seen: &mut Vec<StructID>,
        prefix: &mut Vec<String>,
        out: &mut Vec<Vec<String>>,
    ) {
        if let Type::Struct {
            struct_id,
            type_args,
        } = ty
        {
            if *struct_id == owner_sid {
                out.push(prefix.clone());
                return;
            }
            if depth == 0 || seen.contains(struct_id) {
                return;
            }
            seen.push(*struct_id);
            let s = program.structs.get(struct_id);
            if s.variants.is_none() {
                for f in &s.fields {
                    let ft = f.field_type.substitute_type_params(type_args);
                    prefix.push(f.name.clone());
                    go(program, &ft, owner_sid, depth - 1, seen, prefix, out);
                    prefix.pop();
                }
            }
            seen.pop();
        }
    }
    let mut out = Vec::new();
    go(
        program,
        ty,
        owner_sid,
        3,
        &mut Vec::new(),
        &mut Vec::new(),
        &mut out,
    );
    out
}

/// One resolved world-mode invariant target: a parent-uid source rooted at
/// an owner struct (unified-backend design §7, Phase 5).
#[derive(Debug, Clone)]
struct WorldInvSlot {
    owner_sid: StructID,
    /// Path tail from an owner-struct expression to its UID, including the
    /// leading dot (e.g. `.id` or `.validator_candidates.id`).
    parent_tail: String,
    pred: String,
}

fn is_uid_struct(program: &Program, sid: StructID) -> bool {
    program.structs.has(sid) && program.structs.get(&sid).qualified_name == "object::UID"
}

/// Resolve a UID source through struct `owner`'s field `idx`: the field is
/// itself a `UID`, or a UID-headed struct (Table & co. — their df entries
/// live under their own id in world-mode).
fn world_slot_through_field(program: &Program, owner_sid: StructID, idx: usize) -> Option<String> {
    let owner = program.structs.get(&owner_sid);
    let field = &owner.fields[idx];
    match &field.field_type {
        Type::Struct { struct_id, .. } if is_uid_struct(program, *struct_id) => {
            Some(format!(".{}", field.name))
        }
        Type::Struct { struct_id, .. } if program.structs.has(*struct_id) => {
            let container = program.structs.get(struct_id);
            match container.fields.first() {
                Some(f)
                    if matches!(&f.field_type, Type::Struct { struct_id: uid_sid, .. }
                        if is_uid_struct(program, *uid_sid)) =>
                {
                    Some(format!(".{}.{}", field.name, f.name))
                }
                _ => None,
            }
        }
        _ => None,
    }
}

/// Resolve a declared stem into world-mode slots. Returns `None` when the
/// stem's MODULE is absent from this program (per-target generation modes
/// prune modules, so a package-level hook can legitimately target another
/// target's cone); panics (no-fallbacks rule) when the module exists but the
/// stem names no UID source in it.
fn resolve_world_stem(program: &Program, stem: &str) -> Option<WorldInvSlot> {
    let segs: Vec<&str> = stem.split('.').collect();
    assert!(
        segs.len() == 2 || segs.len() == 3,
        "stored_value_invariants (world): declaration `{}.data_inv` must have a \
         `<Module>.<Struct>` or `<Module>.<Struct>.<field>` stem",
        stem
    );

    let find_struct = |mod_seg: &str, struct_seg: &str| -> Option<StructID> {
        let matches: Vec<StructID> = program
            .structs
            .iter()
            .filter(|(_, s)| {
                s.name == struct_seg
                    && program
                        .modules
                        .get(&s.module_id)
                        .name
                        .eq_ignore_ascii_case(mod_seg)
            })
            .map(|(sid, _)| *sid)
            .collect();
        if matches.is_empty() {
            // Per-target generation modes prune modules/structs, so a
            // package-level hook can legitimately miss this target's cone.
            // Report (never silently inert on a typo) and skip.
            eprintln!(
                "warning: stored_value_invariants (world): declaration `{}.data_inv` does not \
                 resolve in this target (no struct `{}` in module `{}`) — skipped",
                stem, struct_seg, mod_seg
            );
            return None;
        }
        assert!(
            matches.len() == 1,
            "stored_value_invariants (world): declaration `{}.data_inv` is ambiguous \
             ({} structs match)",
            stem,
            matches.len()
        );
        Some(matches[0])
    };
    let pred = format!("{}.data_inv", stem);
    match segs.len() {
        3 => {
            let owner_sid = find_struct(segs[0], segs[1])?;
            let owner = program.structs.get(&owner_sid);
            let idx = owner
                .fields
                .iter()
                .position(|f| f.name == segs[2])
                .unwrap_or_else(|| {
                    panic!(
                        "stored_value_invariants (world): declaration `{}.data_inv` does not \
                         resolve: struct `{}` has no field `{}`",
                        stem, segs[1], segs[2]
                    )
                });
            let parent_tail =
                world_slot_through_field(program, owner_sid, idx).unwrap_or_else(|| {
                    panic!(
                        "stored_value_invariants (world): declaration `{}.data_inv` does not \
                         resolve: field `{}` of `{}` is not a UID or UID-headed container",
                        stem, segs[2], segs[1]
                    )
                });
            Some(WorldInvSlot {
                owner_sid,
                parent_tail,
                pred,
            })
        }
        2 => {
            // Owner-wide: the struct's own UID head is the parent source.
            let owner_sid = find_struct(segs[0], segs[1])?;
            let parent_tail =
                world_slot_through_field(program, owner_sid, 0).unwrap_or_else(|| {
                    panic!(
                        "stored_value_invariants (world): declaration `{}.data_inv` does not \
                     resolve: struct `{}` is not UID-headed",
                        stem, segs[1]
                    )
                });
            Some(WorldInvSlot {
                owner_sid,
                parent_tail,
                pred,
            })
        }
        _ => unreachable!(),
    }
}

/// The world-mode assume/assert flow (unified-backend design §7, Phase 5):
/// `hdinv : Prover.World.World.allDf __world (World.uidNat <parent>) <pred>`
/// hypotheses on spec `.aborts` faces reachable from World state ops, and
/// `_data_inv` preservation goals over the impl's RESULT world. Relevance is
/// world-reachability (a spec whose cone never touches the World needs no
/// hypothesis); the footprint-intersection refinement is deferred to the M1
/// migration where a real invariant corpus exists.
fn thread_world_data_invs(program: &mut Program) {
    let world = program.world_functions.clone().expect("world mode");
    let world_ty = world.world_type();
    let world_native_ids: HashSet<FunctionID> = world.all_ids().into_iter().collect();

    let stems: Vec<String> = program
        .lean_termination_decls
        .data_inv
        .iter()
        .cloned()
        .collect();
    let slots: Vec<WorldInvSlot> = stems
        .iter()
        .filter_map(|stem| resolve_world_stem(program, stem))
        .collect();

    // Caller graph + world-reachability closure.
    let mut callers: HashMap<FunctionID, Vec<FunctionID>> = HashMap::new();
    let fn_ids: Vec<FunctionID> = program.functions.iter_ids().collect();
    for &id in &fn_ids {
        for callee in program.functions.get(&id).body.calls() {
            callers.entry(callee).or_default().push(id);
        }
    }
    let mut reached: HashSet<FunctionID> = HashSet::new();
    let mut worklist: Vec<FunctionID> = fn_ids
        .iter()
        .copied()
        .filter(|id| {
            program
                .functions
                .get(id)
                .body
                .calls()
                .any(|c| world_native_ids.contains(&c))
        })
        .collect();
    while let Some(id) = worklist.pop() {
        if !reached.insert(id) {
            continue;
        }
        if let Some(cs) = callers.get(&id) {
            worklist.extend(cs.iter().copied());
        }
    }

    let mut spec_ids: Vec<FunctionID> = reached
        .iter()
        .copied()
        .filter(|id| {
            let f = program.functions.get(id);
            f.name.ends_with("_spec.aborts")
                && f.signature
                    .parameters
                    .iter()
                    .any(|p| p.name == super::world_threading::WORLD_VAR)
        })
        .collect();
    spec_ids.sort();

    for slot in &slots {
        for &spec_id in &spec_ids {
            let spec = program.functions.get(&spec_id).clone();
            for p in &spec.signature.parameters {
                for chain in chains_to_owner(program, &p.param_type, slot.owner_sid) {
                    let mut path = escape_param(&p.name);
                    for f in &chain {
                        path.push('.');
                        path.push_str(f);
                    }
                    let parent_expr = format!("({}{})", path, slot.parent_tail);
                    let entry = program.fn_data_inv_params.entry(spec_id).or_default();
                    if entry.iter().any(|pp| {
                        matches!(&pp.param_type, ProofParamType::DataInvWorld { parent_expr: pe, pred }
                            if *pe == parent_expr && *pred == slot.pred)
                    }) {
                        continue;
                    }
                    let name = if entry.is_empty() {
                        "hdinv".to_string()
                    } else {
                        format!("hdinv_{}", entry.len())
                    };
                    entry.push(ProofParam {
                        name,
                        param_type: ProofParamType::DataInvWorld {
                            parent_expr: parent_expr.clone(),
                            pred: slot.pred.clone(),
                        },
                    });

                    // Preservation goal over the impl's result world.
                    let base = spec.name.trim_end_matches(".aborts");
                    let Some(impl_base) = base.strip_suffix("_spec") else {
                        continue;
                    };
                    let impl_ids: Vec<FunctionID> = program
                        .functions
                        .iter()
                        .filter(|(id, g)| {
                            *id != spec_id
                                && g.name == impl_base
                                && g.signature.parameters.first().map(|q| q.param_type.clone())
                                    == spec
                                        .signature
                                        .parameters
                                        .first()
                                        .map(|q| q.param_type.clone())
                        })
                        .map(|(id, _)| id)
                        .collect();
                    let Some(&impl_id) = impl_ids.first() else {
                        continue;
                    };
                    let impl_sig = program.functions.get(&impl_id).signature.clone();
                    let n_args = impl_sig.parameters.len();
                    if n_args > spec.signature.parameters.len()
                        || !impl_sig
                            .parameters
                            .iter()
                            .zip(spec.signature.parameters.iter())
                            .all(|(ip, sp)| ip.param_type == sp.param_type)
                    {
                        continue;
                    }
                    // The impl must be a world-threaded value face.
                    let world_proj = if impl_sig.return_type == world_ty {
                        String::new()
                    } else if matches!(&impl_sig.return_type, Type::Tuple(elems)
                        if elems.len() == 2 && elems[1] == world_ty)
                    {
                        ".2".to_string()
                    } else {
                        continue;
                    };
                    let goals = program.data_inv_world_goals.entry(spec_id).or_default();
                    let goal_suffix = if goals.is_empty() {
                        String::new()
                    } else {
                        format!("_{}", goals.len())
                    };
                    goals.push(crate::data::WorldDataInvGoal {
                        goal_suffix,
                        impl_fn_id: impl_id,
                        n_args,
                        world_proj,
                        parent_expr,
                        pred: slot.pred.clone(),
                    });
                }
            }
        }
    }
}

/// Whether `id` is a `<base>_spec.aborts` spec function in a `*specs` module.
fn is_spec_aborts(program: &Program, id: FunctionID) -> bool {
    let f = program.functions.get(&id);
    f.name.ends_with("_spec.aborts")
        && program
            .modules
            .get(&f.module_id)
            .name
            .to_lowercase()
            .ends_with("specs")
}

/// Tuple-projection text for component `i` of an `n`-tuple (right-nested).
fn tuple_proj(i: usize, n: usize) -> String {
    let mut s = ".2".repeat(i);
    if i + 1 < n {
        s.push_str(".1");
    }
    s
}

pub fn thread_stored_value_invariants(program: &mut Program) {
    if program.lean_termination_decls.data_inv.is_empty() {
        return;
    }

    // World-mode face (unified-backend design §7, Phase 5): invariants over
    // World df contents (`allDf`) replace the TypedMap ghost-slot targeting.
    if program.world_functions.is_some() {
        thread_world_data_invs(program);
        return;
    }

    // 1. Resolve declarations into slots; reject overlapping predicates on
    //    one slot (conjunction aliases are not supported in this first cut).
    let stems: Vec<String> = program
        .lean_termination_decls
        .data_inv
        .iter()
        .cloned()
        .collect();
    let mut by_slot: BTreeMap<(StructID, usize), InvSlot> = BTreeMap::new();
    for stem in &stems {
        for slot in resolve_stem(program, stem) {
            let key = (slot.owner_sid, slot.owner_field_idx);
            if let Some(prev) = by_slot.get(&key) {
                panic!(
                    "stored_value_invariants: slot `{}` field #{} is covered by two declarations (`{}` and `{}`); declare a single slot-scoped predicate instead",
                    program.structs.get(&slot.owner_sid).name,
                    slot.owner_field_idx,
                    prev.pred,
                    slot.pred
                );
            }
            by_slot.insert(key, slot);
        }
    }
    let slots: Vec<InvSlot> = by_slot.into_values().collect();

    // 2. Caller graph (callee -> callers), on base call edges.
    let mut callers: HashMap<FunctionID, Vec<FunctionID>> = HashMap::new();
    let fn_ids: Vec<FunctionID> = program.functions.iter_ids().collect();
    for &id in &fn_ids {
        for callee in program.functions.get(&id).body.calls() {
            callers.entry(callee).or_default().push(id);
        }
    }

    for slot in &slots {
        // Seed: functions whose bodies touch the slot; close over callers.
        let mut reached: HashSet<FunctionID> = HashSet::new();
        let mut worklist: Vec<FunctionID> = fn_ids
            .iter()
            .copied()
            .filter(|id| touches_slot(program, &program.functions.get(id).body, slot))
            .collect();
        while let Some(id) = worklist.pop() {
            if !reached.insert(id) {
                continue;
            }
            if let Some(cs) = callers.get(&id) {
                worklist.extend(cs.iter().copied());
            }
        }

        // 3+4. Thread hdinv onto reached spec functions; record goals.
        let mut spec_ids: Vec<FunctionID> = reached
            .iter()
            .copied()
            .filter(|id| is_spec_aborts(program, *id))
            .collect();
        spec_ids.sort();
        for spec_id in spec_ids {
            let spec = program.functions.get(&spec_id).clone();
            for (p_idx, p) in spec.signature.parameters.iter().enumerate() {
                for chain in chains_to_owner(program, &p.param_type, slot.owner_sid) {
                    let mut path = escape_param(&p.name);
                    for f in &chain {
                        path.push('.');
                        path.push_str(f);
                    }
                    let map_expr = format!("({}{})", path, slot.map_tail);
                    let entry = program.fn_data_inv_params.entry(spec_id).or_default();
                    if entry.iter().any(|pp| {
                        matches!(&pp.param_type, ProofParamType::DataInv { map_expr: m, pred, .. }
                            if *m == map_expr && *pred == slot.pred)
                    }) {
                        continue;
                    }
                    let name = if entry.is_empty() {
                        "hdinv".to_string()
                    } else {
                        format!("hdinv_{}", entry.len())
                    };
                    entry.push(ProofParam {
                        name,
                        param_type: ProofParamType::DataInv {
                            key_type: slot.key_type.clone(),
                            value_type: slot.value_type.clone(),
                            pred: slot.pred.clone(),
                            map_expr,
                        },
                    });

                    // Preservation goal: pair the spec with its impl value
                    // function and locate the updated container-root result
                    // components.
                    let base = spec.name.trim_end_matches(".aborts");
                    let impl_base = base
                        .strip_suffix("_spec")
                        .expect("checked by is_spec_aborts");
                    let impl_ids: Vec<FunctionID> = program
                        .functions
                        .iter()
                        .filter(|(_, g)| {
                            g.name == impl_base
                                && !program
                                    .modules
                                    .get(&g.module_id)
                                    .name
                                    .to_lowercase()
                                    .ends_with("specs")
                                && g.signature.parameters.first().map(|q| q.param_type.clone())
                                    == spec
                                        .signature
                                        .parameters
                                        .first()
                                        .map(|q| q.param_type.clone())
                        })
                        .map(|(id, _)| id)
                        .collect();
                    let Some(&impl_id) = impl_ids.first() else {
                        continue;
                    };
                    // The impl's value params must be a positional, type-equal
                    // prefix of the spec's (dead-param elimination can drop
                    // trailing spec params like `ctx`); otherwise skip the goal.
                    let impl_sig = &program.functions.get(&impl_id).signature;
                    let n_args = impl_sig.parameters.len();
                    if n_args > spec.signature.parameters.len()
                        || !impl_sig
                            .parameters
                            .iter()
                            .zip(spec.signature.parameters.iter())
                            .all(|(ip, sp)| ip.param_type == sp.param_type)
                    {
                        continue;
                    }
                    let ret = &program.functions.get(&impl_id).signature.return_type;
                    let components: Vec<(usize, usize)> = match ret {
                        Type::Tuple(elems) => elems
                            .iter()
                            .enumerate()
                            .filter(|(_, t)| *t == &p.param_type)
                            .map(|(i, _)| (i, elems.len()))
                            .collect(),
                        t if t == &p.param_type => vec![(0, 1)],
                        _ => Vec::new(),
                    };
                    for (i, n) in components {
                        let goals = program.data_inv_goals.entry(spec_id).or_default();
                        let goal_suffix = if goals.is_empty() {
                            String::new()
                        } else {
                            format!("_{}", goals.len())
                        };
                        let mut tail = String::new();
                        for f in &chain {
                            tail.push('.');
                            tail.push_str(f);
                        }
                        tail.push_str(&slot.map_tail);
                        goals.push(DataInvGoal {
                            goal_suffix,
                            impl_fn_id: impl_id,
                            n_args,
                            proj_expr: if n == 1 {
                                String::new()
                            } else {
                                tuple_proj(i, n)
                            },
                            map_tail: tail,
                            key_type: slot.key_type.clone(),
                            value_type: slot.value_type.clone(),
                            pred: slot.pred.clone(),
                        });
                    }
                    let _ = p_idx;
                }
            }
        }
    }
}
