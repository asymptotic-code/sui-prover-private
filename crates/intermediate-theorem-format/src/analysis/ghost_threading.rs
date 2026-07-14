// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Ghost-variable threading for the upstream spec-global mechanism
//! (`prover::ghost`): the legacy-pipeline port of the new pipeline's
//! `stage_04_ghost`.
//!
//! Inputs: `Program::ghost_native_seed` — per ghost-writing native, the
//! `(K, V)` marker pairs its `#[spec(target=...)]` spec declares (derived
//! from the Move model by the backend, gated to markers some
//! target-package spec declares). Empty seed = the pass is a no-op and
//! program output is byte-identical (the inertness gate).
//!
//! What it does:
//! 1. Seed `ghost_vars[native]` from the native seed and rename each
//!    seeded native to `<name>__ghost` — the renderer then emits the
//!    hand-written ghost-threading Lean def (e.g.
//!    `Transfer.transfer_impl__ghost` in `lemmas/natives/Sui/`), whose
//!    trailing params/return slots are the threaded markers sorted by
//!    marker struct name.
//! 2. Add direct ghost-op usage: any function whose body calls
//!    `ghost::{global,set,borrow_mut}<K,V>` with a seeded marker threads
//!    that marker. (Ops on unseeded markers are left alone — the
//!    `Ghost.*` abort stubs remain the translation-bug tripwire.)
//! 3. Callee→caller fixpoint over `IRNode::calls()`: a function threads
//!    the union of its callees' markers. This covers value defs, the
//!    translation-time `.aborts` faces, and while/after loop helpers.
//! 4. Signature augmentation: each threaded function gains a trailing
//!    `__ghost_<K-name>` value param per marker. Value-face functions
//!    (everything except `.aborts`/`.requires`/`.ensures`/Prop returns)
//!    also gain trailing return slots (`augmented_return`, mirroring
//!    `mutable_threading`'s shape rules) and have their body tails
//!    wrapped to return the threaded vars.
//! 5. Call-site threading: calls to threaded callees gain the ghost vars
//!    as trailing args; calls to value-face callees additionally
//!    destructure the augmented return into ghost rebinds (which shadow
//!    the caller's own threaded vars — legacy `Let` rebinding gives the
//!    same effect the new pipeline gets from pre-SSA rebinds).
//! 6. Op lowering: `global`/`borrow_mut` reads become the threaded var;
//!    `set` becomes a rebind of it.
//!
//! Runs in `Program::finalize` after mutable threading (its call-site
//! shapes extend the mut-augmented tuples) and before the aborts
//! derivation / spec extraction (which consume the threaded bodies).
//! At that point every call still sits at a `Let`-value or sequencing
//! position (stackless bytecode binds all call results to temps and
//! `optimize_all` has not inlined yet), except the tail calls emitted by
//! the while-loop lowering — handled by the tail walker. A threaded
//! value-face call in any other position is a hard error.

use crate::data::functions::{FunctionID, Parameter};
use crate::data::ir::IRNode;
use crate::data::types::{TempId, Type};
use crate::Program;
use std::collections::BTreeMap;
use std::rc::Rc;

/// Per-callee info the call-site rewriter needs, captured BEFORE any
/// signature was augmented.
#[derive(Debug, Clone)]
struct CalleeInfo {
    /// Value-face callees return the augmented tuple; spec faces keep
    /// their return type (params only).
    value_face: bool,
    /// The callee's pre-augmentation return type was unit.
    orig_ret_unit: bool,
    /// The threaded ghost var names, in marker order.
    ghost_names: Vec<TempId>,
}

pub fn thread_ghosts(program: &mut Program) {
    let seed = std::mem::take(&mut program.ghost_native_seed);
    if seed.is_empty() {
        return;
    }

    // The universe of seeded markers (dedup'd), and per-function sets.
    let mut all_markers: Vec<(Type, Type)> = Vec::new();
    let mut ghost_vars: BTreeMap<FunctionID, Vec<(Type, Type)>> = BTreeMap::new();
    for (fid, markers) in &seed {
        let mut set = markers.clone();
        sort_markers(program, &mut set);
        for kv in &set {
            if !all_markers.contains(kv) {
                all_markers.push(kv.clone());
            }
        }
        ghost_vars.insert(*fid, set);
    }

    let op_fids = resolve_ghost_op_fids(program);

    // Step 2: direct ghost-op usage on seeded markers.
    let fn_ids: Vec<FunctionID> = program.functions.iter_ids().collect();
    for fid in &fn_ids {
        let func = program.functions.get(fid);
        if func.is_native {
            continue;
        }
        let mut used: Vec<(Type, Type)> = Vec::new();
        for n in func.body.iter() {
            if let IRNode::Call {
                function,
                type_args,
                ..
            } = n
            {
                if (op_fids.read.contains(function) || op_fids.set.contains(function))
                    && type_args.len() == 2
                {
                    let kv = (type_args[0].clone(), type_args[1].clone());
                    if all_markers.contains(&kv) && !used.contains(&kv) {
                        used.push(kv);
                    }
                }
            }
        }
        if !used.is_empty() {
            let entry = ghost_vars.entry(*fid).or_default();
            for kv in used {
                if !entry.contains(&kv) {
                    entry.push(kv);
                }
            }
            let mut set = std::mem::take(entry);
            sort_markers(program, &mut set);
            *ghost_vars.get_mut(fid).unwrap() = set;
        }
    }

    // Step 3: callee→caller fixpoint over the call graph.
    loop {
        let mut changed = false;
        for fid in &fn_ids {
            let func = program.functions.get(fid);
            if func.is_native {
                continue;
            }
            let mut additions: Vec<(Type, Type)> = Vec::new();
            for callee in func.body.calls() {
                if let Some(cset) = ghost_vars.get(&callee) {
                    for kv in cset {
                        if !additions.contains(kv) {
                            additions.push(kv.clone());
                        }
                    }
                }
            }
            if additions.is_empty() {
                continue;
            }
            let entry = ghost_vars.entry(*fid).or_default();
            let mut grew = false;
            for kv in additions {
                if !entry.contains(&kv) {
                    entry.push(kv);
                    grew = true;
                }
            }
            if grew {
                let mut set = std::mem::take(entry);
                sort_markers(program, &mut set);
                *ghost_vars.get_mut(fid).unwrap() = set;
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }

    // Capture per-callee info before augmenting any signature.
    let mut callee_info: BTreeMap<FunctionID, CalleeInfo> = BTreeMap::new();
    for (fid, markers) in &ghost_vars {
        let func = program.functions.get(fid);
        callee_info.insert(
            *fid,
            CalleeInfo {
                value_face: is_value_face(&func.name, &func.signature.return_type),
                orig_ret_unit: matches!(&func.signature.return_type, Type::Tuple(v) if v.is_empty()),
                ghost_names: markers.iter().map(|(k, _)| var_name(program, k)).collect(),
            },
        );
    }

    // Step 4: signature augmentation (+ native rename).
    for (fid, markers) in &ghost_vars {
        let names: Vec<TempId> = markers.iter().map(|(k, _)| var_name(program, k)).collect();
        let value_types: Vec<Type> = markers.iter().map(|(_, v)| v.clone()).collect();
        let is_seeded_native = seed.contains_key(fid);
        let func = program.functions.get_mut(*fid);
        for (name, ty) in names.iter().zip(value_types.iter()) {
            func.signature.parameters.push(Parameter {
                name: name.to_string(),
                param_type: ty.clone(),
                ssa_value: name.clone(),
            });
        }
        let info = &callee_info[fid];
        if info.value_face {
            func.signature.return_type =
                augmented_return(&func.signature.return_type, &value_types);
        }
        if is_seeded_native {
            assert!(
                func.is_native,
                "ghost seed entry {} is not a native function",
                func.name
            );
            func.name = format!("{}__ghost", func.name);
        }
    }

    // Steps 5 + 6: rewrite each threaded, non-native function's body.
    for (fid, markers) in &ghost_vars {
        if program.functions.get(fid).is_native {
            continue;
        }
        let my_names: Vec<TempId> = markers.iter().map(|(k, _)| var_name(program, k)).collect();
        let my_face_is_value = callee_info[fid].value_face;
        let my_ret_unit = callee_info[fid].orig_ret_unit;
        let fn_name = program.functions.get(fid).name.clone();
        let body = std::mem::take(&mut program.functions.get_mut(*fid).body);

        // Phase A (value-face only): tail positions — pass-through /
        // destructure tail calls, then wrap terminals to return the
        // threaded vars.
        let body = if my_face_is_value {
            wrap_tails(body, &my_names, my_ret_unit, &callee_info, true)
        } else {
            body
        };

        // Phase B: remaining call sites (Let-value / sequencing).
        let mut body =
            body.map_top_down(&mut |node| rewrite_call_node(node, &callee_info, &fn_name));

        // Phase C: op lowering onto the threaded vars.
        let my_set: Vec<(Type, Type)> = markers.clone();
        body = body.map_top_down(&mut |node| lower_ghost_ops(node, &op_fids, &my_set, program));

        program.functions.get_mut(*fid).body = body;
    }

    program.ghost_vars = ghost_vars;
}

/// Deterministic threading order: sort markers by the marker struct's
/// name (ties broken by struct id — two distinct marker structs sharing
/// a name would otherwise collide on the threaded var name, so panic).
fn sort_markers(program: &Program, set: &mut [(Type, Type)]) {
    set.sort_by_key(|(k, _)| marker_sort_key(program, k));
    for w in set.windows(2) {
        let (a, b) = (&w[0].0, &w[1].0);
        assert!(
            marker_sort_key(program, a).0 != marker_sort_key(program, b).0
                || marker_sort_key(program, a).1 == marker_sort_key(program, b).1,
            "two distinct ghost marker structs share the name {}",
            marker_sort_key(program, a).0
        );
    }
}

fn marker_sort_key(program: &Program, k: &Type) -> (String, usize) {
    match k {
        Type::Struct { struct_id, .. } => (program.structs.get(struct_id).name.clone(), *struct_id),
        other => panic!("ghost marker K must be a struct type, got {:?}", other),
    }
}

/// The threaded-variable name for marker `K`: `__ghost_<StructName>`.
fn var_name(program: &Program, k: &Type) -> TempId {
    match k {
        Type::Struct { struct_id, .. } => {
            Rc::from(format!("__ghost_{}", program.structs.get(struct_id).name).as_str())
        }
        other => panic!("ghost marker K must be a struct type, got {:?}", other),
    }
}

fn is_value_face(name: &str, return_type: &Type) -> bool {
    !(name.contains(".aborts")
        || name.contains(".requires")
        || name.contains(".ensures")
        || *return_type == Type::Prop)
}

/// Mirror `mutable_threading::augmented_return`: unit + one slot → the
/// slot itself; unit + n → tuple of slots; otherwise `(orig, slots...)`.
fn augmented_return(original: &Type, ghost_types: &[Type]) -> Type {
    let is_unit = matches!(original, Type::Tuple(v) if v.is_empty());
    if is_unit && ghost_types.len() == 1 {
        ghost_types[0].clone()
    } else if is_unit {
        Type::Tuple(ghost_types.to_vec())
    } else {
        let mut v = vec![original.clone()];
        v.extend_from_slice(ghost_types);
        Type::Tuple(v)
    }
}

/// The expression a value-face function's tail returns for its ghost
/// slots alone (unit original return).
fn ghost_value(names: &[TempId]) -> IRNode {
    if names.len() == 1 {
        IRNode::Var(names[0].clone())
    } else {
        IRNode::Tuple(names.iter().map(|n| IRNode::Var(n.clone())).collect())
    }
}

struct GhostOpFids {
    read: Vec<FunctionID>,
    set: Vec<FunctionID>,
}

fn resolve_ghost_op_fids(program: &Program) -> GhostOpFids {
    let mut read = Vec::new();
    let mut set = Vec::new();
    for (fid, func) in program.functions.iter() {
        let module = program.modules.get(&func.module_id);
        if module.name != "ghost" {
            continue;
        }
        match func.name.as_str() {
            "global" | "borrow_mut" => read.push(fid),
            "set" => set.push(fid),
            _ => {}
        }
    }
    GhostOpFids { read, set }
}

/// True when the call's trailing args are already the ghost vars —
/// the idempotence guard for `map_top_down` revisits.
fn args_already_threaded(args: &[IRNode], names: &[TempId]) -> bool {
    if names.is_empty() || args.len() < names.len() {
        return false;
    }
    args[args.len() - names.len()..]
        .iter()
        .zip(names)
        .all(|(a, n)| matches!(a, IRNode::Var(v) if v == n))
}

fn extend_args(args: &mut Vec<IRNode>, names: &[TempId]) {
    for n in names {
        args.push(IRNode::Var(n.clone()));
    }
}

/// Phase B rewriter, applied top-down. Handles `Let`-value and
/// sequencing positions; a threaded value-face call anywhere else (all
/// tails were already handled by Phase A) is a hard error.
fn rewrite_call_node(
    node: IRNode,
    info: &BTreeMap<FunctionID, CalleeInfo>,
    caller_name: &str,
) -> IRNode {
    match node {
        IRNode::Let {
            pattern,
            value,
            body,
        } => {
            if let IRNode::Call {
                function,
                type_args,
                args,
            } = *value
            {
                if let Some(ci) = info.get(&function) {
                    if args_already_threaded(&args, &ci.ghost_names) {
                        return IRNode::Let {
                            pattern,
                            value: Box::new(IRNode::Call {
                                function,
                                type_args,
                                args,
                            }),
                            body,
                        };
                    }
                    let mut new_args = args;
                    extend_args(&mut new_args, &ci.ghost_names);
                    let call = IRNode::Call {
                        function,
                        type_args,
                        args: new_args,
                    };
                    if !ci.value_face {
                        // Spec-face callee: return type unchanged.
                        return IRNode::Let {
                            pattern,
                            value: Box::new(call),
                            body,
                        };
                    }
                    return build_destructure(pattern, call, *body, ci);
                }
                return IRNode::Let {
                    pattern,
                    value: Box::new(IRNode::Call {
                        function,
                        type_args,
                        args,
                    }),
                    body,
                };
            }
            IRNode::Let {
                pattern,
                value,
                body,
            }
        }
        IRNode::Call {
            function,
            type_args,
            args,
        } => {
            if let Some(ci) = info.get(&function) {
                if !args_already_threaded(&args, &ci.ghost_names) {
                    if ci.value_face {
                        panic!(
                            "ghost_threading: threaded value-face call (callee fid {}) at an \
                             unsupported position in {} — expected all such calls at Let-value, \
                             sequencing, or tail positions",
                            function, caller_name
                        );
                    }
                    let mut new_args = args;
                    extend_args(&mut new_args, &ci.ghost_names);
                    return IRNode::Call {
                        function,
                        type_args,
                        args: new_args,
                    };
                }
            }
            IRNode::Call {
                function,
                type_args,
                args,
            }
        }
        other => other,
    }
}

/// Build the destructuring `Let` for a threaded value-face call at a
/// `Let`-value position.
fn build_destructure(pattern: Vec<TempId>, call: IRNode, body: IRNode, ci: &CalleeInfo) -> IRNode {
    let ghost_pat: Vec<TempId> = ci.ghost_names.clone();
    if ci.orig_ret_unit {
        // Augmented return is the ghost value(s) alone; the original
        // pattern ([] or [_]) bound nothing meaningful.
        return IRNode::Let {
            pattern: ghost_pat,
            value: Box::new(call),
            body: Box::new(body),
        };
    }
    if pattern.len() <= 1 {
        let mut pat = if pattern.is_empty() {
            vec![Rc::from("_") as TempId]
        } else {
            pattern
        };
        pat.extend(ghost_pat);
        return IRNode::Let {
            pattern: pat,
            value: Box::new(call),
            body: Box::new(body),
        };
    }
    // Multi-element original pattern: bind the original (tuple) return
    // as one component, then destructure it — mirroring
    // `mutable_threading::fix_call_sites`'s `__orig_ret` indirection.
    let orig_temp: TempId = Rc::from("__ghost_orig_ret");
    let mut pat = vec![orig_temp.clone()];
    pat.extend(ghost_pat);
    IRNode::Let {
        pattern: pat,
        value: Box::new(call),
        body: Box::new(IRNode::Let {
            pattern,
            value: Box::new(IRNode::Var(orig_temp)),
            body: Box::new(body),
        }),
    }
}

/// Phase A: walk the body spine of a value-face function, handling tail
/// calls to threaded callees and wrapping every terminal to return the
/// threaded ghost vars.
fn wrap_tails(
    node: IRNode,
    my_names: &[TempId],
    my_ret_unit: bool,
    info: &BTreeMap<FunctionID, CalleeInfo>,
    tail: bool,
) -> IRNode {
    match node {
        IRNode::Let {
            pattern,
            value,
            body,
        } => IRNode::Let {
            pattern,
            value,
            body: Box::new(wrap_tails(*body, my_names, my_ret_unit, info, tail)),
        },
        IRNode::If {
            cond,
            then_branch,
            else_branch,
        } if tail => IRNode::If {
            cond,
            then_branch: Box::new(wrap_tails(*then_branch, my_names, my_ret_unit, info, true)),
            else_branch: Box::new(wrap_tails(*else_branch, my_names, my_ret_unit, info, true)),
        },
        IRNode::Match { scrutinee, cases } if tail => IRNode::Match {
            scrutinee,
            cases: cases
                .into_iter()
                .map(|(tag, bindings, body)| {
                    (
                        tag,
                        bindings,
                        wrap_tails(body, my_names, my_ret_unit, info, true),
                    )
                })
                .collect(),
        },
        IRNode::MatchOption {
            scrutinee,
            binding,
            some_branch,
            none_branch,
        } if tail => IRNode::MatchOption {
            scrutinee,
            binding,
            some_branch: Box::new(wrap_tails(*some_branch, my_names, my_ret_unit, info, true)),
            none_branch: Box::new(wrap_tails(*none_branch, my_names, my_ret_unit, info, true)),
        },
        other if tail => wrap_terminal(other, my_names, my_ret_unit, info),
        other => other,
    }
}

fn wrap_terminal(
    node: IRNode,
    my_names: &[TempId],
    my_ret_unit: bool,
    info: &BTreeMap<FunctionID, CalleeInfo>,
) -> IRNode {
    // Abort tails never return normally; `sorry` inhabits the augmented
    // tuple (same rule as mutable_threading).
    if matches!(node, IRNode::Abort { .. }) {
        return node;
    }
    // Tail call to a threaded value-face callee.
    if let IRNode::Call {
        function,
        type_args,
        args,
    } = node
    {
        if let Some(ci) = info.get(&function) {
            assert!(
                ci.value_face,
                "ghost_threading: spec-face callee (fid {}) in a value-face tail position",
                function
            );
            let mut new_args = args;
            if !args_already_threaded(&new_args, &ci.ghost_names) {
                extend_args(&mut new_args, &ci.ghost_names);
            }
            let call = IRNode::Call {
                function,
                type_args,
                args: new_args,
            };
            if ci.ghost_names == my_names && ci.orig_ret_unit == my_ret_unit {
                // Pass-through: the callee already returns the caller's
                // augmented shape (tail calls are type-preserving).
                return call;
            }
            // Ghost sets differ (caller ⊇ callee): destructure and
            // re-tuple with the caller's full set.
            if ci.orig_ret_unit {
                let inner = build_my_tail(None, my_names, my_ret_unit);
                return IRNode::Let {
                    pattern: ci.ghost_names.clone(),
                    value: Box::new(call),
                    body: Box::new(inner),
                };
            }
            let r: TempId = Rc::from("__ghost_tail_ret");
            let mut pat = vec![r.clone()];
            pat.extend(ci.ghost_names.clone());
            let inner = build_my_tail(Some(IRNode::Var(r)), my_names, my_ret_unit);
            return IRNode::Let {
                pattern: pat,
                value: Box::new(call),
                body: Box::new(inner),
            };
        }
        return build_my_tail(
            Some(IRNode::Call {
                function,
                type_args,
                args,
            }),
            my_names,
            my_ret_unit,
        );
    }
    // Plain terminal expression.
    if my_ret_unit {
        if matches!(&node, IRNode::Tuple(v) if v.is_empty()) {
            return ghost_value(my_names);
        }
        // Preserve the (unit-typed) terminal's evaluation for form's sake.
        return IRNode::Let {
            pattern: vec![],
            value: Box::new(node),
            body: Box::new(ghost_value(my_names)),
        };
    }
    build_my_tail(Some(node), my_names, my_ret_unit)
}

/// The caller's augmented tail value: `(orig, ghosts...)`, or the ghost
/// value(s) alone for a unit original return.
fn build_my_tail(orig: Option<IRNode>, my_names: &[TempId], my_ret_unit: bool) -> IRNode {
    match orig {
        Some(e) if !my_ret_unit => {
            let mut items = vec![e];
            items.extend(my_names.iter().map(|n| IRNode::Var(n.clone())));
            IRNode::Tuple(items)
        }
        Some(e) => IRNode::Let {
            pattern: vec![],
            value: Box::new(e),
            body: Box::new(ghost_value(my_names)),
        },
        None => ghost_value(my_names),
    }
}

/// Phase C rewriter (top-down): lower ghost ops on THIS function's
/// threaded markers. Reads (`global`/`borrow_mut`) become the threaded
/// var; `set` becomes a rebind. Ops on markers this function does not
/// thread are left as the `Ghost.*` render stubs (translation-bug
/// tripwire).
fn lower_ghost_ops(
    node: IRNode,
    op_fids: &GhostOpFids,
    my_set: &[(Type, Type)],
    program: &Program,
) -> IRNode {
    let marker_of = |type_args: &[Type]| -> Option<TempId> {
        if type_args.len() != 2 {
            return None;
        }
        let kv = (type_args[0].clone(), type_args[1].clone());
        my_set
            .iter()
            .any(|m| *m == kv)
            .then(|| var_name(program, &kv.0))
    };
    match node {
        // set<K,V>(e) at a binding/sequencing position → rebind the var.
        IRNode::Let {
            pattern,
            value,
            body,
        } => {
            if let IRNode::Call {
                function,
                type_args,
                args,
            } = &*value
            {
                if op_fids.set.contains(function) {
                    if let Some(name) = marker_of(type_args) {
                        assert!(
                            pattern.is_empty() || pattern.iter().all(|p| &**p == "_"),
                            "ghost::set result must not be bound"
                        );
                        let arg = args
                            .first()
                            .cloned()
                            .expect("ghost::set must have a value argument");
                        let arg = match arg {
                            IRNode::ReadRef(inner) => *inner,
                            other => other,
                        };
                        return IRNode::Let {
                            pattern: vec![name],
                            value: Box::new(arg),
                            body,
                        };
                    }
                }
            }
            IRNode::Let {
                pattern,
                value,
                body,
            }
        }
        // global<K,V>() / borrow_mut<K,V>() anywhere → the threaded var.
        IRNode::Call {
            function,
            type_args,
            args,
        } => {
            if op_fids.read.contains(&function) {
                if let Some(name) = marker_of(&type_args) {
                    return IRNode::Var(name);
                }
            }
            IRNode::Call {
                function,
                type_args,
                args,
            }
        }
        // ReadRef around a ghost read (global returns &V upstream):
        // handled naturally — the inner Call is rewritten to a Var by the
        // top-down revisit and the ReadRef of a plain var is stripped by
        // later cleanup; nothing to do here.
        other => other,
    }
}
