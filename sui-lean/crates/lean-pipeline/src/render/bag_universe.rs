//! Per-project closed-universe `BagU` emission for bag / object_bag
//! key & value types.
//!
//! `BagU` is a SEPARATE, self-contained universe from `TyCode` (the df
//! universe). It is parallel to `dyn_type_universe.rs`'s `TyCode`
//! emission in shape (self-referential leaves + wrappings, interp,
//! Universe + HasCode instances, all `rfl`), but scoped to ONLY the
//! types that flow through `Sui::bag::*` / `Sui::object_bag::*` call
//! sites as keys / values.
//!
//! Why a separate universe: a struct that CONTAINS a `Bag` field (e.g.
//! current-lending `protocol::referral::Referral`) must itself be a
//! `TyCode` (df) value so it can be stored through a dynamic field. If
//! its `Bag` field were `Bag.Bag TyCode` (same universe), the struct's
//! `_Types.lean` would need `[Universe TyCode]` -> import
//! `TyCodeInterp` -> cycle (`TyCodeInterp` already imports that
//! `_Types` to interpret the struct as a df value). Typing the field
//! over `BagU` instead breaks the cycle: `Referral_Types` imports
//! `BagUInterp`, and `BagU` -- which EXCLUDES bag-containing structs --
//! never imports `Referral_Types` back. The graph is a DAG.
//!
//! See `plans/lean-pipeline/split-bag-df-universes.md`.

use std::collections::{BTreeSet, HashSet};
use std::fs;
use std::io;
use std::path::Path;

use crate::ir::expr::{Block, BlockTail, Expr, Stmt};
use crate::ir::{Program, Type};

use super::dyn_type_universe::{
    classify, collect_bag_containing_struct_ids, collect_struct_modules,
    inherit_spec_companion_typeparam_deps, leaf_fqn, lean_str, mangle, struct_base_fqn,
    wrapping_ctor_name, DynTypeUniverse, WrappingStruct,
};
use super::escape;
use super::ty;

/// True iff `fid` resolves to a `Sui::bag::*` or `Sui::object_bag::*`
/// function (translated or native). Bag K/V types are harvested from
/// the type arguments of these call sites.
fn is_bag_op_call(program: &Program, fid: usize) -> bool {
    let Some(callee) = program.lookup_callee(fid) else {
        return false;
    };
    let Some(m) = program.modules.get(&callee.module()) else {
        return false;
    };
    m.package_name == "Sui" && matches!(m.name.as_str(), "bag" | "object_bag")
}

/// True iff `ty` (after stripping refs) is `bag::Bag` / `object_bag::ObjectBag`.
fn is_bag_struct_type(ty: &Type, program: &Program) -> bool {
    let sid = match ty {
        Type::Struct { struct_id, .. } => *struct_id,
        Type::Reference(inner) => return is_bag_struct_type(inner, program),
        Type::MutableRef { inner, .. } => return is_bag_struct_type(inner, program),
        _ => return false,
    };
    program.structs.get(&sid).map_or(false, |s| {
        s.qualified_name == "bag::Bag" || s.qualified_name == "object_bag::ObjectBag"
    })
}

/// Collect single-variable `let` bindings (recursively, across nested
/// blocks) into `map`, so a `BorrowMapKey` base that is a `Var` can be
/// chased to its defining expression.
fn build_var_def<'a>(
    block: &'a Block,
    map: &mut std::collections::HashMap<crate::ir::VarId, &'a Expr>,
) {
    for stmt in &block.stmts {
        if let Stmt::Let { pattern, value } = stmt {
            // A single-variable let, or the FIRST variable of a tuple let
            // bound to a call: an accessor returning `&mut ObjectBag` is
            // destructured into (borrowed bag, updated parent).
            if pattern.len() == 1 || matches!(value, Expr::Call { .. }) {
                if let Some(Some(v)) = pattern.first() {
                    map.insert(v.clone(), value);
                }
            }
            build_var_def_expr(value, map);
        } else if let Stmt::Eval(e) = stmt {
            build_var_def_expr(e, map);
        }
    }
    match &block.tail {
        BlockTail::Value(e) => build_var_def_expr(e, map),
        BlockTail::Break { value, .. } => build_var_def_expr(value, map),
        BlockTail::Continue { value, .. } => build_var_def_expr(value, map),
        BlockTail::Return(e) => build_var_def_expr(e, map),
        BlockTail::ReturnFromBlock { value, .. } => build_var_def_expr(value, map),
        BlockTail::Abort { code } => build_var_def_expr(code, map),
    }
}

fn build_var_def_expr<'a>(
    e: &'a Expr,
    map: &mut std::collections::HashMap<crate::ir::VarId, &'a Expr>,
) {
    match e {
        Expr::If {
            then_branch,
            else_branch,
            ..
        } => {
            build_var_def(then_branch, map);
            build_var_def(else_branch, map);
        }
        Expr::Match { cases, .. } => {
            for c in cases {
                build_var_def(&c.body, map);
            }
        }
        Expr::While { header, body, .. } => {
            build_var_def(header, map);
            build_var_def(body, map);
        }
        Expr::Quantifier { body, .. } => build_var_def(body, map),
        _ => {}
    }
}

/// True iff `e` (a `PathStep::MapKey` borrow base) evaluates to a `Bag` / `ObjectBag`
/// value. The bag op `bag::borrow_mut` is lowered to a `Borrow` with a
/// `PathStep::MapKey`; its base is a field `Borrow` (or a `Var` chained to one) on a `Bag`
/// field, so chase `Var`s through `var_def` and inspect field types.
/// Used so `BagU` collection + taint catch transformed bag borrows that
/// are no longer direct `bag::*` calls at render time.
fn expr_yields_bag(
    e: &Expr,
    var_def: &std::collections::HashMap<crate::ir::VarId, &Expr>,
    program: &Program,
    depth: usize,
) -> bool {
    if depth > 64 {
        return false;
    }
    match e {
        Expr::Field {
            struct_id,
            field_index,
            ..
        } => program
            .structs
            .get(struct_id)
            .and_then(|s| s.fields.get(*field_index))
            .map_or(false, |f| is_bag_struct_type(&f.field_type, program)),
        Expr::Var(v) | Expr::BorrowLoc(v) => var_def
            .get(v)
            .map_or(false, |d| expr_yields_bag(d, var_def, program, depth + 1)),
        Expr::ReadRef(inner) => expr_yields_bag(inner, var_def, program, depth + 1),
        // An accessor call returning the bag (`proposals.active_mut()`), or a
        // tuple whose first element is the bag reference.
        Expr::Call { fun, .. } => program
            .lookup_callee(*fun)
            .map_or(false, |callee| match &callee.signature().return_type {
                Type::Tuple(elements) => elements
                    .first()
                    .map_or(false, |first| is_bag_struct_type(first, program)),
                other => is_bag_struct_type(other, program),
            }),
        // A df borrow whose value type IS a `Bag` / `ObjectBag` (ember's
        // `df<b"supported_assets", Bag>`): the borrowed value is the bag
        // itself, so a subsequent `bag::borrow_mut` on it is a bag op.
        // The bag is fetched from `World` via `store_bag_borrow` (the
        // `df_value`), but the BorrowMapKey's `value_type` already names
        // it as a Bag.
        Expr::Borrow {
            step: crate::ir::path::PathStep::MapKey { value_type, .. },
            ..
        } => is_bag_struct_type(value_type, program),
        Expr::Borrow {
            step:
                crate::ir::path::PathStep::Field {
                    struct_id,
                    field_index,
                },
            ..
        } => program
            .structs
            .get(struct_id)
            .and_then(|s| s.fields.get(*field_index))
            .map_or(false, |f| is_bag_struct_type(&f.field_type, program)),
        Expr::Borrow {
            step:
                crate::ir::path::PathStep::VariantField {
                    struct_id,
                    variant,
                    field_index,
                },
            ..
        } => program
            .structs
            .get(struct_id)
            .and_then(|structure| structure.variant_by_tag(*variant))
            .and_then(|variant| variant.fields.get(*field_index))
            .map_or(false, |field| {
                is_bag_struct_type(&field.field_type, program)
            }),
        _ => false,
    }
}

/// Collect the `BagU` universe: classify the type arguments of every
/// `bag::*` / `object_bag::*` call, then drop bag-containing structs
/// and the `Bag` / `ObjectBag` containers themselves (a bag whose
/// value is itself a bag stays unsupported -- the only residual cycle).
pub fn collect(program: &Program) -> DynTypeUniverse {
    let deps = compute_bagu_typeparam_deps(program);
    let bag_containing = collect_bag_containing_struct_ids(program);
    collect_with_analyses(program, &deps, &bag_containing)
}

pub(crate) fn collect_in(context: &super::context::RenderContext<'_>) -> DynTypeUniverse {
    collect_with_analyses(
        context.program,
        context.bagu_typeparam_deps(),
        context.bag_containing_structs(),
    )
}

fn collect_with_analyses(
    program: &Program,
    deps: &std::collections::HashMap<crate::ir::FunId, Vec<bool>>,
    bag_containing: &std::collections::HashSet<crate::ir::StructId>,
) -> DynTypeUniverse {
    let mut leaves: HashSet<Type> = HashSet::new();
    let mut wrappings: BTreeSet<WrappingStruct> = BTreeSet::new();
    // Per-typeparam bag taint, so call sites passing a CONCRETE type at a
    // bag-tainted callee param harvest that concrete type into BagU (the
    // callee flows it into a bag value -> it needs a BagU HasCode leaf).
    for (_, f) in program.functions.iter() {
        let mut var_def: std::collections::HashMap<crate::ir::VarId, &Expr> =
            std::collections::HashMap::new();
        build_var_def(&f.body, &mut var_def);
        walk_block_bag(
            &f.body,
            program,
            &var_def,
            deps,
            &mut leaves,
            &mut wrappings,
        );
    }

    // BagU MUST NOT contain bag-containing structs, nor Bag/ObjectBag
    // themselves -- otherwise the DAG argument collapses (BagUInterp
    // would import a bag-containing `_Types`, which imports BagUInterp).
    let is_container = |sid: &crate::ir::StructId| -> bool {
        program.structs.get(sid).map_or(false, |s| {
            s.qualified_name == "bag::Bag" || s.qualified_name == "object_bag::ObjectBag"
        })
    };
    wrappings.retain(|w| !bag_containing.contains(&w.struct_id) && !is_container(&w.struct_id));
    leaves.retain(|t| match t {
        Type::Struct { struct_id, .. } => {
            !bag_containing.contains(struct_id) && !is_container(struct_id)
        }
        _ => true,
    });

    let mut leaf_vec: Vec<Type> = leaves.into_iter().collect();
    leaf_vec.sort_by(|a, b| mangle(a, program).cmp(&mangle(b, program)));
    DynTypeUniverse {
        leaves: leaf_vec,
        wrappings: wrappings.into_iter().collect(),
    }
}

fn walk_block_bag(
    block: &Block,
    program: &Program,
    var_def: &std::collections::HashMap<crate::ir::VarId, &Expr>,
    deps: &std::collections::HashMap<crate::ir::FunId, Vec<bool>>,
    leaves: &mut HashSet<Type>,
    wrappings: &mut BTreeSet<WrappingStruct>,
) {
    for stmt in &block.stmts {
        match stmt {
            Stmt::Let { value, .. } => {
                walk_expr_bag(value, program, var_def, deps, leaves, wrappings)
            }
            Stmt::Eval(e) => walk_expr_bag(e, program, var_def, deps, leaves, wrappings),
        }
    }
    match &block.tail {
        BlockTail::Value(e) => walk_expr_bag(e, program, var_def, deps, leaves, wrappings),
        BlockTail::Break { value, .. } => {
            walk_expr_bag(value, program, var_def, deps, leaves, wrappings)
        }
        BlockTail::Continue { value, .. } => {
            walk_expr_bag(value, program, var_def, deps, leaves, wrappings)
        }
        BlockTail::Return(e) => walk_expr_bag(e, program, var_def, deps, leaves, wrappings),
        BlockTail::ReturnFromBlock { value, .. } => {
            walk_expr_bag(value, program, var_def, deps, leaves, wrappings)
        }
        BlockTail::Abort { code } => walk_expr_bag(code, program, var_def, deps, leaves, wrappings),
    }
}

fn walk_expr_bag(
    expr: &Expr,
    program: &Program,
    var_def: &std::collections::HashMap<crate::ir::VarId, &Expr>,
    deps: &std::collections::HashMap<crate::ir::FunId, Vec<bool>>,
    leaves: &mut HashSet<Type>,
    wrappings: &mut BTreeSet<WrappingStruct>,
) {
    match expr {
        Expr::Borrow { step, base } => {
            // Transformed `bag::borrow_mut`: a Bag base means the MapKey
            // step's value_type is a bag VALUE type -> classify into BagU.
            // Table / VecMap / df borrows are skipped (their values are
            // NOT bag members).
            if let crate::ir::path::PathStep::MapKey { value_type, .. } = step {
                if expr_yields_bag(base, var_def, program, 0) {
                    classify(value_type, program, leaves, wrappings);
                }
            }
            for __pe in step.exprs() {
                walk_expr_bag(__pe, program, var_def, deps, leaves, wrappings);
            }
            walk_expr_bag(base, program, var_def, deps, leaves, wrappings);
        }
        Expr::Update { step, base, value } => {
            for __pe in step.exprs() {
                walk_expr_bag(__pe, program, var_def, deps, leaves, wrappings);
            }
            walk_expr_bag(base, program, var_def, deps, leaves, wrappings);
            walk_expr_bag(value, program, var_def, deps, leaves, wrappings);
        }
        Expr::Call {
            fun,
            type_args,
            args,
            ..
        } => {
            if is_bag_op_call(program, *fun) {
                for t in type_args {
                    classify(t, program, leaves, wrappings);
                }
            } else if let Some(callee_taint) = deps.get(fun) {
                // Concrete types passed at a bag-tainted callee param
                // flow into a bag value -> they must be BagU members.
                for (k, &is_tainted) in callee_taint.iter().enumerate() {
                    if is_tainted {
                        if let Some(t) = type_args.get(k) {
                            classify(t, program, leaves, wrappings);
                        }
                    }
                }
            }
            for a in args {
                walk_expr_bag(a, program, var_def, deps, leaves, wrappings);
            }
        }
        Expr::Tuple(es) | Expr::Pack { fields: es, .. } => {
            for x in es {
                walk_expr_bag(x, program, var_def, deps, leaves, wrappings);
            }
        }
        Expr::Unpack { value, .. }
        | Expr::Field { base: value, .. }
        | Expr::ReadRef(value)
        | Expr::ToProp(value)
        | Expr::ToBool(value) => walk_expr_bag(value, program, var_def, deps, leaves, wrappings),
        Expr::WriteRef { reference, value } => {
            walk_expr_bag(reference, program, var_def, deps, leaves, wrappings);
            walk_expr_bag(value, program, var_def, deps, leaves, wrappings);
        }
        Expr::BinOp { lhs, rhs, .. } => {
            walk_expr_bag(lhs, program, var_def, deps, leaves, wrappings);
            walk_expr_bag(rhs, program, var_def, deps, leaves, wrappings);
        }
        Expr::UnOp { operand, .. } => {
            walk_expr_bag(operand, program, var_def, deps, leaves, wrappings)
        }
        Expr::If {
            cond,
            then_branch,
            else_branch,
        } => {
            walk_expr_bag(cond, program, var_def, deps, leaves, wrappings);
            walk_block_bag(then_branch, program, var_def, deps, leaves, wrappings);
            walk_block_bag(else_branch, program, var_def, deps, leaves, wrappings);
        }
        Expr::Match {
            selector, cases, ..
        } => {
            walk_expr_bag(selector, program, var_def, deps, leaves, wrappings);
            for c in cases {
                walk_block_bag(&c.body, program, var_def, deps, leaves, wrappings);
            }
        }
        Expr::While {
            header,
            cond,
            body,
            iter_locals,
            header_exit_locals: _,
            live_out: _,
        } => {
            for (_, init) in iter_locals {
                walk_expr_bag(init, program, var_def, deps, leaves, wrappings);
            }
            walk_block_bag(header, program, var_def, deps, leaves, wrappings);
            walk_expr_bag(cond, program, var_def, deps, leaves, wrappings);
            walk_block_bag(body, program, var_def, deps, leaves, wrappings);
        }
        Expr::Quantifier { domain, body, .. } => {
            use crate::ir::quant::QuantDomain;
            match domain {
                QuantDomain::Unbounded => {}
                QuantDomain::Range { start, end } => {
                    walk_expr_bag(start, program, var_def, deps, leaves, wrappings);
                    walk_expr_bag(end, program, var_def, deps, leaves, wrappings);
                }
                QuantDomain::VecRange { vec, start, end } => {
                    walk_expr_bag(vec, program, var_def, deps, leaves, wrappings);
                    walk_expr_bag(start, program, var_def, deps, leaves, wrappings);
                    walk_expr_bag(end, program, var_def, deps, leaves, wrappings);
                }
                QuantDomain::Collection(c) => {
                    walk_expr_bag(c, program, var_def, deps, leaves, wrappings)
                }
            }
            walk_block_bag(body, program, var_def, deps, leaves, wrappings);
        }
        Expr::Var(_)
        | Expr::Const(_)
        | Expr::Unit
        | Expr::BitOp(_)
        | Expr::BorrowLoc(_)
        | Expr::BorrowGlobal(_)
        | Expr::WriteBack { .. }
        | Expr::IsParent { .. } => {}
        Expr::LabeledBlock { .. } => {
            unreachable!("Expr::LabeledBlock should be eliminated by stage 7 helper extraction")
        }
    }
}

// ---------------------------------------------------------------------------
// Per-typeparam BagU taint: which of a function's type params transitively
// flow into a `bag::*` / `object_bag::*` callsite's type arguments. For each
// `(fid, i)` with `result[fid][i] == true`, the renderer emits
// `[HasCode _root_.BagU T_i]` on that type param so Lean can resolve the
// bag op's `[HasCode BagU K/V]` constraint.
//
// UNLIKE the ObjType taint, this recurses into NESTED type params: BagU is
// self-contained (its wrapping interp recurses via `BagU.interp`, never
// `TyCode`), so the wrapping `HasCode BagU (Wrap T0)` derivation needs
// `[HasCode BagU T0]` -- which T0 does NOT carry unconditionally (BagU
// constraints are conditional, only on bag-tainted params).
// ---------------------------------------------------------------------------

fn collect_typeparams_recursive(ty: &Type, local: &mut Vec<bool>) {
    match ty {
        Type::TypeParam(i) => {
            let i = *i as usize;
            if i < local.len() {
                local[i] = true;
            }
        }
        Type::Vector(inner) | Type::Reference(inner) => collect_typeparams_recursive(inner, local),
        Type::MutableRef { inner, root } => {
            collect_typeparams_recursive(inner, local);
            collect_typeparams_recursive(root, local);
        }
        Type::Tuple(ts) => {
            for t in ts {
                collect_typeparams_recursive(t, local);
            }
        }
        Type::Struct { type_args, .. } => {
            for a in type_args {
                collect_typeparams_recursive(a, local);
            }
        }
        _ => {}
    }
}

pub fn compute_bagu_typeparam_deps(
    program: &Program,
) -> std::collections::HashMap<crate::ir::FunId, Vec<bool>> {
    let mut deps: std::collections::HashMap<crate::ir::FunId, Vec<bool>> =
        std::collections::HashMap::new();
    for (fid, f) in program.functions.iter() {
        deps.insert(*fid, vec![false; f.signature.type_params.len()]);
    }
    loop {
        let mut changed = false;
        let keys: Vec<crate::ir::FunId> = program.functions.keys().copied().collect();
        for fid in keys {
            let f = program.functions.get(&fid).expect("fid present");
            let mut local = deps.get(&fid).cloned().unwrap_or_default();
            let before = local.clone();
            let mut var_def: std::collections::HashMap<crate::ir::VarId, &Expr> =
                std::collections::HashMap::new();
            build_var_def(&f.body, &mut var_def);
            bag_walk_block_taint(&f.body, program, &var_def, &deps, &mut local);
            if before != local {
                deps.insert(fid, local);
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
    inherit_spec_companion_typeparam_deps(program, &mut deps);
    deps
}

fn bag_walk_block_taint(
    block: &Block,
    program: &Program,
    var_def: &std::collections::HashMap<crate::ir::VarId, &Expr>,
    deps: &std::collections::HashMap<crate::ir::FunId, Vec<bool>>,
    local: &mut Vec<bool>,
) {
    for stmt in &block.stmts {
        match stmt {
            Stmt::Let { value, .. } => bag_walk_expr_taint(value, program, var_def, deps, local),
            Stmt::Eval(e) => bag_walk_expr_taint(e, program, var_def, deps, local),
        }
    }
    match &block.tail {
        BlockTail::Value(e) => bag_walk_expr_taint(e, program, var_def, deps, local),
        BlockTail::Break { value, .. } => bag_walk_expr_taint(value, program, var_def, deps, local),
        BlockTail::Continue { value, .. } => {
            bag_walk_expr_taint(value, program, var_def, deps, local)
        }
        BlockTail::Return(e) => bag_walk_expr_taint(e, program, var_def, deps, local),
        BlockTail::ReturnFromBlock { value, .. } => {
            bag_walk_expr_taint(value, program, var_def, deps, local)
        }
        BlockTail::Abort { code } => bag_walk_expr_taint(code, program, var_def, deps, local),
    }
}

fn bag_walk_expr_taint(
    expr: &Expr,
    program: &Program,
    var_def: &std::collections::HashMap<crate::ir::VarId, &Expr>,
    deps: &std::collections::HashMap<crate::ir::FunId, Vec<bool>>,
    local: &mut Vec<bool>,
) {
    match expr {
        Expr::Borrow { step, base } => {
            // Transformed `bag::borrow_mut`: a Bag base means the MapKey
            // step's value_type is a bag value, so its type params need a
            // `[HasCode BagU T]` bound. Skip Table / VecMap / df borrows.
            if let crate::ir::path::PathStep::MapKey { value_type, .. } = step {
                if expr_yields_bag(base, var_def, program, 0) {
                    collect_typeparams_recursive(value_type, local);
                }
            }
            for __pe in step.exprs() {
                bag_walk_expr_taint(__pe, program, var_def, deps, local);
            }
            bag_walk_expr_taint(base, program, var_def, deps, local);
        }
        Expr::Update { step, base, value } => {
            for __pe in step.exprs() {
                bag_walk_expr_taint(__pe, program, var_def, deps, local);
            }
            bag_walk_expr_taint(base, program, var_def, deps, local);
            bag_walk_expr_taint(value, program, var_def, deps, local);
        }
        Expr::Call {
            fun,
            type_args,
            args,
            ..
        } => {
            if is_bag_op_call(program, *fun) {
                for ta in type_args {
                    collect_typeparams_recursive(ta, local);
                }
            } else if let Some(callee_taint) = deps.get(fun) {
                for (k, &is_tainted) in callee_taint.iter().enumerate() {
                    if is_tainted {
                        if let Some(ta) = type_args.get(k) {
                            collect_typeparams_recursive(ta, local);
                        }
                    }
                }
            }
            for a in args {
                bag_walk_expr_taint(a, program, var_def, deps, local);
            }
        }
        Expr::Tuple(es) | Expr::Pack { fields: es, .. } => {
            for x in es {
                bag_walk_expr_taint(x, program, var_def, deps, local);
            }
        }
        Expr::Unpack { value, .. }
        | Expr::Field { base: value, .. }
        | Expr::ReadRef(value)
        | Expr::ToProp(value)
        | Expr::ToBool(value) => bag_walk_expr_taint(value, program, var_def, deps, local),
        Expr::WriteRef { reference, value } => {
            bag_walk_expr_taint(reference, program, var_def, deps, local);
            bag_walk_expr_taint(value, program, var_def, deps, local);
        }
        Expr::BinOp { lhs, rhs, .. } => {
            bag_walk_expr_taint(lhs, program, var_def, deps, local);
            bag_walk_expr_taint(rhs, program, var_def, deps, local);
        }
        Expr::UnOp { operand, .. } => bag_walk_expr_taint(operand, program, var_def, deps, local),
        Expr::If {
            cond,
            then_branch,
            else_branch,
        } => {
            bag_walk_expr_taint(cond, program, var_def, deps, local);
            bag_walk_block_taint(then_branch, program, var_def, deps, local);
            bag_walk_block_taint(else_branch, program, var_def, deps, local);
        }
        Expr::Match {
            selector, cases, ..
        } => {
            bag_walk_expr_taint(selector, program, var_def, deps, local);
            for c in cases {
                bag_walk_block_taint(&c.body, program, var_def, deps, local);
            }
        }
        Expr::While {
            header,
            cond,
            body,
            iter_locals,
            header_exit_locals: _,
            live_out: _,
        } => {
            for (_, init) in iter_locals {
                bag_walk_expr_taint(init, program, var_def, deps, local);
            }
            bag_walk_block_taint(header, program, var_def, deps, local);
            bag_walk_expr_taint(cond, program, var_def, deps, local);
            bag_walk_block_taint(body, program, var_def, deps, local);
        }
        Expr::Quantifier { domain, body, .. } => {
            use crate::ir::quant::QuantDomain;
            match domain {
                QuantDomain::Unbounded => {}
                QuantDomain::Range { start, end } => {
                    bag_walk_expr_taint(start, program, var_def, deps, local);
                    bag_walk_expr_taint(end, program, var_def, deps, local);
                }
                QuantDomain::Collection(c) => bag_walk_expr_taint(c, program, var_def, deps, local),
                QuantDomain::VecRange { vec, start, end } => {
                    bag_walk_expr_taint(vec, program, var_def, deps, local);
                    bag_walk_expr_taint(start, program, var_def, deps, local);
                    bag_walk_expr_taint(end, program, var_def, deps, local);
                }
            }
            bag_walk_block_taint(body, program, var_def, deps, local);
        }
        Expr::Var(_)
        | Expr::Const(_)
        | Expr::Unit
        | Expr::BitOp(_)
        | Expr::BorrowLoc(_)
        | Expr::BorrowGlobal(_)
        | Expr::WriteBack { .. }
        | Expr::IsParent { .. } => {}
        Expr::LabeledBlock { .. } => {
            unreachable!("Expr::LabeledBlock should be eliminated by stage 7 helper extraction")
        }
    }
}

pub fn write_bagu_file(
    universe: &DynTypeUniverse,
    program: &Program,
    output_dir: &Path,
) -> io::Result<()> {
    let gen_dir = output_dir.join("Generated");
    fs::create_dir_all(&gen_dir)?;
    let path = gen_dir.join("BagU.lean");
    let mut out = String::new();
    out.push_str("-- Generated per project by the lean-pipeline renderer.\n");
    out.push_str("-- See `plans/lean-pipeline/split-bag-df-universes.md`.\n");
    out.push_str("--\n");
    out.push_str("-- Bare inductive only. Interp + Universe + HasCode instances\n");
    out.push_str("-- live in Generated/BagUInterp.lean. The bag universe, SEPARATE\n");
    out.push_str("-- from TyCode (the df universe), so bag-containing structs can be\n");
    out.push_str("-- df values without an import cycle.\n\n");
    out.push_str("inductive BagU where\n");
    out.push_str("  | dummy\n");
    for leaf in &universe.leaves {
        out.push_str(&format!("  | {}\n", mangle(leaf, program)));
    }
    for w in &universe.wrappings {
        let stem = wrapping_ctor_name(w, program);
        let args: String = (0..w.arity).map(|i| format!(" (a{} : BagU)", i)).collect();
        out.push_str(&format!("  | {}{}\n", stem, args));
    }
    out.push_str("  deriving DecidableEq, Repr\n");
    fs::write(&path, &out)?;
    Ok(())
}

pub fn write_bagu_interp_file(
    universe: &DynTypeUniverse,
    context: &super::context::RenderContext<'_>,
    output_dir: &Path,
    lemma_libs: &BTreeSet<String>,
) -> io::Result<()> {
    let program = context.program;
    let gen_dir = output_dir.join("Generated");
    fs::create_dir_all(&gen_dir)?;
    let path = gen_dir.join("BagUInterp.lean");

    let mut out = String::new();
    out.push_str("-- Generated per project by the lean-pipeline renderer.\n");
    out.push_str("-- See `plans/lean-pipeline/split-bag-df-universes.md`.\n\n");

    let mut packages: HashSet<(String, String, bool)> = HashSet::new();
    for t in &universe.leaves {
        collect_struct_modules(t, program, lemma_libs, &mut packages);
    }
    for w in &universe.wrappings {
        if let Some(s) = program.structs.get(&w.struct_id) {
            if let Some(m) = program.modules.get(&s.module_id) {
                let pkg = if m.package_name.is_empty() {
                    "NewPipeline".to_string()
                } else {
                    m.package_name.clone()
                };
                let ns = escape::module_name_to_namespace(&m.name);
                let is_lemma = lemma_libs.contains(&pkg);
                packages.insert((pkg, ns, is_lemma));
            }
        }
    }

    out.push_str("import Prelude.BoundedNat\n");
    out.push_str("import Prelude.Universe\n");
    out.push_str("import Generated.BagU\n");
    // BagU members are Bag-FREE (bag values). When a member lives in a
    // module that ALSO defines a Bag-CONTAINING struct, that module is
    // split and the Bag-free member is in `<Mod>_Types_Skeleton`; import
    // the skeleton (the main `_Types` imports BagUInterp, so importing it
    // here would self-cycle). Non-split modules use the regular `_Types`.
    let mut import_lines: Vec<String> = Vec::new();
    for (pkg, ns, is_lemma) in packages.iter() {
        if *is_lemma {
            // A bag-cycle lemma module (e.g. Sui `coin_registry`) is rendered
            // with the user-style Bag-split, so its Bag-free value lives in
            // `_Types_Skeleton`; import that (the main `_Types` imports
            // BagUInterp, which would self-cycle). Obj-taint leaf modules use
            // `_Types`; everything else, the single Full file.
            let mid_opt = program.modules.iter().find_map(|(mid, m)| {
                let m_pkg = if m.package_name.is_empty() {
                    "NewPipeline".to_string()
                } else {
                    m.package_name.clone()
                };
                let m_ns = escape::module_name_to_namespace(&m.name);
                if &m_pkg == pkg && &m_ns == ns {
                    Some(mid)
                } else {
                    None
                }
            });
            if mid_opt.map_or(false, |mid| super::lemma_module_bag_split(context, *mid)) {
                import_lines.push(format!("import {}.{}_Types_Skeleton\n", pkg, ns));
            } else if super::lemma_module_has_types_leaf(context, pkg, ns) {
                import_lines.push(format!("import {}.{}_Types\n", pkg, ns));
            } else {
                import_lines.push(format!("import {}.{}\n", pkg, ns));
            }
        } else {
            let mid_opt = program.modules.iter().find_map(|(mid, m)| {
                let m_pkg = if m.package_name.is_empty() {
                    "NewPipeline".to_string()
                } else {
                    m.package_name.clone()
                };
                let m_ns = escape::module_name_to_namespace(&m.name);
                if &m_pkg == pkg && &m_ns == ns {
                    Some(mid)
                } else {
                    None
                }
            });
            if let Some(mid) = mid_opt {
                if super::dyn_type_universe::module_has_bag_struct(program, *mid) {
                    import_lines.push(format!("import {}.{}_Types_Skeleton\n", pkg, ns));
                } else {
                    import_lines.push(format!("import {}.{}_Types\n", pkg, ns));
                }
            } else {
                import_lines.push(format!("import {}.{}_Types\n", pkg, ns));
            }
        }
    }
    import_lines.sort();
    import_lines.dedup();
    for line in import_lines {
        out.push_str(&line);
    }
    out.push('\n');
    out.push_str("set_option linter.unusedVariables false\n\n");

    out.push_str("abbrev BagU.interp : BagU -> Type\n");
    out.push_str("  | .dummy => Unit\n");
    for leaf in &universe.leaves {
        let stem = mangle(leaf, program);
        let ty_str = ty::type_to_string(leaf, program, None, None);
        out.push_str(&format!("  | .{} => {}\n", stem, ty_str));
    }
    for w in &universe.wrappings {
        let stem = wrapping_ctor_name(w, program);
        let s = program
            .structs
            .get(&w.struct_id)
            .expect("wrapping struct missing");
        let module = program
            .modules
            .get(&s.module_id)
            .expect("struct module missing");
        let namespace = escape::module_render_namespace(&module.package_name, &module.name);
        let struct_path = format!(
            "_root_.{}.{}",
            namespace,
            escape::escape_struct_name(&s.name)
        );
        let pattern_args: String = (0..w.arity).map(|i| format!(" a{}", i)).collect();
        let interp_args: String = (0..w.arity)
            .map(|i| format!(" (BagU.interp a{})", i))
            .collect();
        out.push_str(&format!(
            "  | .{}{} => {}{}\n",
            stem, pattern_args, struct_path, interp_args
        ));
    }
    out.push('\n');

    out.push_str(
        "@[reducible] def BagU.decEqInterp : \u{2200} u : BagU, DecidableEq (BagU.interp u)\n",
    );
    out.push_str("  | .dummy => inferInstance\n");
    for leaf in &universe.leaves {
        let stem = mangle(leaf, program);
        out.push_str(&format!("  | .{} => inferInstance\n", stem));
    }
    for w in &universe.wrappings {
        let stem = wrapping_ctor_name(w, program);
        let pattern_args: String = (0..w.arity).map(|i| format!(" a{}", i)).collect();
        out.push_str(&format!("  | .{}{} =>\n", stem, pattern_args));
        for i in 0..w.arity {
            out.push_str(&format!(
                "    have : DecidableEq (BagU.interp a{0}) := BagU.decEqInterp a{0}\n",
                i
            ));
        }
        out.push_str("    inferInstance\n");
    }
    out.push('\n');

    out.push_str("def BagU.typeName : BagU \u{2192} String\n");
    out.push_str("  | .dummy => \"dummy\"\n");
    for leaf in &universe.leaves {
        let stem = mangle(leaf, program);
        out.push_str(&format!(
            "  | .{} => \"{}\"\n",
            stem,
            lean_str(&leaf_fqn(leaf, program))
        ));
    }
    for w in &universe.wrappings {
        let stem = wrapping_ctor_name(w, program);
        let pat: String = (0..w.arity).map(|i| format!(" a{}", i)).collect();
        let base = lean_str(&struct_base_fqn(w.struct_id, program));
        let args: String = (0..w.arity)
            .map(|i| format!("BagU.typeName a{}", i))
            .collect::<Vec<_>>()
            .join(" ++ \", \" ++ ");
        out.push_str(&format!(
            "  | .{}{} => \"{}<\" ++ {} ++ \">\"\n",
            stem, pat, base, args
        ));
    }
    out.push('\n');

    // `serialize`: real BCS bytes, mirroring `TyCode.serialize` via the
    // shared emitter (same EXACT BYTE FORMAT -- see
    // `dyn_type_universe::serialize_field_expr`). Recursion on a
    // type-param's code goes through `BagU.serialize`. A struct whose
    // value graph is self-recursive stays `[]` (logged).
    out.push_str(
        "def BagU.serialize : (u : BagU) \u{2192} BagU.interp u \u{2192} List (BoundedNat (2^8))\n",
    );
    out.push_str("  | .dummy => fun _ => []\n");
    for leaf in &universe.leaves {
        let stem = mangle(leaf, program);
        out.push_str(&format!(
            "  | .{} => {}\n",
            stem,
            super::dyn_type_universe::bcs_serialize_body_in(
                leaf,
                program,
                "BagU.serialize",
                Some(context),
            )
        ));
    }
    for w in &universe.wrappings {
        let stem = wrapping_ctor_name(w, program);
        let pat: String = (0..w.arity).map(|i| format!(" a{}", i)).collect();
        out.push_str(&format!(
            "  | .{}{} => {}\n",
            stem,
            pat,
            super::dyn_type_universe::bcs_serialize_wrapping_body_in(
                w,
                program,
                "BagU.serialize",
                Some(context),
            )
        ));
    }
    out.push('\n');

    out.push_str("instance : Universe BagU where\n");
    out.push_str("  decEq       := inferInstance\n");
    out.push_str("  interp      := BagU.interp\n");
    out.push_str("  decEqInterp := BagU.decEqInterp\n");
    out.push_str("  typeName    := BagU.typeName\n");
    out.push_str("  serialize   := BagU.serialize\n\n");

    for leaf in &universe.leaves {
        let stem = mangle(leaf, program);
        let ty_str = ty::type_to_string(leaf, program, None, None);
        out.push_str(&format!(
            "instance : HasCode BagU ({}) := \u{27E8}.{}, rfl\u{27E9}\n",
            ty_str, stem
        ));
    }
    for w in &universe.wrappings {
        let stem = wrapping_ctor_name(w, program);
        let s = program
            .structs
            .get(&w.struct_id)
            .expect("wrapping struct missing");
        let module = program
            .modules
            .get(&s.module_id)
            .expect("struct module missing");
        let namespace = escape::module_render_namespace(&module.package_name, &module.name);
        let struct_path = format!(
            "_root_.{}.{}",
            namespace,
            escape::escape_struct_name(&s.name)
        );
        let constraints: String = (0..w.arity)
            .map(|i| format!(" [hc{0} : HasCode BagU T{0}]", i))
            .collect();
        let type_params_intro: String = (0..w.arity)
            .map(|i| format!(" {{T{} : Type}}", i))
            .collect();
        let applied_types: String = (0..w.arity).map(|i| format!(" T{}", i)).collect();
        let ctor_args: String = (0..w.arity).map(|i| format!(" hc{}.code", i)).collect();
        let show_args: String = (0..w.arity)
            .map(|i| format!(" (Universe.interp hc{}.code)", i))
            .collect();
        let rw_args: String = (0..w.arity)
            .map(|i| format!("hc{}.proof", i))
            .collect::<Vec<_>>()
            .join(", ");
        out.push_str(&format!(
            "\ninstance{cs_ty}{cs}: HasCode BagU ({sp}{ats}) where\n  code := .{stem}{ca}\n  proof := by show {sp}{sa} = {sp}{ats}; rw [{rw}]\n",
            cs_ty = type_params_intro,
            cs = constraints,
            sp = struct_path,
            ats = applied_types,
            stem = stem,
            ca = ctor_args,
            sa = show_args,
            rw = rw_args,
        ));
    }

    fs::write(&path, &out)?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::{Field, Struct, Variant};

    #[test]
    fn variant_field_bag_projection_uses_the_declared_tag() {
        let mut program = Program::default();
        program.structs.insert(
            1,
            Struct {
                module_id: 0,
                name: "Bag".to_string(),
                qualified_name: "bag::Bag".to_string(),
                type_params: vec!["K".to_string(), "V".to_string()],
                fields: Vec::new(),
                variants: None,
                is_native: true,
            },
        );
        program.structs.insert(
            2,
            Struct {
                module_id: 0,
                name: "Carrier".to_string(),
                qualified_name: "p::m::Carrier".to_string(),
                type_params: Vec::new(),
                fields: Vec::new(),
                variants: Some(vec![Variant {
                    name: "Selected".to_string(),
                    tag: 9,
                    fields: vec![Field {
                        name: "bag".to_string(),
                        field_type: Type::Struct {
                            struct_id: 1,
                            type_args: vec![Type::UInt(64), Type::Bool],
                        },
                    }],
                }]),
                is_native: false,
            },
        );
        let expression = Expr::Borrow {
            step: crate::ir::path::PathStep::VariantField {
                struct_id: 2,
                variant: 9,
                field_index: 0,
            },
            base: Box::new(Expr::Var("carrier".into())),
        };

        assert!(expr_yields_bag(
            &expression,
            &std::collections::HashMap::new(),
            &program,
            0,
        ));
    }

    fn accessor_program(returns: Type) -> Program {
        use crate::ir::{FunctionKind, Param, Signature, VarId};

        let mut program = Program::default();
        program.modules.insert(
            0,
            crate::ir::Module {
                name: "proposal".to_string(),
                package_name: "p".to_string(),
                address: String::new(),
                required_imports: vec![],
                is_native: false,
            },
        );
        program.structs.insert(
            1,
            Struct {
                module_id: 0,
                name: "ObjectBag".to_string(),
                qualified_name: "object_bag::ObjectBag".to_string(),
                type_params: Vec::new(),
                fields: Vec::new(),
                variants: None,
                is_native: true,
            },
        );
        program.structs.insert(
            2,
            Struct {
                module_id: 0,
                name: "Proposal".to_string(),
                qualified_name: "p::proposal::Proposal".to_string(),
                type_params: vec!["T".to_string()],
                fields: Vec::new(),
                variants: None,
                is_native: false,
            },
        );
        let parent = Type::Struct {
            struct_id: 3,
            type_args: vec![],
        };
        // `active_mut(p: &mut Proposals): &mut ObjectBag` -- an accessor, not
        // a field projection: the borrow base is its (destructured) result.
        program.functions.insert(
            1,
            crate::ir::Function {
                module: 0,
                name: "active_mut".to_string(),
                signature: Signature {
                    type_params: vec![],
                    params: vec![Param {
                        name: "p".to_string(),
                        var: VarId::from("p"),
                        ty: parent.clone(),
                    }],
                    return_type: returns,
                },
                body: Block::just(Expr::Unit),
                kind: FunctionKind::Source,
                effects: crate::ir::Effects::CONSERVATIVE,
                explicit_pure: false,
            },
        );
        program.functions.insert(
            0,
            crate::ir::Function {
                module: 0,
                name: "remove_vote".to_string(),
                signature: Signature {
                    type_params: vec!["T".to_string()],
                    params: vec![Param {
                        name: "parent".to_string(),
                        var: VarId::from("parent"),
                        ty: parent,
                    }],
                    return_type: Type::Unit,
                },
                body: Block {
                    stmts: vec![Stmt::Let {
                        pattern: vec![Some(VarId::from("bag")), Some(VarId::from("parent1"))],
                        value: Expr::Call {
                            fun: 1,
                            type_args: vec![],
                            args: vec![Expr::Var("parent".into())],
                        },
                    }],
                    tail: BlockTail::Value(Expr::Borrow {
                        step: crate::ir::path::PathStep::MapKey {
                            key: Box::new(Expr::Var("id".into())),
                            key_type: Type::Address,
                            value_type: Type::Struct {
                                struct_id: 2,
                                type_args: vec![Type::TypeParam(0)],
                            },
                            df_value: None,
                        },
                        base: Box::new(Expr::Var("bag".into())),
                    }),
                },
                kind: FunctionKind::Source,
                effects: crate::ir::Effects::CONSERVATIVE,
                explicit_pure: false,
            },
        );
        program
    }

    fn bag_ref() -> Type {
        let bag = Type::Struct {
            struct_id: 1,
            type_args: vec![],
        };
        Type::MutableRef {
            inner: Box::new(bag.clone()),
            root: Box::new(bag),
        }
    }

    #[test]
    fn a_bag_borrowed_through_an_accessor_call_taints_the_value_type_params() {
        // hashi `proposal::remove_vote<T>` borrows `Proposal<T>` out of
        // `proposals.active_mut()`; without the taint `T` lacks
        // `[HasCode BagU T]` and `Object_bag.borrow` cannot synthesize
        // `HasCode BagU (Proposal T)`.
        let deps = compute_bagu_typeparam_deps(&accessor_program(bag_ref()));
        assert_eq!(deps.get(&0), Some(&vec![true]));
    }

    #[test]
    fn an_accessor_returning_the_bag_first_in_a_tuple_also_taints() {
        let returns = Type::Tuple(vec![bag_ref(), Type::Bool]);
        let deps = compute_bagu_typeparam_deps(&accessor_program(returns));
        assert_eq!(deps.get(&0), Some(&vec![true]));
    }

    #[test]
    fn an_accessor_returning_something_else_does_not_taint() {
        let deps = compute_bagu_typeparam_deps(&accessor_program(Type::Bool));
        assert_eq!(deps.get(&0), Some(&vec![false]));
    }
}
