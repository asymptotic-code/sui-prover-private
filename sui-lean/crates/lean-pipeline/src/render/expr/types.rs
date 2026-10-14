//! Partial, best-effort typing of the Lean terms emitted by the renderer.
//!
//! This is intentionally distinct from [`crate::ir::analysis::type_of`],
//! which validates IR semantics. Native ABI erasure, explicit Mutation
//! constructors, and render-time arm coercions make the emitted term's type
//! differ from the source IR type at several boundaries. `None` means this
//! projection has no representation evidence for the expression; coercion
//! callers conservatively classify that case as value form.

use crate::ir::analysis::type_of::{
    bind_pattern, framework_integer_struct, framework_option_struct, strip_mutable_ref_in_type,
    strip_singleton_tuple, substitute_type_params,
};
use crate::ir::{BinOp, BitOp, Block, BlockTail, Expr, Program, QuantifierKind, Type, UnOp, VarId};
use std::collections::BTreeMap;

/// Compute the `var_target_types` map: a binder `v`'s entry is the
/// type Lean expects for `v` based on how `v` flows into the
/// function tail.
///
/// **Single-level coverage.** Looks at the body's outermost tail.
/// When the tail is `Value(Tuple([Var(v_0), Var(v_1), ...]))` and
/// the function return type is `Tuple([T_0, T_1, ...])` of matching
/// arity, sets `var_target_types[v_i] = T_i`. This covers the
/// common stage-3 / stage-4 augmented-return shape: the function
/// body builds an updated mutable value (often via a chain of
/// `let X := ...` rebinds), then the function tail tuple references
/// each bound var in slots aligned with the function's return.
///
/// Multi-level propagation (target flows through nested let chains)
/// is future work; this slice catches the dominant pattern observed
/// on ember-vaults's `support_asset_internal` /
/// `create_multi_collateral_vault` / `process_request` (the 9
/// cluster B residual sites).
pub(in crate::render) fn compute_var_target_types(
    body: &Block,
    return_type: &crate::ir::Type,
) -> BTreeMap<VarId, crate::ir::Type> {
    use crate::ir::Type;
    let mut out: BTreeMap<VarId, crate::ir::Type> = BTreeMap::new();
    let tail_expr: &Expr = match &body.tail {
        BlockTail::Value(e) => e,
        BlockTail::Return(e) => e.as_ref(),
        BlockTail::ReturnFromBlock { value, .. } => value.as_ref(),
        _ => return out,
    };
    let (return_tys, elems) = match (return_type, tail_expr) {
        (Type::Tuple(rs), Expr::Tuple(es)) => (rs, es),
        _ => return out,
    };
    if return_tys.len() != elems.len() {
        return out;
    }
    for (slot_ty, slot_e) in return_tys.iter().zip(elems.iter()) {
        if let Expr::Var(v) = slot_e {
            out.insert(v.clone(), slot_ty.clone());
        }
    }
    out
}

pub(in crate::render) fn let_target_type(
    pattern: &[Option<VarId>],
    value: &Expr,
    var_target_types: &BTreeMap<VarId, crate::ir::Type>,
    program: &Program,
    var_types: &BTreeMap<VarId, crate::ir::Type>,
) -> Option<crate::ir::Type> {
    use crate::ir::Type;

    let slot_targets = if pattern.len() > 1 {
        pattern
            .iter()
            .any(|slot| {
                slot.as_ref()
                    .is_some_and(|var| var_target_types.contains_key(var))
            })
            .then(|| {
                pattern
                    .iter()
                    .map(|slot| {
                        slot.as_ref()
                            .and_then(|var| var_target_types.get(var).cloned())
                    })
                    .collect::<Vec<_>>()
            })
    } else if pattern.len() == 1 {
        pattern[0]
            .as_ref()
            .and_then(|var| var_target_types.get(var).cloned())
            .map(|target| vec![Some(target)])
    } else {
        None
    }?;

    let inferred = rendered_type_of(value, program, var_types);
    let inferred_slots = match inferred {
        Some(Type::Tuple(types)) if types.len() == slot_targets.len() => {
            types.into_iter().map(Some).collect()
        }
        _ => vec![None; slot_targets.len()],
    };
    let mut merged: Vec<Type> = slot_targets
        .into_iter()
        .zip(inferred_slots)
        .map(|(target, inferred)| target.or(inferred).unwrap_or(Type::Unit))
        .collect();
    if pattern.len() == 1 {
        merged.pop()
    } else {
        Some(Type::Tuple(merged))
    }
}

pub(in crate::render) fn rendered_let_bindings(
    pattern: &[Option<VarId>],
    value: &Expr,
    target: Option<&crate::ir::Type>,
    program: &Program,
    var_types: &BTreeMap<VarId, crate::ir::Type>,
) -> Vec<(VarId, crate::ir::Type)> {
    use crate::ir::Type;

    let Some(inferred) = rendered_type_of(value, program, var_types) else {
        return Vec::new();
    };
    if pattern.len() == 1 {
        let Some(var) = pattern[0].clone() else {
            return Vec::new();
        };
        let bound = match (target, inferred) {
            (Some(target), _) => target.clone(),
            (None, Type::Tuple(mut elements)) if elements.len() == 1 => elements.pop().unwrap(),
            (None, inferred) => inferred,
        };
        return vec![(var, bound)];
    }

    let Type::Tuple(inferred_slots) = inferred else {
        return Vec::new();
    };
    if inferred_slots.len() != pattern.len() {
        return Vec::new();
    }
    let target_slots = match target {
        Some(Type::Tuple(types)) if types.len() == pattern.len() => Some(types),
        _ => None,
    };
    let coerces_per_slot = matches!(value, Expr::Tuple(_) | Expr::If { .. } | Expr::Match { .. });
    pattern
        .iter()
        .zip(inferred_slots)
        .enumerate()
        .filter_map(|(index, (slot, inferred))| {
            let var = slot.clone()?;
            let bound = if coerces_per_slot {
                target_slots
                    .and_then(|types| types.get(index))
                    .cloned()
                    .unwrap_or(inferred)
            } else {
                inferred
            };
            Some((var, bound))
        })
        .collect()
}

pub(in crate::render) fn effective_types_equal(
    left: &crate::ir::Type,
    right: &crate::ir::Type,
) -> bool {
    normalize_effective_type(left) == normalize_effective_type(right)
}

fn normalize_effective_type(ty: &crate::ir::Type) -> crate::ir::Type {
    use crate::ir::Type;
    match ty {
        Type::Unit => Type::Unit,
        Type::Bool => Type::Bool,
        Type::Prop => Type::Prop,
        Type::UInt(bits) => Type::UInt(*bits),
        Type::Address => Type::Address,
        Type::Vector(element) => Type::Vector(Box::new(normalize_effective_type(element))),
        Type::Tuple(elements) if elements.is_empty() => Type::Unit,
        Type::Tuple(elements) if elements.len() == 1 => normalize_effective_type(&elements[0]),
        Type::Tuple(elements) => {
            Type::Tuple(elements.iter().map(normalize_effective_type).collect())
        }
        Type::Struct {
            struct_id,
            type_args,
        } => Type::Struct {
            struct_id: *struct_id,
            type_args: type_args.iter().map(normalize_effective_type).collect(),
        },
        Type::Reference(inner) => normalize_effective_type(inner),
        Type::MutableRef { inner, .. } => Type::MutableRef {
            inner: Box::new(normalize_effective_type(inner)),
            root: Box::new(Type::Unit),
        },
        Type::TypeParam(index) => Type::TypeParam(*index),
    }
}

pub(in crate::render) fn rendered_type_of(
    e: &Expr,
    program: &Program,
    var_types: &BTreeMap<VarId, crate::ir::Type>,
) -> Option<crate::ir::Type> {
    use crate::ir::{Const, Type};
    match e {
        Expr::Var(v) => var_types.get(v).cloned(),
        Expr::Const(Const::Bool(_)) => Some(Type::Bool),
        Expr::Const(Const::UInt { bits, .. }) => Some(Type::UInt(*bits)),
        Expr::Const(Const::Address(_)) => Some(Type::Address),
        Expr::Const(Const::Vector { elem_type, .. }) => {
            Some(Type::Vector(Box::new(elem_type.clone())))
        }
        Expr::Const(Const::Unit) => Some(Type::Unit),
        Expr::Const(Const::Default(ty)) => Some(ty.clone()),
        Expr::Unit => Some(Type::Unit),
        Expr::BorrowLoc(v) => {
            // Immutable `&T` is erased to a value `T` here (see the
            // matching BorrowLoc arm in `ir::analysis::type_of`): a
            // local slot holding an immutable-ref-returning call's
            // result is a VALUE, so `BorrowLoc` mutably borrows that
            // value -> `MutableRef { T }`, never `MutableRef { Reference(T) }`.
            let inner = match var_types.get(v)?.clone() {
                Type::Reference(pointee) => *pointee,
                other => other,
            };
            Some(Type::MutableRef {
                inner: Box::new(inner.clone()),
                root: Box::new(inner),
            })
        }
        Expr::BorrowGlobal(id) => Some(program.globals.get(id)?.threaded_param_type()),
        Expr::Field {
            struct_id,
            field_index,
            base,
        } => {
            let struct_def = program.structs.get(struct_id)?;
            let base_type = rendered_type_of(base, program, var_types)?;
            let type_args = rendered_struct_type_args(&base_type, *struct_id)?;
            Some(substitute_type_params(
                &struct_def.fields.get(*field_index)?.field_type,
                &type_args,
            ))
        }
        Expr::Pack {
            struct_id,
            type_args,
            ..
        } => Some(Type::Struct {
            struct_id: *struct_id,
            type_args: type_args.clone(),
        }),
        Expr::Tuple(elems) => {
            let elem_tys: Option<Vec<Type>> = elems
                .iter()
                .map(|e| rendered_type_of(e, program, var_types))
                .collect();
            Some(Type::Tuple(elem_tys?))
        }
        Expr::Call {
            fun,
            type_args,
            args: _,
        } => {
            let callee = program.lookup_callee(*fun)?;
            // After stage 3's `augment_signatures`, every callee's
            // `signature.return_type` already carries the augmented
            // shape (orig_ret + trailing MutableRef slots for &mut
            // params). For non-natives (translated), the rendered
            // Lean function returns Mutable-wrapped trailing values,
            // so the IR shape matches verbatim.
            //
            // For natives, the hand-written Lean function strips
            // MutableRef on the returned values -- so the rendered
            // call's effective type is the IR shape with MutableRef
            // wrappers stripped.
            //
            // Exception: `Mutation.uninit` (the synthetic native
            // registered by stage 2's `mutation_natives` to lower
            // upstream `Operation::Uninit`) ships its return value
            // pre-wrapped in `Prover.Mutation.Mutation`. Its IR
            // signature carries `MutableRef T` and its rendered
            // form carries `Mutation Key T` -- the strip would
            // mismatch and cause downstream `render_expr_with_target_ty`
            // to insert a spurious `Mutation.ofLocal` wrap at any
            // conditional-branch join the temp flows through,
            // producing `Mutation Key (Mutation Key T)` and breaking
            // tuple-position unification. Mirrors the special-case in
            // `render_call` for the same callee name.
            let mut ret = substitute_type_params(&callee.signature().return_type, type_args);
            if callee.is_native() && callee.name() != "Mutation.uninit" {
                ret = strip_mutable_ref_in_type(&ret);
            }
            Some(ret)
        }
        Expr::ReadRef(inner) => {
            let t = rendered_type_of(inner, program, var_types)?;
            match t {
                Type::Reference(inner_ty)
                | Type::MutableRef {
                    inner: inner_ty, ..
                } => Some((*inner_ty).clone()),
                other => Some(other),
            }
        }
        // WriteBack node-of-LocalRoot is the local's prior type
        // (the let-rebound local; renderer emits the bare updated
        // value, no Mutation wrapper). Reference WriteBacks render
        // via `Mutation.set parent ...`, which ALWAYS returns
        // `Mutation Key T` -- even when the parent's IR-side
        // `var_types` entry is the plain struct (e.g. coming from a
        // native return whose `MutableRef` was stripped). Lift the
        // inner to MutableRef in that case so let-bound results
        // type-check as Mutation downstream.
        Expr::WriteBack { node, world, .. } => {
            let node_ty = match node {
                crate::ir::BorrowNode::LocalRoot(v) => var_types.get(v).cloned(),
                crate::ir::BorrowNode::Reference(v) => {
                    let inner_ty = var_types.get(v).cloned()?;
                    let (inner, root) = match inner_ty {
                        Type::MutableRef { inner, root } => (*inner, *root),
                        other => (other.clone(), other),
                    };
                    Some(Type::MutableRef {
                        inner: Box::new(inner),
                        root: Box::new(root),
                    })
                }
                crate::ir::BorrowNode::GlobalRoot(id) => {
                    let inner = program.globals.get(id)?.ty.clone();
                    Some(Type::MutableRef {
                        inner: Box::new(inner.clone()),
                        root: Box::new(inner),
                    })
                }
                _ => None,
            };
            // World-threaded df writeback: result is `(node_value, World)`,
            // like a world-returning call. Trailing slot is the world type.
            match (node_ty, world) {
                (Some(nt), Some(wv)) => {
                    let wt = var_types.get(wv).cloned()?;
                    Some(Type::Tuple(vec![nt, wt]))
                }
                (nt, _) => nt,
            }
        }
        Expr::WriteRef { reference, .. } => {
            // The rendered `Mutation.set parent new_val` always returns
            // `Mutation Key T`. The `reference` operand can be either:
            //   * already Mutation-typed (the typical case after stage 3
            //     mut-to-let preserves Mutation parameters), or
            //   * the plain underlying struct (when the operand comes
            //     from a native return whose IR `MutableRef` slot was
            //     stripped by `is_native` strip_mutable_ref above --
            //     the hand-written native ships value-form returns
            //     while the IR signature still carries MutableRef).
            // In either case the result of the rendered WriteRef is
            // `Mutation T`; lift the inner type into a MutableRef so
            // downstream `var_types` lookups treat the let-bound
            // result as Mutation-typed.
            let inner_ty = rendered_type_of(reference, program, var_types)?;
            let (inner, root) = match inner_ty {
                Type::MutableRef { inner, root } => (*inner, *root),
                other => (other.clone(), other),
            };
            Some(Type::MutableRef {
                inner: Box::new(inner),
                root: Box::new(root),
            })
        }
        Expr::Borrow { step, base } => {
            use crate::ir::path::PathStep;
            match step {
                PathStep::Field {
                    struct_id,
                    field_index,
                } => {
                    let base_ty = rendered_type_of(base, program, var_types)?;
                    // Strip an outer MutableRef so we look up the field on
                    // the inner struct (the Mutable is itself wrapped on the
                    // result).
                    let inner_struct = match &base_ty {
                        Type::MutableRef { inner, .. } => (**inner).clone(),
                        _ => base_ty.clone(),
                    };
                    let struct_def = program.structs.get(struct_id)?;
                    let type_args = rendered_struct_type_args(&inner_struct, *struct_id)?;
                    let field_ty = substitute_type_params(
                        &struct_def.fields.get(*field_index)?.field_type,
                        &type_args,
                    );
                    let root = match &base_ty {
                        Type::MutableRef { root, .. } => (**root).clone(),
                        _ => inner_struct,
                    };
                    Some(Type::MutableRef {
                        inner: Box::new(field_ty),
                        root: Box::new(root),
                    })
                }
                PathStep::VariantField {
                    struct_id,
                    variant,
                    field_index,
                } => {
                    let base_ty = rendered_type_of(base, program, var_types)?;
                    let inner_struct = match &base_ty {
                        Type::MutableRef { inner, .. } => (**inner).clone(),
                        _ => base_ty.clone(),
                    };
                    let type_args = rendered_struct_type_args(&inner_struct, *struct_id)?;
                    let field = program
                        .structs
                        .get(struct_id)?
                        .variant_by_tag(*variant)?
                        .fields
                        .get(*field_index)?;
                    let field_ty = substitute_type_params(&field.field_type, &type_args);
                    let root = match &base_ty {
                        Type::MutableRef { root, .. } => (**root).clone(),
                        _ => inner_struct,
                    };
                    Some(Type::MutableRef {
                        inner: Box::new(field_ty),
                        root: Box::new(root),
                    })
                }
                PathStep::VecIndex(_) => {
                    // `vector::borrow_mut(v, i)` -- result is `Mutation T`
                    // where T is the vector element type. Mirrors
                    // `ir::analysis::type_of::BorrowVecIndex`.
                    let base_ty = rendered_type_of(base, program, var_types)?;
                    let elem = match &base_ty {
                        Type::Vector(t) => (**t).clone(),
                        Type::MutableRef { inner, .. } => match inner.as_ref() {
                            Type::Vector(t) => (**t).clone(),
                            _ => return None,
                        },
                        _ => return None,
                    };
                    let root = match base_ty {
                        Type::MutableRef { root, .. } => (*root).clone(),
                        other => other,
                    };
                    Some(Type::MutableRef {
                        inner: Box::new(elem),
                        root: Box::new(root),
                    })
                }
                PathStep::MapKey { value_type, .. } => {
                    // `table::borrow_mut(t, k)` / `dynamic_field::borrow_mut`
                    // / `bag::borrow_mut` etc. Result is `Mutation V` where
                    // V is the value type carried on the borrow op.
                    let base_ty = rendered_type_of(base, program, var_types)?;
                    let root = match base_ty {
                        Type::MutableRef { root, .. } => (*root).clone(),
                        other => other,
                    };
                    Some(Type::MutableRef {
                        inner: Box::new(value_type.clone()),
                        root: Box::new(root),
                    })
                }
            }
        }
        Expr::Update { base, .. } => rendered_type_of(base, program, var_types),
        Expr::Unpack {
            struct_id,
            variant,
            value,
        } => {
            let struct_def = program.structs.get(struct_id)?;
            let value_type = rendered_type_of(value, program, var_types)?;
            let type_args = rendered_struct_type_args(&value_type, *struct_id)?;
            // For an ENUM, the payload fields live on the selected VARIANT,
            // not on the (empty) struct-level `fields`. Using `struct_def.fields`
            // for a variant unpack infers `Tuple([])` (arity 0), so the
            // multi-binder `let (a, b) := unpack ..` render path (body.rs)
            // fails closed on an apparent arity mismatch. Mirror the render
            // arm (`render::expr` Unpack) and project the chosen variant's
            // fields so valid unpack bindings retain their precise shape.
            let fields = if struct_def.variants.is_some() {
                &struct_def.variant_by_tag((*variant)?)?.fields
            } else {
                &struct_def.fields
            };
            if fields.len() == 1 {
                Some(substitute_type_params(&fields[0].field_type, &type_args))
            } else {
                Some(Type::Tuple(
                    fields
                        .iter()
                        .map(|field| substitute_type_params(&field.field_type, &type_args))
                        .collect(),
                ))
            }
        }
        Expr::If {
            then_branch,
            else_branch,
            ..
        } => {
            // Inferred type matches what the renderer emits for the
            // if expression, including the `{Mutation T, T}` arm
            // coercion in `unify_if_arm_types` /
            // `render_inner_block_with_target_ty`. If exactly one
            // arm is `Mutation T` and the other is `T`, the
            // renderer wraps the value-form arm in
            // `Mutation.ofLocal`, so the if's result is `Mutation T`
            // -- report that here so let-binding propagation,
            // downstream `.val` unwraps, and field projections all
            // see the post-coercion type.
            let arm_types = [
                rendered_block_branch_type(then_branch, program, var_types),
                rendered_block_branch_type(else_branch, program, var_types),
            ];
            unify_branch_value_types(&arm_types).ok().flatten()
        }
        Expr::Match {
            struct_id,
            selector,
            cases,
        } => {
            // Same unification logic across N arms: peel singleton
            // tuples, then if any arm is `Mutation T` and another
            // is `T`, the renderer coerces all `T` arms up. Fold
            // left.
            //
            let selector_type_args =
                rendered_match_selector_type_args(*struct_id, selector, program, var_types);
            let structure = program.structs.get(struct_id)?;
            structure.variants.as_ref()?;
            let mut arm_types = Vec::with_capacity(cases.len());
            for case in cases {
                let variant = structure.variant_by_tag(case.variant)?;
                let mut arm_var_types = var_types.clone();
                arm_var_types.extend(match_arm_binding_types(
                    &case.bindings,
                    &variant.fields,
                    &selector_type_args,
                ));
                arm_types.push(rendered_block_branch_type(
                    &case.body,
                    program,
                    &arm_var_types,
                ));
            }
            unify_branch_value_types(&arm_types).ok().flatten()
        }
        Expr::UnOp { op, operand } => match op {
            // `!b` is always Bool; `x as uN` is UInt(N); `~x`
            // preserves the operand's (integer) type.
            UnOp::Not => Some(Type::Bool),
            UnOp::Cast(bits) => Some(Type::UInt(*bits)),
            UnOp::BitNot => rendered_type_of(operand, program, var_types),
        },
        Expr::BinOp { op, lhs, rhs } => match op {
            // Logical / comparison ops yield Bool; arithmetic and
            // bitwise ops yield the operand type (prefer lhs, fall
            // back to rhs). Without this, a tuple element like
            // `(!status.flag, world)` infers to None, which makes a
            // valid multi-slot `let (b, world) := if ...` fail closed
            // as an apparent RHS-shape mismatch. Reproduced by
            // cetus-clmm `is_allow_*` readers once their df/dof reads
            // world-thread.
            BinOp::And
            | BinOp::Or
            | BinOp::Eq
            | BinOp::Neq
            | BinOp::Lt
            | BinOp::Le
            | BinOp::Gt
            | BinOp::Ge
            | BinOp::SLt
            | BinOp::SLe
            | BinOp::SGt
            | BinOp::SGe => Some(Type::Bool),
            _ => rendered_type_of(lhs, program, var_types)
                .or_else(|| rendered_type_of(rhs, program, var_types)),
        },
        Expr::BitOp(op) => match op {
            BitOp::Extract { high, low, .. } => {
                Some(Type::UInt(high.checked_sub(*low).unwrap_or(0) + 1))
            }
            BitOp::ZeroExtend { bits, operand } | BitOp::SignExtend { bits, operand } => {
                match rendered_type_of(operand, program, var_types) {
                    Some(Type::UInt(width)) => Some(Type::UInt(width + bits)),
                    _ => None,
                }
            }
            BitOp::Concat { high, low } => {
                match (
                    rendered_type_of(high, program, var_types),
                    rendered_type_of(low, program, var_types),
                ) {
                    (Some(Type::UInt(high_width)), Some(Type::UInt(low_width))) => {
                        Some(Type::UInt(high_width + low_width))
                    }
                    _ => None,
                }
            }
        },
        Expr::IsParent { .. } => Some(Type::Bool),
        Expr::Quantifier {
            kind,
            binder,
            binder_type,
            body,
            ..
        } => rendered_quantifier_type(*kind, binder, binder_type, body, program, var_types),
        Expr::While { .. } | Expr::ToProp(_) | Expr::ToBool(_) | Expr::LabeledBlock { .. } => None,
    }
}

fn rendered_quantifier_type(
    kind: QuantifierKind,
    binder: &VarId,
    binder_type: &Type,
    body: &Block,
    program: &Program,
    var_types: &BTreeMap<VarId, Type>,
) -> Option<Type> {
    let body_type = || {
        let mut inner = var_types.clone();
        inner.insert(binder.clone(), binder_type.clone());
        rendered_block_value_type(body, program, &inner)
    };
    match kind {
        QuantifierKind::Forall
        | QuantifierKind::Exists
        | QuantifierKind::Any
        | QuantifierKind::All => Some(Type::Bool),
        QuantifierKind::Count => Some(Type::UInt(64)),
        QuantifierKind::SumMap => framework_integer_struct(program)
            .map(|struct_id| Type::Struct {
                struct_id,
                type_args: Vec::new(),
            })
            .or_else(body_type),
        QuantifierKind::FindIndex => framework_option_struct(program)
            .map(|struct_id| Type::Struct {
                struct_id,
                type_args: vec![Type::UInt(64)],
            })
            .or_else(body_type),
        QuantifierKind::Map => body_type().map(|body| Type::Vector(Box::new(body))),
        QuantifierKind::Filter => Some(Type::Vector(Box::new(strip_rendered_ref(binder_type)))),
        QuantifierKind::Find => {
            let element = strip_rendered_ref(binder_type);
            framework_option_struct(program)
                .map(|struct_id| Type::Struct {
                    struct_id,
                    type_args: vec![element],
                })
                .or_else(|| body_type().map(|body| Type::Vector(Box::new(body))))
        }
        QuantifierKind::FindIndices => Some(Type::Vector(Box::new(Type::UInt(64)))),
    }
}

fn strip_rendered_ref(ty: &Type) -> Type {
    match ty {
        Type::Reference(inner) | Type::MutableRef { inner, .. } => inner.as_ref().clone(),
        other => other.clone(),
    }
}

pub(in crate::render) fn rendered_struct_type_args(
    ty: &crate::ir::Type,
    struct_id: crate::ir::StructId,
) -> Option<Vec<crate::ir::Type>> {
    use crate::ir::Type;
    match ty {
        Type::Struct {
            struct_id: actual,
            type_args,
        } if *actual == struct_id => Some(type_args.clone()),
        Type::Reference(inner) | Type::MutableRef { inner, .. } => {
            rendered_struct_type_args(inner, struct_id)
        }
        Type::Tuple(items) if items.len() == 1 => rendered_struct_type_args(&items[0], struct_id),
        _ => None,
    }
}

pub(in crate::render) fn rendered_match_selector_type_args(
    struct_id: crate::ir::StructId,
    selector: &Expr,
    program: &Program,
    var_types: &BTreeMap<VarId, crate::ir::Type>,
) -> Vec<crate::ir::Type> {
    rendered_type_of(selector, program, var_types)
        .and_then(|ty| rendered_struct_type_args(&ty, struct_id))
        .unwrap_or_default()
}

pub(in crate::render) fn match_arm_binding_types(
    bindings: &[VarId],
    fields: &[crate::ir::Field],
    type_args: &[crate::ir::Type],
) -> Vec<(VarId, crate::ir::Type)> {
    bindings
        .iter()
        .zip(fields)
        .map(|(binding, field)| {
            (
                binding.clone(),
                substitute_type_params(&field.field_type, type_args),
            )
        })
        .collect()
}

/// Infer the value type of a `Block`: only succeeds when the tail
/// is `BlockTail::Value(_)`. Used for inferring the type of
/// `Expr::If` / `Expr::Match` arms, which are Blocks.
///
/// Walks the block's preceding `Stmt::Let`s to extend `var_types`
/// with arm-local bindings before inferring the tail. Without this
/// extension, a tail expression like `Tuple([Var(arm_local), ...])`
/// where `arm_local` is bound inside the arm falls back to outer
/// `var_types` (which doesn't have it) and `rendered_type_of` returns
/// `None`, breaking arm unification.
pub(in crate::render) fn rendered_block_value_type(
    b: &Block,
    program: &Program,
    var_types: &BTreeMap<VarId, crate::ir::Type>,
) -> Option<crate::ir::Type> {
    use crate::ir::Stmt;
    let tail_expr = match &b.tail {
        BlockTail::Value(e) => e,
        _ => return None,
    };
    let mut local_vt = var_types.clone();
    for s in &b.stmts {
        if let Stmt::Let { pattern, value } = s {
            if let Some(ty) = rendered_type_of(value, program, &local_vt) {
                let _ = bind_pattern(pattern, &ty, &mut local_vt);
            }
        }
    }
    rendered_type_of(tail_expr, program, &local_vt)
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum RenderedBranchType {
    Terminal,
    Known(crate::ir::Type),
    Unknown,
}

pub(crate) fn rendered_block_branch_type(
    block: &Block,
    program: &Program,
    var_types: &BTreeMap<VarId, crate::ir::Type>,
) -> RenderedBranchType {
    match &block.tail {
        BlockTail::Abort { .. } => RenderedBranchType::Terminal,
        BlockTail::Value(expression) => {
            let mut local_var_types = var_types.clone();
            for statement in &block.stmts {
                if let crate::ir::Stmt::Let { pattern, value } = statement {
                    if let Some(ty) = rendered_type_of(value, program, &local_var_types) {
                        let _ = bind_pattern(pattern, &ty, &mut local_var_types);
                    }
                }
            }
            rendered_expr_branch_type(expression, program, &local_var_types)
        }
        _ => RenderedBranchType::Unknown,
    }
}

fn rendered_expr_branch_type(
    expression: &Expr,
    program: &Program,
    var_types: &BTreeMap<VarId, crate::ir::Type>,
) -> RenderedBranchType {
    let arms = match expression {
        Expr::If {
            then_branch,
            else_branch,
            ..
        } => vec![
            rendered_block_branch_type(then_branch, program, var_types),
            rendered_block_branch_type(else_branch, program, var_types),
        ],
        Expr::Match {
            struct_id,
            selector,
            cases,
        } if !cases.is_empty() => {
            let Some(structure) = program.structs.get(struct_id) else {
                return RenderedBranchType::Unknown;
            };
            let type_args =
                rendered_match_selector_type_args(*struct_id, selector, program, var_types);
            let mut arms = Vec::with_capacity(cases.len());
            for arm in cases {
                let Some(variant) = structure.variant_by_tag(arm.variant) else {
                    return RenderedBranchType::Unknown;
                };
                let mut arm_scope = var_types.clone();
                arm_scope.extend(match_arm_binding_types(
                    &arm.bindings,
                    &variant.fields,
                    &type_args,
                ));
                arms.push(rendered_block_branch_type(&arm.body, program, &arm_scope));
            }
            arms
        }
        _ => {
            return rendered_type_of(expression, program, var_types)
                .map(RenderedBranchType::Known)
                .unwrap_or(RenderedBranchType::Unknown);
        }
    };

    match unify_branch_value_types(&arms) {
        Ok(Some(ty)) => RenderedBranchType::Known(ty),
        Ok(None) => RenderedBranchType::Terminal,
        Err(()) => RenderedBranchType::Unknown,
    }
}

pub(crate) fn unify_branch_value_types(
    arms: &[RenderedBranchType],
) -> Result<Option<crate::ir::Type>, ()> {
    let mut unified = None;
    for arm in arms {
        match arm {
            RenderedBranchType::Terminal => {}
            RenderedBranchType::Unknown => return Err(()),
            RenderedBranchType::Known(next) => {
                unified = Some(match unified {
                    None => next.clone(),
                    Some(previous) => unify_arm_value_types(previous, next.clone()).ok_or(())?,
                });
            }
        }
    }
    Ok(unified)
}

pub(in crate::render) fn branch_coercion_target(
    arms: &[RenderedBranchType],
) -> Result<Option<crate::ir::Type>, ()> {
    let unified = unify_branch_value_types(arms)?;
    let Some(target) = unified else {
        return Ok(None);
    };
    let needs_target = arms.iter().any(|arm| match arm {
        RenderedBranchType::Terminal => true,
        RenderedBranchType::Known(actual) => !effective_types_equal(actual, &target),
        RenderedBranchType::Unknown => false,
    });
    Ok(needs_target.then_some(target))
}

pub(crate) fn block_can_render_as_type(
    block: &Block,
    target: &crate::ir::Type,
    program: &Program,
    var_types: &BTreeMap<VarId, crate::ir::Type>,
) -> bool {
    match &block.tail {
        BlockTail::Abort { .. } => true,
        BlockTail::Value(expression) => {
            let mut local = var_types.clone();
            for statement in &block.stmts {
                if let crate::ir::Stmt::Let { pattern, value } = statement {
                    if let Some(ty) = rendered_type_of(value, program, &local) {
                        let _ = bind_pattern(pattern, &ty, &mut local);
                    }
                }
            }
            expr_can_render_as_type(expression, target, program, &local)
        }
        _ => false,
    }
}

pub(crate) fn expr_can_render_as_type(
    expression: &Expr,
    target: &crate::ir::Type,
    program: &Program,
    var_types: &BTreeMap<VarId, crate::ir::Type>,
) -> bool {
    use crate::ir::Type;

    match expression {
        Expr::If {
            then_branch,
            else_branch,
            ..
        } => {
            return block_can_render_as_type(then_branch, target, program, var_types)
                && block_can_render_as_type(else_branch, target, program, var_types);
        }
        Expr::Match {
            struct_id,
            selector,
            cases,
        } if !cases.is_empty() => {
            let Some(structure) = program.structs.get(struct_id) else {
                return false;
            };
            let type_args =
                rendered_match_selector_type_args(*struct_id, selector, program, var_types);
            return cases.iter().all(|arm| {
                let Some(variant) = structure.variant_by_tag(arm.variant) else {
                    return false;
                };
                let mut arm_scope = var_types.clone();
                arm_scope.extend(match_arm_binding_types(
                    &arm.bindings,
                    &variant.fields,
                    &type_args,
                ));
                block_can_render_as_type(&arm.body, target, program, &arm_scope)
            });
        }
        _ => {}
    }

    let Some(actual) = rendered_type_of(expression, program, var_types)
        .map(|ty| strip_singleton_tuple(&ty).clone())
    else {
        return false;
    };
    if effective_types_equal(&actual, target) {
        return true;
    }
    match (target, &actual) {
        (Type::MutableRef { inner, .. }, actual)
            if !matches!(actual, Type::MutableRef { .. })
                && effective_types_equal(inner, actual) =>
        {
            true
        }
        (target, Type::MutableRef { inner, .. }) if effective_types_equal(target, inner) => true,
        (Type::Tuple(targets), Type::Tuple(actuals)) if targets.len() == actuals.len() => {
            match expression {
                Expr::Tuple(elements) if elements.len() == targets.len() => {
                    elements.iter().zip(targets).all(|(element, target)| {
                        expr_can_render_as_type(element, target, program, var_types)
                    })
                }
                _ => false,
            }
        }
        _ => false,
    }
}

/// Unify two known emitted arm types. When exactly one is `MutableRef T`
/// and the other is `T`, pick the `MutableRef T` form; recurse slot-by-slot
/// through equal-arity tuples. Unrelated types return `None` instead of a
/// first-arm fallback.
fn unify_arm_value_types(left: crate::ir::Type, right: crate::ir::Type) -> Option<crate::ir::Type> {
    use crate::ir::Type;
    let left = strip_singleton_tuple(&left).clone();
    let right = strip_singleton_tuple(&right).clone();
    match (left, right) {
        (left, right) if effective_types_equal(&left, &right) => Some(left),
        (Type::Tuple(left), Type::Tuple(right)) if left.len() == right.len() => {
            // Per-slot unification for multi-slot tuples. Single-slot
            // tuples are already peeled above by peel_singleton.
            let unified: Option<Vec<Type>> = left
                .into_iter()
                .zip(right)
                .map(|(left, right)| unify_arm_value_types(left, right))
                .collect();
            unified.map(Type::Tuple)
        }
        (left, right) => {
            // {MutableRef T, T} -> pick MutableRef T.
            match (&left, &right) {
                (Type::MutableRef { inner, .. }, value) if effective_types_equal(inner, value) => {
                    Some(left)
                }
                (value, Type::MutableRef { inner, .. }) if effective_types_equal(value, inner) => {
                    Some(right)
                }
                _ => None,
            }
        }
    }
}
