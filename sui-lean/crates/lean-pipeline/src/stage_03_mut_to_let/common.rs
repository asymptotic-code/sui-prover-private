//! Shared helpers for stage 3 (mut-to-let) transformations.
//!
//! Three primitives consumed by `signatures.rs`, `body_tail.rs`, and
//! `call_augment.rs`:
//!
//! - [`mut_param_info`] -- enumerate a function's `&mut` parameters in
//!   declaration order, returning `(index, var_id, inner_type, root_type)`
//!   for each. Returns an empty vec for functions with no `&mut` params.
//! - [`augment_return_type`] -- compute the augmented return type given the
//!   original and the list of `&mut` param types.
//! - [`augment_value`] -- wrap a tail value expression with the trailing
//!   mut-state `Var(p)` elements, flattening tuples as appropriate.

use crate::ir::{Expr, Function, Type, VarId};

/// One `&mut` parameter's identifying info.
#[derive(Debug, Clone)]
pub struct MutParam {
    /// Variable id (the parameter's SSA name).
    pub var: VarId,
    /// The full `Type::MutableRef { inner, root }`. Reused as the
    /// element type when appended to the augmented return tuple.
    pub mut_ref_type: Type,
}

/// Enumerate every `&mut` parameter of `func` in declaration order.
pub fn mut_param_info(func: &Function) -> Vec<MutParam> {
    mut_param_info_sig(&func.signature)
}

pub fn mut_param_info_sig(sig: &crate::ir::Signature) -> Vec<MutParam> {
    sig.params
        .iter()
        .filter_map(|p| match &p.ty {
            Type::MutableRef { .. } => Some(MutParam {
                var: p.var.clone(),
                mut_ref_type: p.ty.clone(),
            }),
            _ => None,
        })
        .collect()
}

/// Compute the augmented return type. See the design doc's Transform 4.
///
/// **Always-Tuple invariant.** The augmented return type is **always**
/// `Type::Tuple([...])`, even when the head is empty (Unit return) and
/// there's only one mut param (the result is `Type::Tuple([mut_ref_type])`,
/// a singleton tuple). This makes idempotency detection reliable: a
/// non-Tuple return type is unambiguously NOT yet augmented; a Tuple
/// whose trailing N entries match the mut param types IS augmented.
/// The renderer collapses singleton tuples to their element when
/// emitting Lean.
///
/// Rules:
/// - No `&mut` params: return `orig` unchanged (no Tuple wrapping).
/// - `orig == Unit`: `Tuple([mut_ref_types...])`.
/// - `orig` is a `Tuple`: extend with mut types, flattening.
/// - Otherwise: `Tuple([orig, mut_ref_types...])`.
pub fn augment_return_type(orig: Type, muts: &[MutParam]) -> Type {
    if muts.is_empty() {
        return orig;
    }
    let mut_types: Vec<Type> = muts.iter().map(|m| m.mut_ref_type.clone()).collect();
    match orig {
        Type::Unit => Type::Tuple(mut_types),
        Type::Tuple(mut items) => {
            items.extend(mut_types);
            Type::Tuple(items)
        }
        other => {
            let mut items = Vec::with_capacity(1 + mut_types.len());
            items.push(other);
            items.extend(mut_types);
            Type::Tuple(items)
        }
    }
}

/// Augment a tail value expression with trailing mut-state `Var(p)`
/// elements. See the design doc's Transform 5.
///
/// Mirrors [`augment_return_type`]'s always-Tuple rule -- the augmented
/// value is always `Expr::Tuple([...])`, even for the singleton case.
pub fn augment_value(value: Expr, muts: &[MutParam], ret_is_unit: bool) -> Expr {
    if muts.is_empty() {
        return value;
    }
    let mut_vars: Vec<Expr> = muts.iter().map(|m| Expr::Var(m.var.clone())).collect();
    if ret_is_unit {
        return Expr::Tuple(mut_vars);
    }
    match value {
        Expr::Tuple(mut items) => {
            items.extend(mut_vars);
            Expr::Tuple(items)
        }
        other => {
            let mut items = Vec::with_capacity(1 + mut_vars.len());
            items.push(other);
            items.extend(mut_vars);
            Expr::Tuple(items)
        }
    }
}
