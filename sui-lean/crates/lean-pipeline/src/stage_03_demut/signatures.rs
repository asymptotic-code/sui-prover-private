//! Signature manipulation for stage 3.
//!
//! Phase 1 (this file): pure type-level computation. `augment_return`
//! takes a function's original return type and the (already-stripped)
//! types of its `&mut`-typed parameters, and produces the augmented
//! return type per the convention in
//! `plans/lean-pipeline/stage-03-demut.md` "Augmented return
//! convention":
//!
//! | Case | Return type |
//! |---|---|
//! | `R != ()` and `R` not a `Tuple` | `Tuple([R, T1, T2, ...])` |
//! | `R != ()` and `R = Tuple([A, B, ...])` | `Tuple([A, B, ..., T1, T2, ...])` (flattened) |
//! | `R = ()` and one mut param | `T1` (no tuple wrap) |
//! | `R = ()` and two+ mut params | `Tuple([T1, T2, ...])` |
//! | No mut params | `R` unchanged |
//!
//! Phase 2 (this file): per-function signature rewriter built on top
//! of `augment_return`. `demote_signature` mutates a `Function::signature`
//! in place: strips `Type::MutableRef` from every parameter, and
//! adjusts the return type per the demotion pattern (standard /
//! pattern 4a / pattern 4b). Native functions and functions with no
//! `&mut`-typed params or return are no-ops.
//!
//! Phases 3-4 use this to rewrite call sites and rebuild body tails.

use crate::ir::{BlockTail, Expr, Function, Program, Type, VarId};

use super::demotion_set::DemotionMap;

/// Augment `r` with the trailing types of demoted `&mut`-typed
/// parameters. See the table above for the rules.
pub fn augment_return(r: Type, mut_param_types: &[Type]) -> Type {
    if mut_param_types.is_empty() {
        return r;
    }
    match r {
        Type::Unit => {
            if mut_param_types.len() == 1 {
                mut_param_types[0].clone()
            } else {
                Type::Tuple(mut_param_types.to_vec())
            }
        }
        Type::Tuple(mut existing) => {
            existing.extend_from_slice(mut_param_types);
            Type::Tuple(existing)
        }
        other => {
            let mut tup = Vec::with_capacity(1 + mut_param_types.len());
            tup.push(other);
            tup.extend_from_slice(mut_param_types);
            Type::Tuple(tup)
        }
    }
}

/// Classifies a function's demotion shape based on its current
/// signature and body tail.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DemotionPattern {
    /// No `&mut` params and no `&mut` return -- nothing to do.
    NoMut,
    /// Standard demotion: strip `&mut` from params, augment return.
    Standard,
    /// Pattern 4a (self-return): function returns `&mut T` where the
    /// body's tail is `Value(Var(p))` with `p` one of the `&mut`-typed
    /// params. Demote the return to plain `T` (the inner type, no
    /// augmentation -- the param's final state IS the return value).
    SelfReturn,
    /// Pattern 4b (sub-field-mutref-return): function returns `&mut U`
    /// where the body's tail is some other borrow chain (a sub-field
    /// borrow off a `&mut`-typed param). Strip `&mut` from params, but
    /// KEEP `Type::MutableRef` in the return position. Caller-side
    /// consumers see this as `Mutable<U, T>` and unwrap it at the
    /// consumption site via stage 3's WriteRef-rebind plus stage 4's
    /// ReadRef substitution.
    SubFieldReturn,
}

/// Classify how `func` should be demoted. Only ever called on
/// translated `Function` entries (`program.functions`); native
/// `NativeDecl` signatures are intentionally not demoted -- the
/// hand-written Lean prelude declares them in their already-demoted
/// shape.
pub fn classify(func: &Function) -> DemotionPattern {
    let has_mut_param = func
        .signature
        .params
        .iter()
        .any(|p| matches!(p.ty, Type::MutableRef { .. }));
    let returns_mut = matches!(func.signature.return_type, Type::MutableRef { .. });

    if !has_mut_param && !returns_mut {
        return DemotionPattern::NoMut;
    }
    if !returns_mut {
        return DemotionPattern::Standard;
    }

    // Returns `&mut U`. Distinguish 4a (self-return) from 4b
    // (sub-field). The deciding signal is whether the body tail is
    // exactly `Value(Var(p))` for a `&mut`-typed param p.
    if let BlockTail::Value(Expr::Var(name)) = &func.body.tail {
        if is_mut_param(func, name) {
            return DemotionPattern::SelfReturn;
        }
    }
    DemotionPattern::SubFieldReturn
}

fn is_mut_param(func: &Function, var: &VarId) -> bool {
    func.signature
        .params
        .iter()
        .any(|p| &p.var == var && matches!(p.ty, Type::MutableRef { .. }))
}

/// Rewrite `func`'s signature in place per its demotion pattern.
///
/// - Strips `Type::MutableRef` from every parameter (standard,
///   self-return, and sub-field-return cases).
/// - Adjusts the return type:
///   - Standard: `augment_return(R, &mut_param_inner_types)`.
///   - SelfReturn: replaces `&mut T` return with `T` (no augmentation).
///   - SubFieldReturn: keeps `&mut U` return unchanged.
///   - NoMut: no-op.
///
/// Body rewriting (call-site destructure, WriteRef/WriteBack rebinds,
/// body-tail rewrite) is the responsibility of later phases.
pub fn demote_signature(func: &mut Function) {
    let pattern = classify(func);
    if pattern == DemotionPattern::NoMut {
        return;
    }

    // Collect the inner types of every `&mut`-typed param BEFORE
    // stripping (we need them for the augmentation step in standard
    // demotion).
    let mut_inner_types: Vec<Type> = func
        .signature
        .params
        .iter()
        .filter_map(|p| match &p.ty {
            Type::MutableRef { inner, .. } => Some((**inner).clone()),
            _ => None,
        })
        .collect();

    // Strip `&mut` from every param.
    for param in func.signature.params.iter_mut() {
        if let Type::MutableRef { inner, .. } = &param.ty {
            param.ty = (**inner).clone();
        }
    }

    // Adjust the return type per the pattern.
    match pattern {
        DemotionPattern::NoMut => unreachable!(),
        DemotionPattern::Standard => {
            let r = std::mem::replace(&mut func.signature.return_type, Type::Unit);
            func.signature.return_type = augment_return(r, &mut_inner_types);
        }
        DemotionPattern::SelfReturn => {
            // Return type was `MutableRef { inner: T, .. }`; demote to T.
            if let Type::MutableRef { inner, .. } = &func.signature.return_type {
                let t = (**inner).clone();
                func.signature.return_type = t;
            }
        }
        DemotionPattern::SubFieldReturn => {
            // Keep `Type::MutableRef` in the return position untouched.
        }
    }
}

// ---------------------------------------------------------------------------
// Body-tail rewriter (Phase 4 §11)
// ---------------------------------------------------------------------------

/// Rewrite the tail of every Standard-demoted function's body to
/// match its augmented return type.
///
/// For each demoted-as-Standard function with `&mut`-typed params
/// `p1, p2, ...` (taken from the function's pre-augmentation
/// signature -- captured by `DemotionMap` before
/// `demote_signature` mutated anything):
///
/// - `BlockTail::Value(Expr::Unit)`, one mut: `Value(Var(p1))`.
/// - `BlockTail::Value(Expr::Unit)`, many muts: `Value(Tuple([Var(p1), Var(p2), ...]))`.
/// - `BlockTail::Value(Expr::Tuple(items))`: `Value(Tuple(items ++ [Var(p1), ...]))` (flatten).
/// - `BlockTail::Value(other)`: `Value(Tuple([other, Var(p1), ...]))` (wrap).
/// - Non-`Value` tails (`Break` / `Continue` / `Return` / `Abort`):
///   left untouched. Mutref consumption inside them is Phase 5's
///   concern.
///
/// `SelfReturn` and `SubFieldReturn` patterns are no-ops here -- their
/// tails already match the demoted return shape (the param's value
/// for 4a, a borrow chain for 4b).
pub fn rewrite_body_tails(program: &mut Program, demotion_map: &DemotionMap) {
    for (fid, func) in program.functions.iter_mut() {
        let info = match demotion_map.info(*fid) {
            Some(i) => i,
            None => continue,
        };
        if info.pattern != DemotionPattern::Standard {
            continue;
        }
        // Take the var ids of the mut-typed params (in their original
        // order, by index). After `demote_signature`, params still
        // carry the same `var` -- only `.ty` was stripped.
        let mut_var_ids: Vec<crate::ir::VarId> = info
            .mut_param_indices
            .iter()
            .map(|&idx| func.signature.params[idx].var.clone())
            .collect();
        rewrite_tail(&mut func.body.tail, &mut_var_ids);
    }
}

fn rewrite_tail(tail: &mut BlockTail, mut_var_ids: &[crate::ir::VarId]) {
    if let BlockTail::Value(v) = tail {
        let original = std::mem::replace(v, crate::ir::Expr::Unit);
        let augmented = augment_tail_value(original, mut_var_ids);
        *v = augmented;
    }
}

fn augment_tail_value(value: crate::ir::Expr, mut_var_ids: &[crate::ir::VarId]) -> crate::ir::Expr {
    use crate::ir::Expr;
    let var_exprs: Vec<Expr> = mut_var_ids.iter().map(|v| Expr::Var(v.clone())).collect();
    match value {
        Expr::Unit => {
            if var_exprs.len() == 1 {
                var_exprs.into_iter().next().unwrap()
            } else {
                Expr::Tuple(var_exprs)
            }
        }
        Expr::Tuple(mut items) => {
            items.extend(var_exprs);
            Expr::Tuple(items)
        }
        other => {
            let mut items = Vec::with_capacity(1 + var_exprs.len());
            items.push(other);
            items.extend(var_exprs);
            Expr::Tuple(items)
        }
    }
}
