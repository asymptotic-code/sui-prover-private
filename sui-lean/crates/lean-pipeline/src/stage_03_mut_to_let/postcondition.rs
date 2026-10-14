//! Stage-3 (mut-to-let) postcondition.
//!
//! Stage-3-local checks (see `plans/lean-pipeline/stage-03-mut-to-let.md` "Outputs"):
//!
//! 1. Zero `Stmt::Eval(Expr::WriteRef ..)` in any non-native body.
//! 2. Zero `Stmt::Eval(Expr::WriteBack ..)` in any non-native body.
//! 3. Every non-native function with `&mut` params has a return type
//!    matching the augmented shape.
//! 4. Zero `Stmt::Eval(Expr::Call(f, ..))` where `f` (in the program)
//!    has `&mut` params. (Such calls must live in `Stmt::Let { value: Call ..}` so
//!    the caller picks up the augmented destructure.)
//!
//! This check deliberately does not run the base IR validator. Stage 2
//! can emit pre-SSA branch merges as `Stmt::Eval(If { arm: let t = ...
//! })` followed by uses of `t`; stage 5's phi pass rewrites that to a
//! well-scoped `Stmt::Let { value: If, .. }`. A full scope check before
//! SSA is therefore a false positive for valid pipeline input.

use std::collections::BTreeMap;

use crate::ir::validate::ValidationError;
use crate::ir::{Block, BlockTail, Expr, FunId, MatchArm, Program, Stmt, StructId, Type};

use super::common::{augment_return_type, mut_param_info, MutParam};

/// Find the synthetic World struct's `StructId` if stage 4 has already
/// registered it. Stage 3's signature-shape check must allow for a
/// trailing `World` slot on the return type when this invariant is
/// re-checked after stage 4 has appended one to every Impure function.
fn find_world_struct_id(program: &Program) -> Option<StructId> {
    program.struct_id_by_qualified_name(crate::stage_04_effects::WORLD_QUALIFIED_NAME)
}

/// Return `(stripped, Some(world_ty))` if `ty` is a `Type::Tuple` whose
/// last element is the World struct; otherwise `(ty, None)`.
///
/// The stripped form always stays a `Type::Tuple` (or `Type::Unit` for
/// the empty case) -- the always-Tuple invariant of stage 3 means a
/// post-stage-3 return type is always a tuple, even when it has a
/// single element. Unwrapping a singleton here would make the
/// stage-3-shape recovery wrongly think the original return was that
/// single element type.
fn strip_trailing_world(ty: &Type, world_id: Option<StructId>) -> (Type, Option<Type>) {
    let Some(wid) = world_id else {
        return (ty.clone(), None);
    };
    let Type::Tuple(items) = ty else {
        return (ty.clone(), None);
    };
    let Some(last) = items.last() else {
        return (ty.clone(), None);
    };
    let is_world = matches!(
        last,
        Type::Struct { struct_id, type_args } if *struct_id == wid && type_args.is_empty()
    );
    if !is_world {
        return (ty.clone(), None);
    }
    let world_ty = last.clone();
    let head: Vec<Type> = items[..items.len() - 1].to_vec();
    let stripped = if head.is_empty() {
        Type::Unit
    } else {
        Type::Tuple(head)
    };
    (stripped, Some(world_ty))
}

/// Re-append the (stage-4) trailing World slot to a stage-3-augmented
/// return type, matching stage 4's `augment_return_type_with_world`
/// shape rules.
fn reapply_trailing_world(ty: Type, world_ty: Type) -> Type {
    match ty {
        Type::Unit => Type::Tuple(vec![world_ty]),
        Type::Tuple(mut items) => {
            items.push(world_ty);
            Type::Tuple(items)
        }
        other => Type::Tuple(vec![other, world_ty]),
    }
}

/// The stage-4-ghost return-slot value types for `fid`, in the order the
/// ghost stage appends them (the `V` of each `(K, V)` in
/// `program.ghost_vars[fid]`, sorted by marker struct id upstream). Empty
/// when the function threads no ghost vars.
fn ghost_return_types(program: &Program, fid: FunId) -> Vec<Type> {
    program
        .ghost_vars
        .get(&fid)
        .map(|vars| vars.iter().map(|(_, v)| v.clone()).collect())
        .unwrap_or_default()
}

/// Return `(stripped, Some(ghost_tys))` if `ty` is a `Type::Tuple` whose
/// trailing `ghost_vs.len()` elements equal `ghost_vs` as a contiguous
/// block; otherwise `(ty, None)`.
///
/// Stage 4g appends these slots *after* the trailing World slot (see
/// `stage_04_ghost`). The stage-3 signature-shape check, re-run as a
/// render-time invariant, must peel them (then the World slot) before
/// recovering the stage-3 augmented shape underneath. The full-sequence
/// tail match is what makes this safe to run at every stage: before the
/// ghost stage has appended them the tail ends in a mut ref (stage 3) or
/// the World struct (stage 4), never the ghost value sequence.
///
/// Mirrors `strip_trailing_world`'s always-Tuple result rule: the
/// stripped form stays a `Type::Tuple` (or `Type::Unit` when the head is
/// empty), preserving stage 3's always-Tuple invariant.
fn strip_trailing_ghosts(ty: &Type, ghost_vs: &[Type]) -> (Type, Option<Vec<Type>>) {
    if ghost_vs.is_empty() {
        return (ty.clone(), None);
    }
    let Type::Tuple(items) = ty else {
        return (ty.clone(), None);
    };
    if items.len() < ghost_vs.len() {
        return (ty.clone(), None);
    }
    let split = items.len() - ghost_vs.len();
    if &items[split..] != ghost_vs {
        return (ty.clone(), None);
    }
    let head: Vec<Type> = items[..split].to_vec();
    let stripped = if head.is_empty() {
        Type::Unit
    } else {
        Type::Tuple(head)
    };
    (stripped, Some(ghost_vs.to_vec()))
}

/// Re-append the (stage-4-ghost) trailing return slots to a
/// stage-3-augmented (optionally world-augmented) return type, matching
/// stage 4g's `augment_return_type_with_ghosts` shape rules. Used only to
/// reconstruct the `expected` type for a genuine violation's error.
fn reapply_trailing_ghosts(ty: Type, ghost_tys: Vec<Type>) -> Type {
    if ghost_tys.is_empty() {
        return ty;
    }
    match ty {
        Type::Unit => Type::Tuple(ghost_tys),
        Type::Tuple(mut items) => {
            items.extend(ghost_tys);
            Type::Tuple(items)
        }
        other => {
            let mut items = vec![other];
            items.extend(ghost_tys);
            Type::Tuple(items)
        }
    }
}

/// Stage-3 postcondition errors.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PostconditionError {
    /// Base IR validator rejected the program.
    BaseValidator(ValidationError),
    /// Lingering `Stmt::Eval(WriteRef ..)`.
    LingeringWriteRefEval { function: FunId },
    /// Lingering `Stmt::Eval(WriteBack ..)`.
    LingeringWriteBackEval { function: FunId },
    /// A function with `&mut` params has a return type that doesn't
    /// match the augmented shape.
    SignatureReturnNotAugmented {
        function: FunId,
        expected: Type,
        actual: Type,
    },
    /// A `Stmt::Eval(Call(f, ..))` survives where `f` has `&mut` params.
    /// The call must be in `Stmt::Let { value: Call .. }` so the
    /// destructure picks up the augmented return.
    UnaugmentedCallEval { function: FunId, callee: FunId },
    /// A `Stmt::Let { pattern, value: Call(f, ..) }` has a pattern
    /// whose length doesn't match the callee's render-time augmented
    /// return arity. Indicates call_augment didn't extend the pattern
    /// (or extended it incorrectly).
    CallPatternArityMismatch {
        function: FunId,
        callee: FunId,
        pattern_len: usize,
        expected_arity: usize,
    },
}

impl From<ValidationError> for PostconditionError {
    fn from(e: ValidationError) -> Self {
        PostconditionError::BaseValidator(e)
    }
}

/// Run the stage-3-local postcondition checks.
pub fn check(program: &Program) -> Result<(), PostconditionError> {
    // Pre-compute callee info per function for caller-side checks.
    // Includes both translated functions and native declarations:
    // call sites may resolve to either, and the caller-side body
    // check needs the callee's mut-arity in both cases.
    //
    // `world_id` is the synthetic World struct id if stage 4 has
    // already registered it. When present, the signature-shape check
    // (check 4) strips a trailing World slot from `signature.return_type`
    // before comparing against the stage-3 augmented form -- stage 4
    // appends `World` to every Impure function's return tuple, which
    // is fine for the stage-3 invariant as long as the rest of the
    // tuple is still in the stage-3 augmented shape.
    let world_id = find_world_struct_id(program);
    let mut callee_has_muts: BTreeMap<FunId, bool> = BTreeMap::new();
    let mut callee_arities: BTreeMap<FunId, usize> = BTreeMap::new();
    for (fid, f) in &program.functions {
        callee_has_muts.insert(*fid, has_mut_params_sig(&f.signature));
        callee_arities.insert(*fid, render_time_arity_sig(&f.signature, world_id));
    }
    for (fid, d) in &program.natives.decls {
        callee_has_muts.insert(*fid, has_mut_params_sig(&d.signature));
        callee_arities.insert(*fid, render_time_arity_sig(&d.signature, world_id));
    }

    for (&fid, func) in &program.functions {
        // Synthesized functions stage 3 never saw. Stage 7 extracts
        // `LoopBody` / `LoopAfter` helpers from while-loops, `Spec`
        // (aborts/requires/ensures) companions from source bodies, and
        // `Synthetic` continuations (`*.cont_N`, labeled-block
        // helpers); each follows its own body- and signature-shape
        // convention, enforced by the stage-7 / stage-8 invariants, not
        // this one.
        let is_post_stage3_synthetic = matches!(
            func.kind,
            crate::ir::FunctionKind::LoopBody { .. }
                | crate::ir::FunctionKind::LoopAfter { .. }
                | crate::ir::FunctionKind::Spec { .. }
                | crate::ir::FunctionKind::Synthetic
                | crate::ir::FunctionKind::Theorem { .. }
                | crate::ir::FunctionKind::Axiom { .. },
        );

        // Checks 2, 3, 5, 6: walk body for forbidden Stmt::Eval shapes
        // and validate Stmt::Let pattern arity at call sites. The
        // unaugmented-mut-eval check (5) is exempted for the synthesized
        // kinds above: a `Spec(Aborts)` companion legitimately `eval`s a
        // `&mut` call whose writeback is dead (the companion returns
        // AbortResult, not the threaded values), and the call's abort is
        // already covered by the preceding `<callee>.aborts` check. The
        // lingering-writeref / writeback checks still apply.
        check_body(
            fid,
            &func.body,
            &callee_has_muts,
            &callee_arities,
            is_post_stage3_synthetic,
        )?;

        // Check 4: signature return-type matches augmented shape.
        // Skipped for the synthesized kinds (their signature shape --
        // loop-state subset of mut params, target-shape mirror for
        // specs -- is not the stage-3 augmented form).
        if is_post_stage3_synthetic {
            continue;
        }
        let muts = mut_param_info(func);
        if !muts.is_empty() {
            let actual = func.signature.return_type.clone();
            // Peel the later stages' trailing return slots before
            // recovering the stage-3 augmented shape underneath. Stage 4g
            // (ghost) appends its slots AFTER the stage-4 World slot, so
            // strip ghosts first, then World. The stage-3 signature-shape
            // promise applies to what's left.
            let ghost_vs = ghost_return_types(program, fid);
            let (after_ghosts, ghost_tys) = strip_trailing_ghosts(&actual, &ghost_vs);
            let (stripped_actual, world_ty) = strip_trailing_world(&after_ghosts, world_id);
            let expected_inner = expected_augmented_return(&stripped_actual, &muts);
            if stripped_actual != expected_inner {
                let expected_world = match world_ty {
                    Some(wt) => reapply_trailing_world(expected_inner, wt),
                    None => expected_inner,
                };
                let expected = match ghost_tys {
                    Some(gts) => reapply_trailing_ghosts(expected_world, gts),
                    None => expected_world,
                };
                return Err(PostconditionError::SignatureReturnNotAugmented {
                    function: fid,
                    expected,
                    actual,
                });
            }
        }
    }
    Ok(())
}

/// Compute the augmented return arity for a function. The arity is
/// the destructure-pattern length the caller uses for this call. After
/// stage 3, that's `orig_items + mut_count` (the augmented tuple
/// shape). After stage 4 has further augmented Impure callees with a
/// trailing `World` slot, the caller also threads world via a slot in
/// the destructure pattern, so the arity grows by one accordingly. In
/// both cases the arity is simply the tuple-length of
/// `signature.return_type`.
fn render_time_arity_sig(sig: &crate::ir::Signature, _world_id: Option<StructId>) -> usize {
    match &sig.return_type {
        Type::Tuple(items) => items.len(),
        Type::Unit => 0,
        _ => 1,
    }
}

fn has_mut_params_sig(sig: &crate::ir::Signature) -> bool {
    sig.params
        .iter()
        .any(|p| matches!(p.ty, Type::MutableRef { .. }))
}

/// Compute what the augmented return type SHOULD be for a function
/// whose current return type is `current`. This is a fixed-point check:
/// if the current already matches the augmented shape (which it should
/// after Transform 4), `expected == current`.
///
/// Algorithm: recover the original return type by stripping the
/// trailing mut elements from the current type, then re-augment.
fn expected_augmented_return(current: &Type, muts: &[MutParam]) -> Type {
    let orig = recover_original_return(current, muts);
    augment_return_type(orig, muts)
}

/// Recover the original return type by stripping `muts.len()` trailing
/// elements that match the mut param types from the augmented Tuple.
///
/// Per the always-Tuple invariant, the augmented form is always
/// `Type::Tuple([head..., mut_types...])`. Strip the trailing N
/// elements; the remaining `head_count` items become the original
/// return:
/// - `head_count == 0` -> `Type::Unit`
/// - `head_count == 1` -> the singleton head element
/// - `head_count >= 2` -> `Type::Tuple(head)`
fn recover_original_return(current: &Type, muts: &[MutParam]) -> Type {
    if muts.is_empty() {
        return current.clone();
    }
    match current {
        Type::Tuple(items) if items.len() >= muts.len() => {
            let head_count = items.len() - muts.len();
            let trail_matches = items[head_count..]
                .iter()
                .zip(muts.iter())
                .all(|(t, m)| t == &m.mut_ref_type);
            if !trail_matches {
                return current.clone();
            }
            match head_count {
                0 => Type::Unit,
                1 => items[0].clone(),
                _ => Type::Tuple(items[..head_count].to_vec()),
            }
        }
        _ => current.clone(),
    }
}

fn check_body(
    fid: FunId,
    body: &Block,
    callee_muts: &BTreeMap<FunId, bool>,
    callee_arities: &BTreeMap<FunId, usize>,
    exempt_mut_eval: bool,
) -> Result<(), PostconditionError> {
    for stmt in &body.stmts {
        check_stmt(fid, stmt, callee_muts, callee_arities, exempt_mut_eval)?;
    }
    check_tail(
        fid,
        &body.tail,
        callee_muts,
        callee_arities,
        exempt_mut_eval,
    )
}

fn check_stmt(
    fid: FunId,
    stmt: &Stmt,
    callee_muts: &BTreeMap<FunId, bool>,
    callee_arities: &BTreeMap<FunId, usize>,
    exempt_mut_eval: bool,
) -> Result<(), PostconditionError> {
    match stmt {
        Stmt::Eval(Expr::WriteRef { .. }) => {
            Err(PostconditionError::LingeringWriteRefEval { function: fid })
        }
        Stmt::Eval(Expr::WriteBack { node, .. }) => {
            // SpecGlobalRoot writebacks have no local rebind target;
            // `rewrite_write_backs` leaves them as `Stmt::Eval(WriteBack { SpecGlobalRoot, .. })`
            // for the renderer's `writeBackSpecGlobal` stub. Allow them
            // through; reject only `LocalRoot` / `Reference` shapes,
            // which should have been rewritten by stage 3.
            match node {
                crate::ir::BorrowNode::SpecGlobalRoot { .. } => Ok(()),
                _ => Err(PostconditionError::LingeringWriteBackEval { function: fid }),
            }
        }
        Stmt::Eval(Expr::Call { fun, .. }) => {
            if !exempt_mut_eval && callee_muts.get(fun).copied().unwrap_or(false) {
                Err(PostconditionError::UnaugmentedCallEval {
                    function: fid,
                    callee: *fun,
                })
            } else {
                Ok(())
            }
        }
        Stmt::Let {
            pattern,
            value: Expr::Call { fun, .. },
        } => {
            // Check 6: pattern arity matches render-time augmented return arity.
            if callee_muts.get(fun).copied().unwrap_or(false) {
                let expected = callee_arities.get(fun).copied().unwrap_or(0);
                if pattern.len() != expected {
                    return Err(PostconditionError::CallPatternArityMismatch {
                        function: fid,
                        callee: *fun,
                        pattern_len: pattern.len(),
                        expected_arity: expected,
                    });
                }
            }
            Ok(())
        }
        Stmt::Eval(other) => check_expr(fid, other, callee_muts, callee_arities, exempt_mut_eval),
        Stmt::Let { value, .. } => {
            check_expr(fid, value, callee_muts, callee_arities, exempt_mut_eval)
        }
    }
}

fn check_tail(
    fid: FunId,
    tail: &BlockTail,
    callee_muts: &BTreeMap<FunId, bool>,
    callee_arities: &BTreeMap<FunId, usize>,
    exempt_mut_eval: bool,
) -> Result<(), PostconditionError> {
    match tail {
        BlockTail::Value(e) => check_expr(fid, e, callee_muts, callee_arities, exempt_mut_eval),
        BlockTail::Break { value, .. }
        | BlockTail::Continue { value, .. }
        | BlockTail::Return(value)
        | BlockTail::ReturnFromBlock { value, .. } => {
            check_expr(fid, value, callee_muts, callee_arities, exempt_mut_eval)
        }
        BlockTail::Abort { code } => {
            check_expr(fid, code, callee_muts, callee_arities, exempt_mut_eval)
        }
    }
}

fn check_expr(
    fid: FunId,
    expr: &Expr,
    callee_muts: &BTreeMap<FunId, bool>,
    callee_arities: &BTreeMap<FunId, usize>,
    exempt_mut_eval: bool,
) -> Result<(), PostconditionError> {
    match expr {
        Expr::If {
            cond,
            then_branch,
            else_branch,
        } => {
            check_expr(fid, cond, callee_muts, callee_arities, exempt_mut_eval)?;
            check_body(
                fid,
                then_branch,
                callee_muts,
                callee_arities,
                exempt_mut_eval,
            )?;
            check_body(
                fid,
                else_branch,
                callee_muts,
                callee_arities,
                exempt_mut_eval,
            )
        }
        Expr::Match {
            selector, cases, ..
        } => {
            check_expr(fid, selector, callee_muts, callee_arities, exempt_mut_eval)?;
            for MatchArm { body, .. } in cases {
                check_body(fid, body, callee_muts, callee_arities, exempt_mut_eval)?;
            }
            Ok(())
        }
        Expr::While {
            header, cond, body, ..
        } => {
            check_body(fid, header, callee_muts, callee_arities, exempt_mut_eval)?;
            check_expr(fid, cond, callee_muts, callee_arities, exempt_mut_eval)?;
            check_body(fid, body, callee_muts, callee_arities, exempt_mut_eval)
        }
        Expr::Quantifier { body, .. } => {
            check_body(fid, body, callee_muts, callee_arities, exempt_mut_eval)
        }
        Expr::LabeledBlock { body, .. } => {
            check_body(fid, body, callee_muts, callee_arities, exempt_mut_eval)
        }
        _ => Ok(()),
    }
}
