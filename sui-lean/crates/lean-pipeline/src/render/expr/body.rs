//! Function-body / statement rendering (split from `expr/mod.rs`,
//! `plans/lean-pipeline/renderer-split.md`).

use super::*;
use crate::ir::analysis::type_of::strip_singleton_tuple;
use crate::ir::{Block, BlockTail, Expr, MatchArm, Stmt, VarId};
use crate::render::escape;
use crate::render::writer::LeanWriter;
use crate::render::{RenderError, RenderResult};
use std::fmt::Write;

/// Render `block` as a function body. `block.tail` becomes the
/// terminal expression; `Return(v)` at the function body's outermost
/// tail is collapsed to `v`. Other terminator tails are rejected.
pub(in crate::render) fn render_function_body<W: Write>(
    block: &Block,
    ctx: &ExprCtx<'_>,
    w: &mut LeanWriter<W>,
) -> RenderResult<()> {
    // Cosmetic peephole: detect `[..., let v := X]; Value(Var(v))`
    // where `v` is used exactly once (the tail). Drop the trailing
    // Let and use `X` as the tail expression. Stage 5 (SSA) +
    // stage 6's single-use inliner would handle this for pure-total
    // values, but partial arithmetic (`a + b` on UInt) is PurePartial
    // and stage 6 leaves it bound. Inlining it at the tail is sound
    // -- the abort happens at the same point either way -- and
    // produces much more readable Lean.
    // Loop: a `[..., let v := X]; Value(Var(v))` rewrite to
    // `[...]; Value(X)` exposes the new tail as a fresh candidate
    // when X is itself a Var. Re-run peephole to collapse copy chains.
    let mut cur_stmts: Vec<Stmt> = block.stmts.clone();
    let mut cur_tail: BlockTail = block.tail.clone();
    loop {
        match try_peephole_tail_let(&cur_stmts, &cur_tail) {
            Some((ns, nt)) => {
                cur_stmts = ns;
                cur_tail = nt;
            }
            None => break,
        }
    }
    for stmt in &cur_stmts {
        render_stmt(stmt, ctx, w)?;
        w.newline();
    }
    render_function_tail(&cur_tail, ctx, w)
}

pub(in crate::render) fn try_peephole_tail_let(
    stmts: &[Stmt],
    tail: &BlockTail,
) -> Option<(Vec<Stmt>, BlockTail)> {
    let last = stmts.last()?;
    let (var, value) = match last {
        Stmt::Let { pattern, value } if pattern.len() == 1 => match &pattern[0] {
            Some(v) => (v.clone(), value.clone()),
            None => return None,
        },
        _ => return None,
    };
    match tail {
        BlockTail::Value(Expr::Var(v)) if v == &var => {}
        _ => return None,
    }
    // Defensive: ensure `var` isn't referenced in any earlier stmt
    // (would change semantics if inlined).
    for s in stmts.iter().rev().skip(1) {
        if stmt_references_var(s, &var) {
            return None;
        }
    }
    Some((stmts[..stmts.len() - 1].to_vec(), BlockTail::Value(value)))
}

pub(in crate::render) fn stmt_references_var(s: &Stmt, target: &VarId) -> bool {
    match s {
        Stmt::Let { value, .. } => expr_references_var(value, target),
        Stmt::Eval(e) => expr_references_var(e, target),
    }
}

pub(in crate::render) fn expr_references_var(e: &Expr, target: &VarId) -> bool {
    match e {
        Expr::Borrow { step, base } => {
            step.exprs().any(|__pe| expr_references_var(__pe, target))
                || expr_references_var(base, target)
        }
        Expr::Update { step, base, value } => {
            step.exprs().any(|__pe| expr_references_var(__pe, target))
                || expr_references_var(base, target)
                || expr_references_var(value, target)
        }
        Expr::Var(v) => v == target,
        Expr::Const(_)
        | Expr::Unit
        | Expr::BorrowLoc(_)
        | Expr::BorrowGlobal(_)
        | Expr::WriteBack { .. }
        | Expr::IsParent { .. } => false,
        Expr::BinOp { lhs, rhs, .. } => {
            expr_references_var(lhs, target) || expr_references_var(rhs, target)
        }
        Expr::UnOp { operand, .. } => expr_references_var(operand, target),
        Expr::BitOp(op) => match op {
            crate::ir::BitOp::Extract { operand, .. }
            | crate::ir::BitOp::ZeroExtend { operand, .. }
            | crate::ir::BitOp::SignExtend { operand, .. } => expr_references_var(operand, target),
            crate::ir::BitOp::Concat { high, low } => {
                expr_references_var(high, target) || expr_references_var(low, target)
            }
        },
        Expr::Call { args, .. } => args.iter().any(|a| expr_references_var(a, target)),
        Expr::Tuple(es) | Expr::Pack { fields: es, .. } => {
            es.iter().any(|x| expr_references_var(x, target))
        }
        Expr::Unpack { value, .. }
        | Expr::Field { base: value, .. }
        | Expr::ReadRef(value)
        | Expr::ToProp(value)
        | Expr::ToBool(value) => expr_references_var(value, target),
        Expr::If {
            cond,
            then_branch,
            else_branch,
        } => {
            expr_references_var(cond, target)
                || block_references_var(then_branch, target)
                || block_references_var(else_branch, target)
        }
        Expr::Match {
            selector, cases, ..
        } => {
            expr_references_var(selector, target)
                || cases.iter().any(|c| block_references_var(&c.body, target))
        }
        Expr::While {
            header,
            cond,
            body,
            iter_locals,
            header_exit_locals: _,
            live_out: _,
        } => {
            iter_locals
                .iter()
                .any(|(_, e)| expr_references_var(e, target))
                || block_references_var(header, target)
                || expr_references_var(cond, target)
                || block_references_var(body, target)
        }
        Expr::WriteRef { reference, value } => {
            expr_references_var(reference, target) || expr_references_var(value, target)
        }
        Expr::Quantifier { domain, body, .. } => {
            use crate::ir::QuantDomain;
            let d = match domain {
                QuantDomain::Unbounded => false,
                QuantDomain::Range { start, end } => {
                    expr_references_var(start, target) || expr_references_var(end, target)
                }
                QuantDomain::VecRange { vec, start, end } => {
                    expr_references_var(vec, target)
                        || expr_references_var(start, target)
                        || expr_references_var(end, target)
                }
                QuantDomain::Collection(c) => expr_references_var(c, target),
            };
            d || block_references_var(body, target)
        }
        Expr::LabeledBlock { .. } => {
            unreachable!("Expr::LabeledBlock should be eliminated by stage 7 helper extraction")
        }
    }
}

pub(in crate::render) fn block_references_var(b: &Block, target: &VarId) -> bool {
    for s in &b.stmts {
        if stmt_references_var(s, target) {
            return true;
        }
    }
    match &b.tail {
        BlockTail::Value(e) => expr_references_var(e, target),
        BlockTail::Return(e) | BlockTail::Abort { code: e } => {
            expr_references_var(e.as_ref(), target)
        }
        BlockTail::Break { value, .. } | BlockTail::Continue { value, .. } => {
            expr_references_var(value.as_ref(), target)
        }
        BlockTail::ReturnFromBlock { .. } => unreachable!(
            "BlockTail::ReturnFromBlock should be eliminated by stage 7 helper extraction"
        ),
    }
}

pub(in crate::render) fn render_function_tail<W: Write>(
    tail: &BlockTail,
    ctx: &ExprCtx<'_>,
    w: &mut LeanWriter<W>,
) -> RenderResult<()> {
    match tail {
        BlockTail::Value(e) => render_tail_value_coerced(e, ctx, w),
        // Collapse outermost Return(v) -> v. Stage 7 will do this
        // systematically; until then, we accept it here as a
        // syntactic special case. Use `render_tail_value_coerced`
        // (not bare `render_expr`) so the function-return-type
        // tuple coercion fires for Return tails too -- otherwise
        // any function whose body ends in `Return(Tuple([...]))`
        // (which the stage 3 / 4 augmentation produces for Impure
        // functions returning &mut params + world) bypasses the
        // augmented-return value-form -> Mutation slot wrap and
        // Lean rejects the body at the function-return-type
        // boundary.
        BlockTail::Return(v) => render_tail_value_coerced(v, ctx, w),
        BlockTail::ReturnFromBlock { value, .. } => render_tail_value_coerced(value, ctx, w),
        BlockTail::Abort { .. } => {
            // Function body that aborts: emit `default`. The `.aborts`
            // companion (generated by stage 7's `spec_extract`) carries
            // the abort condition; the regular body's value at the abort
            // path is never consumed by the test runner (drivers gate on
            // `f.aborts(world)` before evaluating `f(world)` itself). So
            // emitting `default` rather than `sorry` is semantically
            // equivalent here AND has the practical benefit of not
            // panicking the Lean runtime when `make_self_contained_aborts_body`
            // hoists let-bindings past their original `if`-guards in the
            // .aborts companion -- those evaluations now call regular
            // function bodies whose abort tails would have crashed on
            // `sorry`. See `cetus-stl-stage-d-borrow-mut-handoff.md`.
            write_abort_tail_default(ctx.function_return_type, ctx, w);
            Ok(())
        }
        BlockTail::Break { .. } => Err(RenderError::UnsupportedConstruct {
            what: "BlockTail::Break (post-stage-7 invariant violation)",
        }),
        BlockTail::Continue { .. } => Err(RenderError::UnsupportedConstruct {
            what: "BlockTail::Continue (post-stage-7 invariant violation)",
        }),
    }
}

/// Emit an aborting tail's value. Normally `default`, but for a function
/// returning a tuple ending in `World`, emit `(default, .., world)` --
/// forwarding the trailing `world` param rather than synthesizing an
/// EMPTY `default` World. Rationale: a `.aborts` companion threads the
/// REGULAR body's returned world (`let (_, .., world') := f(..)`), so an
/// abort branch reached inside the companion's execution (e.g. via a
/// model divergence -- cetus-dlmm `bin::remove_group`'s `else abort`
/// when a stale `used_bins_mask` survives a lossy df writeback) would
/// otherwise WIPE every prior df entry / shared object in the threaded
/// world. Mirrors function.rs's native-stub world preservation.
pub(in crate::render) fn write_abort_tail_default<W: Write>(
    expected: Option<&crate::ir::Type>,
    ctx: &ExprCtx<'_>,
    w: &mut LeanWriter<W>,
) {
    if let (Some(crate::ir::Type::Tuple(parts)), Some(wp)) = (expected, ctx.world_param.as_deref())
    {
        let ends_in_world = parts.last().map_or(false, |t| {
            let s = ctx.type_to_string(t);
            s == "World"
                || s.starts_with("Prover.World.World ")
                || s.starts_with("(Prover.World.World ")
        });
        if ends_in_world {
            w.write("(");
            let n = parts.len();
            for i in 0..n {
                if i > 0 {
                    w.write(", ");
                }
                if i == n - 1 {
                    w.write(wp);
                } else {
                    w.write("default");
                }
            }
            w.write(")");
            return;
        }
    }
    w.write("default");
}

/// Render a function body's tail value, applying the augmented-return
/// type bridge when the expression is a tuple whose elements don't
/// match the function's declared return-tuple shape at the Mutation
/// level. Specifically: when the function returns `Type::Tuple([T0,
/// ..., Tn])` where some `Ti = MutableRef U`, but the tail tuple
/// element at position `i` is a value-form `U` (e.g. a destructured
/// slot from a native call whose return was stripped via
/// `strip_mutable_ref_in_type`), wrap with `Prover.Mutation.Mutation.ofLocal
/// 0 e_i`. This bridges the gap between the IR-level augmented return
/// (Mutation) and the hand-written natives' value-form return.
///
/// Non-tuple tails fall through to the regular `render_expr`.
pub(in crate::render) fn render_tail_value_coerced<W: Write>(
    e: &Expr,
    ctx: &ExprCtx<'_>,
    w: &mut LeanWriter<W>,
) -> RenderResult<()> {
    // Descend into `Expr::If` / `Expr::Match` so the coercion fires
    // on every branch's tail tuple, not just the outermost function
    // tail. Common shape: `fun ... = if cond then (a, b, c) else
    // sorry` where the function returns `(Mutation A, Mutation B, C)`
    // but `b` is a value-form slot. Without descending, the tail
    // is `Expr::If(...)`, not a tuple, and the coercion falls
    // through to plain `render_expr`. Descending hands each arm
    // its own coercion context.
    match e {
        Expr::If {
            cond,
            then_branch,
            else_branch,
        } => {
            w.write("if ");
            render_expr(cond, ctx, w)?;
            w.write(" then");
            w.indent(true);
            render_function_tail_arm(then_branch, ctx, w)?;
            w.dedent(false);
            w.newline();
            w.write("else");
            w.indent(true);
            render_function_tail_arm(else_branch, ctx, w)?;
            w.dedent(false);
            return Ok(());
        }
        Expr::Match {
            struct_id,
            selector,
            cases,
        } => {
            return render_match_coerced(*struct_id, selector, cases, ctx, w);
        }
        _ => {}
    }
    let expected_tuple_tys = match (ctx.function_return_type, e) {
        (Some(crate::ir::Type::Tuple(ts)), Expr::Tuple(elems)) if ts.len() == elems.len() => {
            Some(ts.clone())
        }
        _ => None,
    };
    let Some(expected_tys) = expected_tuple_tys else {
        return render_expr(e, ctx, w);
    };
    let Expr::Tuple(elems) = e else {
        unreachable!()
    };
    w.write("(");
    for (i, elem) in elems.iter().enumerate() {
        if i > 0 {
            w.write(", ");
        }
        let expected = &expected_tys[i];
        if needs_mutation_wrap(elem, expected, ctx) {
            render_in_form(
                elem,
                ExpectedForm::Mutation {
                    value_target: None,
                    slot: MutationSlot::Fixed(0),
                },
                ExprSyntax::Inline,
                ExprSyntax::Inline,
                ctx,
                w,
            )?;
        } else {
            render_expr(elem, ctx, w)?;
        }
    }
    w.write(")");
    Ok(())
}

fn render_function_tail_arm<W: Write>(
    block: &Block,
    ctx: &ExprCtx<'_>,
    w: &mut LeanWriter<W>,
) -> RenderResult<()> {
    if let Some(target) = ctx.function_return_type {
        let can_target = {
            let var_types = ctx.var_types.borrow();
            block_can_render_as_type(block, target, ctx.program, &var_types)
        };
        if can_target {
            return render_inner_block_with_target_ty(block, target, ctx, w);
        }
    }
    render_inner_block_coerced(block, ctx, w)
}

fn render_inner_block_coerced<W: Write>(
    block: &Block,
    ctx: &ExprCtx<'_>,
    w: &mut LeanWriter<W>,
) -> RenderResult<()> {
    for stmt in &block.stmts {
        if is_erased_inner_discard(stmt) {
            continue;
        }
        render_stmt(stmt, ctx, w)?;
        w.newline();
    }
    match &block.tail {
        BlockTail::Value(expression) => render_tail_value_coerced(expression, ctx, w),
        BlockTail::Abort { .. } => {
            write_abort_tail_default(ctx.function_return_type, ctx, w);
            Ok(())
        }
        BlockTail::Return(_) => Err(RenderError::UnsupportedConstruct {
            what: "inner BlockTail::Return (post-stage-7 invariant violation)",
        }),
        BlockTail::Break { .. } => Err(RenderError::UnsupportedConstruct {
            what: "BlockTail::Break (post-stage-7 invariant violation)",
        }),
        BlockTail::Continue { .. } => Err(RenderError::UnsupportedConstruct {
            what: "BlockTail::Continue (post-stage-7 invariant violation)",
        }),
        BlockTail::ReturnFromBlock { .. } => unreachable!(
            "BlockTail::ReturnFromBlock should be eliminated by stage 7 helper extraction"
        ),
    }
}

/// Render a function-tail match, applying the declared return target to each
/// arm when the renderer can realize that coercion structurally.
pub(in crate::render) fn render_match_coerced<W: Write>(
    struct_id: crate::ir::StructId,
    selector: &Expr,
    cases: &[MatchArm],
    ctx: &ExprCtx<'_>,
    w: &mut LeanWriter<W>,
) -> RenderResult<()> {
    let struct_def = ctx
        .program
        .structs
        .get(&struct_id)
        .ok_or(RenderError::UnknownStructId { id: struct_id })?;
    if struct_def.variants.is_none() {
        return Err(RenderError::MatchOnNonEnum { id: struct_id });
    }
    let selector_type_args = match_selector_type_args(struct_id, selector, ctx);
    w.write("match ");
    render_expr(selector, ctx, w)?;
    w.write(" with");
    w.indent(true);
    for arm in cases {
        let v = struct_def
            .variant_by_tag(arm.variant)
            .ok_or(RenderError::UnknownVariant {
                struct_id,
                variant: arm.variant,
            })?;
        w.write("| .");
        w.write(&escape::escape_identifier(&v.name));
        for b in &arm.bindings {
            w.write(" ");
            w.write(&escape::escape_identifier(b));
        }
        w.write(" =>");
        w.indent(true);
        let result = with_match_arm_binding_types(
            &arm.bindings,
            &v.fields,
            &selector_type_args,
            ctx,
            || render_function_tail_arm(&arm.body, ctx, w),
        );
        w.dedent(false);
        result?;
        w.newline();
    }
    w.dedent(false);
    Ok(())
}

fn render_match_for_eval<W: Write>(
    struct_id: crate::ir::StructId,
    selector: &Expr,
    cases: &[MatchArm],
    ctx: &ExprCtx<'_>,
    w: &mut LeanWriter<W>,
) -> RenderResult<()> {
    let struct_def = ctx
        .program
        .structs
        .get(&struct_id)
        .ok_or(RenderError::UnknownStructId { id: struct_id })?;
    if struct_def.variants.is_none() {
        return Err(RenderError::MatchOnNonEnum { id: struct_id });
    }
    let selector_type_args = match_selector_type_args(struct_id, selector, ctx);
    w.write("match ");
    render_expr(selector, ctx, w)?;
    w.write(" with");
    w.indent(true);
    for arm in cases {
        let variant =
            struct_def
                .variant_by_tag(arm.variant)
                .ok_or(RenderError::UnknownVariant {
                    struct_id,
                    variant: arm.variant,
                })?;
        w.write("| .");
        w.write(&escape::escape_identifier(&variant.name));
        for binding in &arm.bindings {
            w.write(" ");
            w.write(&escape::escape_identifier(binding));
        }
        w.write(" =>");
        w.indent(true);
        let result = with_match_arm_binding_types(
            &arm.bindings,
            &variant.fields,
            &selector_type_args,
            ctx,
            || render_inner_block_for_eval(&arm.body, ctx, w),
        );
        w.dedent(false);
        result?;
        w.newline();
    }
    w.dedent(false);
    Ok(())
}

/// True iff `e`'s inferred type is the inner of `expected = MutableRef
/// { inner, .. }` -- a value-form slot we need to wrap to match the
/// function's declared Mutation return.
pub(in crate::render) fn needs_mutation_wrap(
    e: &Expr,
    expected: &crate::ir::Type,
    ctx: &ExprCtx<'_>,
) -> bool {
    use crate::ir::Type;
    let inner = match expected {
        Type::MutableRef { inner, .. } => inner.as_ref(),
        _ => return false,
    };
    let Some(inferred) = rendered_type_of(e, ctx.program, &ctx.var_types.borrow()) else {
        return false;
    };
    // Already Mutation -- nothing to do.
    if matches!(inferred, Type::MutableRef { .. }) {
        return false;
    }
    // Inferred matches the Mutation's inner exactly.
    effective_types_equal(&inferred, inner)
}

/// Determine whether two `Block`s used as If arms need an explicit target
/// type. A `{Mutation T, T}` mismatch chooses the Mutation form; a terminal
/// abort arm chooses the surviving value arm's type so `default` is emitted
/// with the right context.
///
/// Returns `None` when:
/// - The two arm types are already equal (no coercion needed).
/// - Both arms abort.
/// - A value-arm type is unknown or the known types are incompatible; the
///   render invariant reports those cases before emission.
pub(in crate::render) fn unify_if_arm_types(
    then_branch: &Block,
    else_branch: &Block,
    ctx: &ExprCtx<'_>,
) -> Option<crate::ir::Type> {
    let arm_types = {
        let var_types = ctx.var_types.borrow();
        [
            rendered_block_branch_type(then_branch, ctx.program, &var_types),
            rendered_block_branch_type(else_branch, ctx.program, &var_types),
        ]
    };
    branch_coercion_target(&arm_types).ok().flatten()
}

pub(in crate::render) fn unify_match_arm_types(
    struct_id: crate::ir::StructId,
    selector: &Expr,
    cases: &[MatchArm],
    ctx: &ExprCtx<'_>,
) -> Option<crate::ir::Type> {
    let structure = ctx.program.structs.get(&struct_id)?;
    structure.variants.as_ref()?;
    let base_scope = ctx.var_types.borrow().clone();
    let type_args =
        rendered_match_selector_type_args(struct_id, selector, ctx.program, &base_scope);
    let mut arm_types = Vec::with_capacity(cases.len());
    for arm in cases {
        let variant = structure.variant_by_tag(arm.variant)?;
        let mut arm_scope = base_scope.clone();
        arm_scope.extend(match_arm_binding_types(
            &arm.bindings,
            &variant.fields,
            &type_args,
        ));
        arm_types.push(rendered_block_branch_type(
            &arm.body,
            ctx.program,
            &arm_scope,
        ));
    }
    branch_coercion_target(&arm_types).ok().flatten()
}

/// Render an inner Block with a target tail type. When the block's
/// `Value` tail's inferred type doesn't match `target_ty` AND the
/// mismatch is the `{Mutation T, T}` shape, emit an explicit
/// coercion at the tail: `Mutation.ofLocal` to lift value-form into
/// `Mutation T`, or `.val` to lower `Mutation T` into value form.
/// On any other mismatch, fall back to plain `render_expr` -- the
/// renderer's existing auto-unwrap on call args and field bases
/// handles the rest, and an unfixable mismatch surfaces as a Lean
/// elaboration error (the explicit signal we want).
/// Render `e` so its emitted form has type `target_ty`. Applies
/// scalar `{Mutation T, T}` coercion at the leaf level and recurses
/// into Tuple targets paired with Tuple expressions so each slot
/// gets its own coercion. Also recurses into nested `Expr::If` /
/// `Expr::Match` arms so the target propagates through chains like
/// `if X then if Y then Tuple else Abort else ...`.
pub(in crate::render) fn render_expr_with_target_ty<W: Write>(
    e: &Expr,
    target_ty: &crate::ir::Type,
    ctx: &ExprCtx<'_>,
    w: &mut LeanWriter<W>,
) -> RenderResult<()> {
    use crate::ir::Type;
    // Tuple-target + Tuple-expr: render each slot with its target
    // type. Mirrors the per-slot unification in
    // `unify_arm_value_types`.
    if let (Type::Tuple(target_tys), Expr::Tuple(elems)) = (target_ty, e) {
        if target_tys.len() == elems.len() {
            w.write("(");
            for (i, (slot_target, slot_e)) in target_tys.iter().zip(elems.iter()).enumerate() {
                if i > 0 {
                    w.write(", ");
                }
                render_expr_with_target_ty(slot_e, slot_target, ctx, w)?;
            }
            w.write(")");
            return Ok(());
        }
    }
    // Tuple-expr against a non-Tuple target (or mismatched-arity
    // Tuple target): the program flow at this position is "lost",
    // typically because a stage-7 transformation
    // collapsed an outer function's return shape (e.g. a LoopBody
    // that originally threaded a many-slot loop state but is now
    // emitted with a Bool return type per the .aborts companion
    // derivation). Lean rejects the tuple in non-tuple position
    // with `Type mismatch: (..., ...) has type T1 x T2 x ... but
    // expected ...`. Emit `sorry` (polymorphic bottom) so the
    // surrounding type wins.
    if matches!(e, Expr::Tuple(_)) && !matches!(target_ty, Type::Tuple(_)) {
        w.write("sorry");
        return Ok(());
    }
    // Nested If: propagate the target to each arm so coercion fires
    // on inner Tuple tails.
    if let Expr::If {
        cond,
        then_branch,
        else_branch,
    } = e
    {
        w.write("if ");
        render_expr(cond, ctx, w)?;
        w.write(" then");
        w.indent(true);
        render_inner_block_with_target_ty(then_branch, target_ty, ctx, w)?;
        w.dedent(false);
        w.newline();
        w.write("else");
        w.indent(true);
        render_inner_block_with_target_ty(else_branch, target_ty, ctx, w)?;
        w.dedent(false);
        return Ok(());
    }
    // Nested Match: propagate the target to each case body.
    if let Expr::Match {
        struct_id,
        selector,
        cases,
    } = e
    {
        let struct_def = ctx
            .program
            .structs
            .get(struct_id)
            .ok_or(RenderError::UnknownStructId { id: *struct_id })?;
        if struct_def.variants.is_none() {
            return Err(RenderError::MatchOnNonEnum { id: *struct_id });
        }
        let selector_type_args = match_selector_type_args(*struct_id, selector, ctx);
        w.write("match ");
        render_expr(selector, ctx, w)?;
        w.write(" with");
        w.indent(true);
        for arm in cases {
            let v = struct_def
                .variant_by_tag(arm.variant)
                .ok_or(RenderError::UnknownVariant {
                    struct_id: *struct_id,
                    variant: arm.variant,
                })?;
            w.write("| .");
            w.write(&escape::escape_identifier(&v.name));
            for b in &arm.bindings {
                w.write(" ");
                w.write(&escape::escape_identifier(b));
            }
            w.write(" =>");
            w.indent(true);
            let result = with_match_arm_binding_types(
                &arm.bindings,
                &v.fields,
                &selector_type_args,
                ctx,
                || render_inner_block_with_target_ty(&arm.body, target_ty, ctx, w),
            );
            w.dedent(false);
            result?;
            w.newline();
        }
        w.dedent(false);
        return Ok(());
    }
    let actual = rendered_type_of(e, ctx.program, &ctx.var_types.borrow())
        .map(|ty| strip_singleton_tuple(&ty).clone());
    if matches!(e, Expr::Call { fun, .. } if
        ctx.program
            .functions
            .get(fun)
            .is_some_and(|callee| callee.kind.is_loop_helper()))
        && actual
            .as_ref()
            .is_some_and(|actual| !effective_types_equal(actual, target_ty))
    {
        return Err(RenderError::UnsupportedConstruct {
            what: "mismatched loop-helper handoff (post-stage-7 invariant violation)",
        });
    }
    match (target_ty, actual) {
        (Type::MutableRef { inner, .. }, Some(actual_ty))
            if effective_types_equal(inner, &actual_ty)
                && !matches!(actual_ty, Type::MutableRef { .. }) =>
        {
            render_in_form(
                e,
                ExpectedForm::Mutation {
                    value_target: None,
                    slot: MutationSlot::DerivedFromExpr,
                },
                ExprSyntax::Inline,
                ExprSyntax::Contextual,
                ctx,
                w,
            )
        }
        (t1, Some(Type::MutableRef { inner: i2, .. }))
            if effective_types_equal(i2.as_ref(), t1) =>
        {
            render_in_form(
                e,
                ExpectedForm::Value,
                ExprSyntax::Inline,
                ExprSyntax::Contextual,
                ctx,
                w,
            )
        }
        _ => render_expr(e, ctx, w),
    }
}

pub(in crate::render) fn render_inner_block_with_target_ty<W: Write>(
    block: &Block,
    target_ty: &crate::ir::Type,
    ctx: &ExprCtx<'_>,
    w: &mut LeanWriter<W>,
) -> RenderResult<()> {
    for stmt in &block.stmts {
        if is_erased_inner_discard(stmt) {
            continue;
        }
        render_stmt(stmt, ctx, w)?;
        w.newline();
    }
    match &block.tail {
        BlockTail::Value(e) => render_expr_with_target_ty(e, target_ty, ctx, w),
        BlockTail::Abort { .. } => {
            // See the function-body Abort site for the rationale on
            // `default` rather than `sorry`.
            write_abort_tail_default(Some(target_ty), ctx, w);
            Ok(())
        }
        BlockTail::Return(_) => Err(RenderError::UnsupportedConstruct {
            what: "inner BlockTail::Return (post-stage-7 invariant violation)",
        }),
        BlockTail::Break { .. } => Err(RenderError::UnsupportedConstruct {
            what: "BlockTail::Break (post-stage-7 invariant violation)",
        }),
        BlockTail::Continue { .. } => Err(RenderError::UnsupportedConstruct {
            what: "BlockTail::Continue (post-stage-7 invariant violation)",
        }),
        BlockTail::ReturnFromBlock { .. } => unreachable!(
            "BlockTail::ReturnFromBlock should be eliminated by stage 7 helper extraction"
        ),
    }
}

/// Render an inner Block used by `If` / `Match` arms. Control-flow tails are
/// post-stage-7 invariant failures.
pub(in crate::render) fn render_inner_block<W: Write>(
    block: &Block,
    ctx: &ExprCtx<'_>,
    w: &mut LeanWriter<W>,
) -> RenderResult<()> {
    for stmt in &block.stmts {
        // Skip purely side-effect-free statements: Stmt::Eval and
        // Stmt::Let with an anonymous (`_`) pattern. Our natives
        // and translated functions are pure in Lean, so computing
        // and discarding a value has no observable effect, but the
        // emitted `let _ := X` lines mess with Lean's
        // indentation-sensitive parsing when the surrounding
        // expression is deeply nested (e.g. inside a struct-literal
        // field's value position, where the let-chain's column is
        // shallower than the enclosing `if` keyword and Lean
        // truncates the then-block prematurely).
        if is_erased_inner_discard(stmt) {
            continue;
        }
        render_stmt(stmt, ctx, w)?;
        w.newline();
    }
    match &block.tail {
        BlockTail::Value(e) => render_expr(e, ctx, w),
        BlockTail::Abort { .. } => {
            // See the function-body Abort site for the rationale on
            // `default` rather than `sorry`.
            write_abort_tail_default(None, ctx, w);
            Ok(())
        }
        BlockTail::Return(_) => Err(RenderError::UnsupportedConstruct {
            what: "inner BlockTail::Return (post-stage-7 invariant violation)",
        }),
        BlockTail::Break { .. } => Err(RenderError::UnsupportedConstruct {
            what: "BlockTail::Break (post-stage-7 invariant violation)",
        }),
        BlockTail::Continue { .. } => Err(RenderError::UnsupportedConstruct {
            what: "BlockTail::Continue (post-stage-7 invariant violation)",
        }),
        BlockTail::ReturnFromBlock { .. } => unreachable!(
            "BlockTail::ReturnFromBlock should be eliminated by stage 7 helper extraction"
        ),
    }
}

pub(in crate::render) fn render_stmt<W: Write>(
    stmt: &Stmt,
    ctx: &ExprCtx<'_>,
    w: &mut LeanWriter<W>,
) -> RenderResult<()> {
    match stmt {
        Stmt::Let { pattern, value } => {
            // Peephole: `let v := BorrowLoc(x)` where every use of
            // `v` is `ReadRef(Var(v))` -- the renderer drops the
            // statement entirely and rewrites every `ReadRef(Var(v))`
            // to bare `Var(x)` at the use sites (see `redundant_borrowloc`).
            if let [Some(v)] = pattern.as_slice() {
                if ctx.redundant_borrowloc.contains_key(v) {
                    // Still need to update var_types so downstream
                    // ReadRef redirects pick up the right type, but
                    // we use the underlying source's type.
                    if let Some(src) = ctx.redundant_borrowloc.get(v) {
                        let src_ty = ctx.var_types.borrow().get(src).cloned();
                        if let Some(ty) = src_ty {
                            ctx.var_types.borrow_mut().insert(v.clone(), ty);
                        }
                    }
                    return Ok(());
                }
            }
            // A multi-slot pattern must bind a same-arity tuple. In
            // particular, do not paper over a mismatched stage-7 loop-helper
            // handoff by manufacturing placeholder values for the binders:
            // that would turn invalid IR into well-typed but semantically
            // unrelated Lean.
            if pattern.len() > 1 {
                let inferred_v = rendered_type_of(value, ctx.program, &ctx.var_types.borrow());
                let rhs_is_arity_matched_tuple = matches!(
                    &inferred_v,
                    Some(crate::ir::Type::Tuple(ts)) if ts.len() == pattern.len()
                );
                if !rhs_is_arity_matched_tuple {
                    return Err(RenderError::UnsupportedConstruct {
                        what: "multi-slot let RHS type mismatch (post-stage-7 invariant violation)",
                    });
                }
            }
            w.write("let ");
            render_pattern(pattern, ctx, w);
            w.write(" := ");
            // Propagate var_target_types as a per-slot target tuple
            // when the let-pattern has multiple slots and at least
            // one slot's var has a downstream-driven target type.
            // For each slot: if the slot is a binder with an entry
            // in `var_target_types`, use that as the slot's target;
            // otherwise inherit the inferred type from the RHS
            // (effectively a no-op coercion for that slot).
            let let_target = let_target_type(
                pattern,
                value,
                &ctx.var_target_types,
                ctx.program,
                &ctx.var_types.borrow(),
            );
            let rendered_bindings = rendered_let_bindings(
                pattern,
                value,
                let_target.as_ref(),
                ctx.program,
                &ctx.var_types.borrow(),
            );
            if let Some(target) = &let_target {
                render_expr_with_target_ty(value, target, ctx, w)?;
            } else {
                render_expr(value, ctx, w)?;
            }
            let mut var_types = ctx.var_types.borrow_mut();
            for (var, ty) in rendered_bindings {
                var_types.insert(var, ty);
            }
            Ok(())
        }
        Stmt::Eval(e) => {
            // `let _ := e` is the standard Lean encoding for "evaluate
            // for side effect, drop the value". Plain `e` would leave
            // the value floating in the term.
            //
            // Special-case `If` / `Match` because their branch types
            // must unify; in Move's eval-context Stmt::Eval(If{...})
            // the arms commonly disagree (one arm returns a struct,
            // the other returns Unit). Wrap each arm in eval-discard
            // mode so both produce Unit; then the outer if-expression
            // has type Unit and `let _ := <Unit>` typechecks.
            match e {
                Expr::If {
                    cond,
                    then_branch,
                    else_branch,
                } => {
                    w.write("let _ := if ");
                    render_expr(cond, ctx, w)?;
                    w.write(" then");
                    w.indent(true);
                    render_inner_block_for_eval(then_branch, ctx, w)?;
                    w.dedent(false);
                    w.newline();
                    w.write("else");
                    w.indent(true);
                    render_inner_block_for_eval(else_branch, ctx, w)?;
                    w.dedent(false);
                    Ok(())
                }
                Expr::Match {
                    struct_id,
                    selector,
                    cases,
                } => {
                    w.write("let _ := ");
                    render_match_for_eval(*struct_id, selector, cases, ctx, w)
                }
                _ => {
                    w.write("let _ := ");
                    render_expr(e, ctx, w)?;
                    Ok(())
                }
            }
        }
    }
}

/// Render `block` as if its value were being discarded by an
/// enclosing `Stmt::Eval`. The tail expression is wrapped in
/// `let _ := <tail>` followed by `()` so the block has type Unit
/// regardless of the original tail's type. Recurses into `If`
/// branches so nested if/then/else with arm-type mismatches
/// also flatten to Unit.
pub(in crate::render) fn render_inner_block_for_eval<W: Write>(
    block: &Block,
    ctx: &ExprCtx<'_>,
    w: &mut LeanWriter<W>,
) -> RenderResult<()> {
    for stmt in &block.stmts {
        render_stmt(stmt, ctx, w)?;
        w.newline();
    }
    match &block.tail {
        BlockTail::Value(Expr::Unit) => {
            // Already Unit -- emit directly.
            w.write("()");
            Ok(())
        }
        BlockTail::Value(Expr::If {
            cond,
            then_branch,
            else_branch,
        }) => {
            // Nested If in eval-position: recurse so each arm flattens
            // to Unit. Don't wrap with `let _ :=` -- the outer Eval
            // context already does that, and we want the nested If
            // itself to be a Unit-typed expression.
            w.write("if ");
            render_expr(cond, ctx, w)?;
            w.write(" then");
            w.indent(true);
            render_inner_block_for_eval(then_branch, ctx, w)?;
            w.dedent(false);
            w.newline();
            w.write("else");
            w.indent(true);
            render_inner_block_for_eval(else_branch, ctx, w)?;
            w.dedent(false);
            Ok(())
        }
        BlockTail::Value(Expr::Match {
            struct_id,
            selector,
            cases,
        }) => render_match_for_eval(*struct_id, selector, cases, ctx, w),
        BlockTail::Value(e) => {
            // Force-discard: `let _ := <tail>` then `()`.
            w.write("let _ := ");
            render_expr(e, ctx, w)?;
            w.newline();
            w.write("()");
            Ok(())
        }
        BlockTail::Abort { .. } => {
            // Eval-context: value is discarded. Emit `()` directly --
            // no need to compute a default for a discarded slot. Same
            // rationale as `BlockTail::Value` above, but the abort
            // path means there's nothing to compute.
            w.write("()");
            Ok(())
        }
        BlockTail::Return(_) => Err(RenderError::UnsupportedConstruct {
            what: "inner BlockTail::Return in eval context (post-stage-7 invariant violation)",
        }),
        BlockTail::Break { .. } => Err(RenderError::UnsupportedConstruct {
            what: "BlockTail::Break inside eval-context inner block (post-stage-7 invariant violation)",
        }),
        BlockTail::Continue { .. } => Err(RenderError::UnsupportedConstruct {
            what: "BlockTail::Continue inside eval-context inner block (post-stage-7 invariant violation)",
        }),
        BlockTail::ReturnFromBlock { .. } => unreachable!(
            "BlockTail::ReturnFromBlock should be eliminated by stage 7 helper extraction"
        ),
    }
}

pub(in crate::render) fn render_pattern<W: Write>(
    pattern: &[Option<crate::ir::VarId>],
    ctx: &ExprCtx<'_>,
    w: &mut LeanWriter<W>,
) {
    match pattern.len() {
        0 => panic!("render_pattern: empty pattern (validator should reject)"),
        1 => render_pattern_slot(&pattern[0], ctx, w),
        _ => {
            w.write("(");
            for (i, slot) in pattern.iter().enumerate() {
                if i > 0 {
                    w.write(", ");
                }
                render_pattern_slot(slot, ctx, w);
            }
            w.write(")");
        }
    }
}

pub(in crate::render) fn render_pattern_slot<W: Write>(
    slot: &Option<crate::ir::VarId>,
    ctx: &ExprCtx<'_>,
    w: &mut LeanWriter<W>,
) {
    match slot {
        Some(v) => {
            // Honour `var_overrides` so a param's SSA var (`$t0`)
            // displayed as `q` is rebound under the same display name
            // by `let q := ...`. Without this, stage 3's WriteBack
            // rebindings emit `let t_t0 := ...` while later
            // references to `q` resolve to the un-rebound param.
            if let Some(display) = ctx.var_overrides.get(v) {
                w.write(&escape::escape_identifier(display));
            } else {
                w.write(&escape::escape_identifier(v));
            }
        }
        None => w.write("_"),
    }
}
