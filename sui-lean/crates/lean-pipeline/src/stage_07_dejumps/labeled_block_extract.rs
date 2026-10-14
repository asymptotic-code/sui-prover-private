//! Phase 3a-pre: extract `Expr::LabeledBlock` into helper functions.
//!
//! For each `Stmt::Eval(Expr::LabeledBlock { body, .. })` found in any
//! source-function body (skipping helpers), this pass:
//!
//! 1. Identifies the **result temp** = the last `Stmt::Let { pattern:
//!    [Some(t)], value: V }` immediately before the body's natural-tail
//!    `Value(Unit)`. Removes that stmt; sets the tail to `Value(V)`.
//! 2. Rewrites each inner `BlockTail::ReturnFromBlock { level: 0,
//!    value: V_in }`: if `V_in` is `Unit` AND the preceding stmt is a
//!    `Stmt::Let { value: V_let }`, drops the stmt and emits
//!    `BlockTail::Return(V_let)` (so the helper's exit carries the
//!    actual labeled-return value). If `V_in` is non-Unit, just emits
//!    `BlockTail::Return(V_in)`.
//! 3. Allocates a new helper function (`<parent>.labeled_<N>`) whose
//!    signature takes the body's free vars as params and returns
//!    `result_ty` (the type of `V` from step 1).
//! 4. Replaces the original `Stmt::Eval(LabeledBlock)` with
//!    `Stmt::Let { pattern: [Some(result_temp)], value: Call(helper_id,
//!    free_var_args) }`.
//!
//! Runs BEFORE `loop_extract` so any `Expr::While` inside a
//! LabeledBlock body lands inside the helper, where `loop_extract`
//! then extracts it normally (with the helper's return type now being
//! the result temp's type, not `Unit`).

use std::collections::{BTreeMap, BTreeSet};

use super::Stage7Error;
use crate::ir::analysis::free_vars::free_vars;
use crate::ir::analysis::type_of::type_of;
use crate::ir::expr::{Block, BlockTail, Expr, Stmt};
use crate::ir::function::{
    AbortBit, DetBit, Effects, Function, FunctionKind, MutLevel, Param, Signature,
};
use crate::ir::ty::{Const, Type};
use crate::ir::{FunId, ModId, Program, VarId};

struct ExtractCtx<'p> {
    program: &'p mut Program,
    parent_fid: FunId,
    parent_module: ModId,
    parent_name: String,
    parent_type_params: Vec<String>,
    next_fid: FunId,
    slot_counters: BTreeMap<FunId, u32>,
}

pub fn run(program: &mut Program) -> Result<(), Stage7Error> {
    // Allocate above BOTH functions and natives.decls -- stage 10 (which
    // runs before stage 7) registers synthetic `BoundedU*` natives that
    // share the FunId space; maxing over functions alone could collide
    // with one and overwrite its decl. Every other helper-allocating
    // pass uses the shared function-id namespace; this one must too.
    let mut next_fid: FunId = program.next_function_id();
    let mut slot_counters: BTreeMap<FunId, u32> = BTreeMap::new();

    let fids: Vec<FunId> = program.functions.keys().copied().collect();
    for fid in fids {
        let kind = program.functions[&fid].kind.clone();
        // Process Spec/.aborts companions too. After aborts_variant's
        // RFB-preserve fix, the .aborts labeled_block body's NoAbort
        // arm has `tail: ReturnFromBlock { level: 0, value: Unit }`
        // (instead of `Return(pack NoAbort)`), with the `let $t = V`
        // bound inside the NoAbort arm body. Step 1's
        // `.aborts`-shape branch identifies the result temp from
        // that arm.
        if matches!(
            kind,
            FunctionKind::LoopBody { .. } | FunctionKind::LoopAfter { .. }
        ) {
            continue;
        }
        let parent_module = program.functions[&fid].module;
        let parent_name = program.functions[&fid].name.clone();
        let parent_type_params = program.functions[&fid].signature.type_params.clone();
        let scope: BTreeMap<VarId, Type> = program.functions[&fid]
            .signature
            .params
            .iter()
            .map(|p| (p.var.clone(), p.ty.clone()))
            .collect();

        let mut body = std::mem::replace(
            &mut program.functions.get_mut(&fid).unwrap().body,
            Block {
                stmts: vec![],
                tail: BlockTail::Value(Expr::Unit),
            },
        );
        let mut ctx = ExtractCtx {
            program,
            parent_fid: fid,
            parent_module,
            parent_name,
            parent_type_params,
            next_fid,
            slot_counters,
        };
        process_block(&mut body, &mut ctx, scope)?;
        next_fid = ctx.next_fid;
        slot_counters = ctx.slot_counters;
        ctx.program.functions.get_mut(&fid).unwrap().body = body;
    }
    Ok(())
}

/// Extend `scope` with a `Stmt::Let`'s binding(s). `len()==1` binds the
/// slot to the value's type; a tuple pattern binds each slot to its
/// COMPONENT type (a `&mut`-augmented call returns `(orig, threaded_refs..)`,
/// and without per-slot typing a captured first slot is mistyped as the
/// whole tuple -- cetus-dlmm `reward_settle`'s `any!` loop). A `type_of`
/// failure falls back to `Type::Unit` (the base validator owns the
/// malformedness). Shared by `process_block`'s stmt walk and the
/// `While`-header scope fold so they stay in lockstep.
fn extend_scope_with_let(
    scope: &mut BTreeMap<VarId, Type>,
    pattern: &[Option<VarId>],
    value: &Expr,
    program: &Program,
    parent_name: &str,
) {
    // `process_block` extracts each top-level labeled block INLINE as it
    // walks the spine, so a find-index block's escaping result temp is
    // already bound by `let $tR = <parent>.labeled_N(..)` before the
    // following `let $tC = $tR` copy is typed (this used to be a forward
    // reference -- ika `system_inner::authorize_upgrade` -- and forced a
    // Unit fallback). Every let value is therefore typeable against the
    // scope built so far; a `type_of` failure now signals real
    // malformedness, so assert rather than silently fall back. The
    // enclosing function name is in the message because the usual
    // culprit is a malformed `ReadRef` over a value type reaching here
    // from an upstream stage (see the `NormalizeMode::Early` guard).
    let value_ty = type_of(value, scope, program).unwrap_or_else(|e| {
        panic!(
            "stage-7 scope build in `{parent_name}`: let value must be typeable ({e:?}): {value:?}"
        )
    });
    if pattern.len() == 1 {
        if let Some(v) = &pattern[0] {
            scope.insert(v.clone(), value_ty);
        }
    } else if let Type::Tuple(elem_types) = &value_ty {
        for (slot, ty) in pattern.iter().zip(elem_types.iter()) {
            if let Some(v) = slot {
                scope.insert(v.clone(), ty.clone());
            }
        }
    }
}

fn process_block(
    b: &mut Block,
    ctx: &mut ExtractCtx,
    mut scope: BTreeMap<VarId, Type>,
) -> Result<(), Stage7Error> {
    // Single forward pass: build `scope` from the spine, recurse into
    // nested constructs (so inner LabeledBlocks extract first), and
    // convert each top-level `Stmt::Eval(LabeledBlock)` inline. Doing
    // the extraction inline -- rather than in a separate second pass --
    // means a find-index block's escaping result temp `$tR` is bound by
    // `let $tR = <parent>.labeled_N(..)` BEFORE a following `let $tC =
    // $tR` copy is typed, so the copy types against the helper's real
    // return type instead of falling back to Unit.
    let mut taken = std::mem::take(&mut b.stmts);
    let n = taken.len();
    let mut new_stmts: Vec<Stmt> = Vec::with_capacity(n);
    for i in 0..n {
        let mut s = std::mem::replace(&mut taken[i], Stmt::Eval(Expr::Unit));
        process_stmt(&mut s, ctx, &scope)?;
        match s {
            Stmt::Eval(Expr::LabeledBlock {
                body: lb_body,
                result_ty: _,
            }) => {
                if labeled_block_is_inlinable(&lb_body) {
                    // Degenerate labeled block: its only exit is the
                    // trailing tail, so it is a plain statement
                    // sequence. Inline it -- its inner `Stmt::Let`s
                    // bind function-level temps that later code (the
                    // following loop / return) consumes. Extracting
                    // it into a helper would drop every live-out
                    // binding except the single result temp.
                    let Block {
                        stmts: inner_stmts,
                        tail: inner_tail,
                    } = *lb_body;
                    // Inlining hoists these lets onto the function spine,
                    // so fold each into `scope` as it lands -- later
                    // inner lets AND following statements (`let c = y`)
                    // must see the bindings, exactly as if they had been
                    // written at this level. Without this a following
                    // copy of an inlined temp fails to type.
                    for st in inner_stmts {
                        if let Stmt::Let { pattern, value } = &st {
                            extend_scope_with_let(
                                &mut scope,
                                pattern,
                                value,
                                ctx.program,
                                &ctx.parent_name,
                            );
                        }
                        new_stmts.push(st);
                    }
                    // The labeled block is in statement (Eval)
                    // position, so its value is discarded. Preserve
                    // any side-effecting non-Unit tail as an Eval;
                    // drop a Unit tail outright.
                    let tail_val: Option<Expr> = match inner_tail {
                        BlockTail::Value(e) => Some(e),
                        BlockTail::ReturnFromBlock { value, .. } => Some(*value),
                        _ => None,
                    };
                    if let Some(e) = tail_val {
                        if !matches!(e, Expr::Unit) {
                            new_stmts.push(Stmt::Eval(e));
                        }
                    }
                } else {
                    // Live-out vars: referenced in the statements that
                    // FOLLOW this labeled block (plus the block tail)
                    // but NOT in the outer scope -- so they are bound
                    // inside the labeled block and escape it.
                    // Extracting the block into a helper would drop
                    // them (helper locals don't escape); we thread
                    // them out as extra helper return-tuple elements.
                    let suffix = Block {
                        stmts: taken[i + 1..].to_vec(),
                        tail: b.tail.clone(),
                    };
                    let mut lb_binds: BTreeSet<VarId> = BTreeSet::new();
                    collect_block_binds(&lb_body, &mut lb_binds);
                    let live_out: Vec<VarId> = free_vars(&suffix)
                        .into_iter()
                        .filter(|v| !scope.contains_key(v) && lb_binds.contains(v))
                        .collect();
                    let stmt = extract_one(*lb_body, ctx, &scope, &live_out)?;
                    // Bind the extracted result temp(s) so a following
                    // copy (`let $tC = $tR`) types against the helper's
                    // real return type rather than the old Unit fallback.
                    if let Stmt::Let { pattern, value } = &stmt {
                        extend_scope_with_let(
                            &mut scope,
                            pattern,
                            value,
                            ctx.program,
                            &ctx.parent_name,
                        );
                    }
                    new_stmts.push(stmt);
                }
            }
            Stmt::Let { pattern, value } => {
                extend_scope_with_let(&mut scope, &pattern, &value, ctx.program, &ctx.parent_name);
                new_stmts.push(Stmt::Let { pattern, value });
            }
            other => new_stmts.push(other),
        }
    }
    process_tail(&mut b.tail, ctx, &scope)?;
    b.stmts = new_stmts;
    Ok(())
}

fn process_stmt(
    s: &mut Stmt,
    ctx: &mut ExtractCtx,
    scope: &BTreeMap<VarId, Type>,
) -> Result<(), Stage7Error> {
    match s {
        Stmt::Let { value, .. } | Stmt::Eval(value) => process_expr(value, ctx, scope),
    }
}

fn process_tail(
    t: &mut BlockTail,
    ctx: &mut ExtractCtx,
    scope: &BTreeMap<VarId, Type>,
) -> Result<(), Stage7Error> {
    match t {
        BlockTail::Value(e) => process_expr(e, ctx, scope),
        BlockTail::Return(value) => process_expr(value, ctx, scope),
        BlockTail::Break { value, .. } | BlockTail::Continue { value, .. } => {
            process_expr(value, ctx, scope)
        }
        BlockTail::ReturnFromBlock { value, .. } => process_expr(value, ctx, scope),
        BlockTail::Abort { code } => process_expr(code, ctx, scope),
    }
}

fn process_expr(
    e: &mut Expr,
    ctx: &mut ExtractCtx,
    scope: &BTreeMap<VarId, Type>,
) -> Result<(), Stage7Error> {
    match e {
        Expr::If {
            cond,
            then_branch,
            else_branch,
        } => {
            process_expr(cond, ctx, scope)?;
            process_block(then_branch, ctx, scope.clone())?;
            process_block(else_branch, ctx, scope.clone())?;
        }
        Expr::Match {
            selector, cases, ..
        } => {
            process_expr(selector, ctx, scope)?;
            for arm in cases.iter_mut() {
                process_block(&mut arm.body, ctx, scope.clone())?;
            }
        }
        Expr::While {
            header,
            cond,
            body,
            iter_locals,
            ..
        } => {
            // The iter-local binders AND the header's lets are in scope
            // for `cond` and `body` (the header runs each iteration
            // before them). Build that loop-interior scope so an inner
            // LabeledBlock that reads an iter-local / header local types
            // correctly and isn't mis-classified as live-out. Mirrors
            // `loop_extract::extract_while`. (Was a header-isolation bug:
            // each of header/cond/body got a fresh `scope.clone()`, so
            // iter-locals and header locals looked free.)
            let mut loop_scope = scope.clone();
            for (binder, init) in iter_locals.iter() {
                let ty = type_of(init, scope, ctx.program)
                    .expect("value must be typeable to size the synthetic helper signature");
                loop_scope.insert(binder.clone(), ty);
            }
            process_block(header, ctx, loop_scope.clone())?;
            for s in &header.stmts {
                if let Stmt::Let { pattern, value } = s {
                    extend_scope_with_let(
                        &mut loop_scope,
                        pattern,
                        value,
                        ctx.program,
                        &ctx.parent_name,
                    );
                }
            }
            process_expr(cond, ctx, &loop_scope)?;
            process_block(body, ctx, loop_scope)?;
        }
        Expr::Quantifier { body, .. } => {
            process_block(body, ctx, scope.clone())?;
        }
        Expr::LabeledBlock { body, .. } => {
            // Nested LabeledBlock in Expr position (not Stmt::Eval).
            // Recurse for inner LabeledBlocks; this outer one is left
            // alone (no result-temp extraction at expr position for
            // now -- the IR-level rewrite at Stmt::Eval is enough for
            // the find_index! shape).
            process_block(body, ctx, scope.clone())?;
        }
        Expr::Call { args, .. } | Expr::Tuple(args) | Expr::Pack { fields: args, .. } => {
            for a in args.iter_mut() {
                process_expr(a, ctx, scope)?;
            }
        }
        Expr::Unpack { value, .. }
        | Expr::Field { base: value, .. }
        | Expr::ReadRef(value)
        | Expr::ToProp(value)
        | Expr::ToBool(value)
        | Expr::UnOp { operand: value, .. } => {
            process_expr(value, ctx, scope)?;
        }
        Expr::BinOp { lhs, rhs, .. } => {
            process_expr(lhs, ctx, scope)?;
            process_expr(rhs, ctx, scope)?;
        }
        Expr::WriteRef { reference, value } => {
            process_expr(reference, ctx, scope)?;
            process_expr(value, ctx, scope)?;
        }
        _ => {}
    }
    Ok(())
}

/// True if any `BlockTail::ReturnFromBlock` appears anywhere in `b`,
/// including its own tail and every nested block. Used to decide
/// whether a top-level `Stmt::Eval(LabeledBlock)` is "degenerate"
/// (its only exit is the trailing tail) and can be inlined rather
/// than extracted into a helper.
fn block_contains_rfb(b: &Block) -> bool {
    b.stmts.iter().any(stmt_contains_rfb) || tail_contains_rfb_full(&b.tail)
}

fn stmt_contains_rfb(s: &Stmt) -> bool {
    match s {
        Stmt::Let { value, .. } | Stmt::Eval(value) => expr_contains_rfb(value),
    }
}

fn tail_contains_rfb_full(t: &BlockTail) -> bool {
    match t {
        BlockTail::ReturnFromBlock { .. } => true,
        BlockTail::Value(e) => expr_contains_rfb(e),
        BlockTail::Return(e)
        | BlockTail::Break { value: e, .. }
        | BlockTail::Continue { value: e, .. }
        | BlockTail::Abort { code: e } => expr_contains_rfb(e),
    }
}

/// Like `tail_contains_rfb_full`, but a top-level
/// `ReturnFromBlock` tail does NOT count -- only nested ones inside
/// its carried value. Used on a labeled block's OWN tail: the
/// trailing `return_from_block` is the expected single exit, not an
/// early one.
fn tail_contains_nested_rfb(t: &BlockTail) -> bool {
    match t {
        BlockTail::ReturnFromBlock { value, .. } => expr_contains_rfb(value),
        BlockTail::Value(e) => expr_contains_rfb(e),
        BlockTail::Return(e)
        | BlockTail::Break { value: e, .. }
        | BlockTail::Continue { value: e, .. }
        | BlockTail::Abort { code: e } => expr_contains_rfb(e),
    }
}

fn expr_contains_rfb(e: &Expr) -> bool {
    use Expr::*;
    match e {
        Expr::Borrow { step, base } => {
            step.exprs().any(expr_contains_rfb) || expr_contains_rfb(base)
        }
        Expr::Update { step, base, value } => {
            step.exprs().any(expr_contains_rfb)
                || expr_contains_rfb(base)
                || expr_contains_rfb(value)
        }
        Var(_)
        | Const(_)
        | Unit
        | BorrowLoc(_)
        | BorrowGlobal(_)
        | WriteBack { .. }
        | IsParent { .. } => false,
        BinOp { lhs, rhs, .. } => expr_contains_rfb(lhs) || expr_contains_rfb(rhs),
        UnOp { operand, .. } => expr_contains_rfb(operand),
        BitOp(op) => match op {
            crate::ir::ops::BitOp::Extract { operand, .. }
            | crate::ir::ops::BitOp::ZeroExtend { operand, .. }
            | crate::ir::ops::BitOp::SignExtend { operand, .. } => expr_contains_rfb(operand),
            crate::ir::ops::BitOp::Concat { high, low } => {
                expr_contains_rfb(high) || expr_contains_rfb(low)
            }
        },
        Call { args, .. } | Tuple(args) | Pack { fields: args, .. } => {
            args.iter().any(expr_contains_rfb)
        }
        Unpack { value, .. }
        | Field { base: value, .. }
        | ReadRef(value)
        | ToProp(value)
        | ToBool(value) => expr_contains_rfb(value),
        WriteRef { reference, value } => expr_contains_rfb(reference) || expr_contains_rfb(value),
        If {
            cond,
            then_branch,
            else_branch,
        } => {
            expr_contains_rfb(cond)
                || block_contains_rfb(then_branch)
                || block_contains_rfb(else_branch)
        }
        Match {
            selector, cases, ..
        } => expr_contains_rfb(selector) || cases.iter().any(|a| block_contains_rfb(&a.body)),
        While {
            header, cond, body, ..
        } => block_contains_rfb(header) || expr_contains_rfb(cond) || block_contains_rfb(body),
        Quantifier { domain, body, .. } => {
            let d = match domain {
                crate::ir::QuantDomain::Unbounded => false,
                crate::ir::QuantDomain::Range { start, end } => {
                    expr_contains_rfb(start) || expr_contains_rfb(end)
                }
                crate::ir::QuantDomain::VecRange { vec, start, end } => {
                    expr_contains_rfb(vec) || expr_contains_rfb(start) || expr_contains_rfb(end)
                }
                crate::ir::QuantDomain::Collection(c) => expr_contains_rfb(c),
            };
            d || block_contains_rfb(body)
        }
        LabeledBlock { body, .. } => block_contains_rfb(body),
    }
}

/// A labeled block is "degenerate" (inlinable) when its only exit is
/// the trailing tail -- i.e. no early `ReturnFromBlock` reaches it
/// from nested control flow. Such a block is a plain statement
/// sequence whose inner `Stmt::Let`s bind function-level temps that
/// later code (loops, returns) consumes; extracting it into a helper
/// would drop those live-out bindings. Inlining preserves them.
fn labeled_block_is_inlinable(body: &Block) -> bool {
    !body.stmts.iter().any(stmt_contains_rfb) && !tail_contains_nested_rfb(&body.tail)
}

/// Replace the value at every function-exit `BlockTail::Return` in
/// `b` (recursing through If/Match arms, labeled blocks, and loop
/// bodies) with `val`. Used to make an extracted labeled-block helper
/// return its live-out values instead of its (discarded) result: the
/// labeled block binds vars used after it, but extraction would
/// otherwise drop them. Every exit is a `Return` after
/// `rewrite_returns_in_block`, and the live-out vars are bound before
/// all exits, so substituting the tuple at each Return is well-formed.
/// Collect every variable BOUND inside block `b` (Let patterns,
/// match-arm bindings, While iter-local binders), recursing through
/// nested blocks. Used to restrict a labeled block's live-out set to
/// vars it actually binds (free_vars of the suffix can leak vars
/// bound inside a following loop).
fn collect_block_binds(b: &Block, out: &mut BTreeSet<VarId>) {
    for s in &b.stmts {
        match s {
            Stmt::Let { pattern, value } => {
                for p in pattern.iter().flatten() {
                    out.insert(p.clone());
                }
                collect_expr_binds(value, out);
            }
            Stmt::Eval(e) => collect_expr_binds(e, out),
        }
    }
    match &b.tail {
        BlockTail::Value(e) => collect_expr_binds(e, out),
        BlockTail::Return(e)
        | BlockTail::Break { value: e, .. }
        | BlockTail::Continue { value: e, .. }
        | BlockTail::Abort { code: e }
        | BlockTail::ReturnFromBlock { value: e, .. } => collect_expr_binds(e, out),
    }
}

fn collect_expr_binds(e: &Expr, out: &mut BTreeSet<VarId>) {
    match e {
        Expr::If {
            then_branch,
            else_branch,
            ..
        } => {
            collect_block_binds(then_branch, out);
            collect_block_binds(else_branch, out);
        }
        Expr::Match { cases, .. } => {
            for arm in cases.iter() {
                for b in arm.bindings.iter() {
                    out.insert(b.clone());
                }
                collect_block_binds(&arm.body, out);
            }
        }
        Expr::LabeledBlock { body, .. } => collect_block_binds(body, out),
        Expr::While {
            header,
            body,
            iter_locals,
            ..
        } => {
            for (binder, _) in iter_locals.iter() {
                out.insert(binder.clone());
            }
            collect_block_binds(header, out);
            collect_block_binds(body, out);
        }
        _ => {}
    }
}

fn replace_return_values(b: &mut Block, val: &Expr) {
    for s in b.stmts.iter_mut() {
        match s {
            Stmt::Let { value, .. } | Stmt::Eval(value) => {
                replace_return_values_in_expr(value, val)
            }
        }
    }
    match &mut b.tail {
        BlockTail::Return(v) => **v = val.clone(),
        BlockTail::Value(e) => replace_return_values_in_expr(e, val),
        _ => {}
    }
}

fn replace_return_values_in_expr(e: &mut Expr, val: &Expr) {
    match e {
        Expr::If {
            then_branch,
            else_branch,
            ..
        } => {
            replace_return_values(then_branch, val);
            replace_return_values(else_branch, val);
        }
        Expr::Match { cases, .. } => {
            for arm in cases.iter_mut() {
                replace_return_values(&mut arm.body, val);
            }
        }
        Expr::LabeledBlock { body, .. } => replace_return_values(body, val),
        Expr::While { header, body, .. } => {
            replace_return_values(header, val);
            replace_return_values(body, val);
        }
        _ => {}
    }
}

fn extract_one(
    mut body: Block,
    ctx: &mut ExtractCtx,
    scope: &BTreeMap<VarId, Type>,
    live_out: &[VarId],
) -> Result<Stmt, Stage7Error> {
    // 1. Identify the result temp.
    //
    // Two shapes accepted:
    //   (a) natural-tail `Value(Unit)` with preceding `Stmt::Let{[Some(t)], V}`
    //       -- the legacy shape produced when the labeled body falls
    //       through (no explicit ReturnFromBlock at the natural exit).
    //   (b) natural-tail `ReturnFromBlock{level:0, value:Unit}` with
    //       preceding `Stmt::Let{[Some(t)], V}` -- the shape
    //       label_analysis produces for find_index!-style macros where
    //       every body path exits via return_from_block (the loop's
    //       "not found" arm sets the result temp then explicitly
    //       returns from the labeled block).
    //
    // In both cases we pop the trailing let, register `t` as the
    // result temp, and inline its value `V` into the tail so the
    // helper carries it out.
    let result_temp: Option<VarId>;
    let result_ty: Type;
    {
        let tail_is_value_unit = matches!(&body.tail, BlockTail::Value(Expr::Unit));
        let tail_is_rfb_level_0_unit = matches!(
            &body.tail,
            BlockTail::ReturnFromBlock { level: 0, value: v } if matches!(v.as_ref(), Expr::Unit)
        );
        let last_is_let = body
            .stmts
            .last()
            .map(|s| matches!(s, Stmt::Let { pattern, .. } if pattern.len() == 1 && pattern[0].is_some()))
            .unwrap_or(false);

        // .aborts pattern: tail is `Value(Match { ... })` where the
        // NoAbort arm body has `Let { [Some($t)], V }; tail RFB(0, Unit)`.
        // Mirrors the source `[..., let $t = V] + RFB(0, Unit)` shape
        // but nested inside a Match introduced by aborts_variant's
        // callee-abort splice. The result temp is in the NoAbort arm.
        //
        // Detection requires extracting it via a mutable borrow, so we
        // collect the temp + ty up front (immutable scan) and apply the
        // mutation in a separate scope.
        //
        // Note: this branch is checked independently of `last_is_let`
        // and `tail_is_value_unit/rfb` -- the .aborts shape has a
        // trailing `let __c_N = .aborts(...)` stmt (so `last_is_let`
        // is also true) but its tail is a Value(Match), not the
        // Value(Unit)/RFB shape the source-pattern branch matches.
        let aborts_match_info: Option<(VarId, Type)> = if !tail_is_value_unit
            && !tail_is_rfb_level_0_unit
        {
            if let BlockTail::Value(Expr::Match { cases, .. }) = &body.tail {
                let noabort_idx = cases
                    .iter()
                    .position(|arm| arm.variant == 0 && arm.bindings.is_empty());
                if let Some(idx) = noabort_idx {
                    let arm_body = &cases[idx].body;
                    let arm_tail_rfb_unit = matches!(
                        &arm_body.tail,
                        BlockTail::ReturnFromBlock { level: 0, value: v } if matches!(v.as_ref(), Expr::Unit)
                    );
                    let arm_last_let = arm_body.stmts.last().map(|s| matches!(s, Stmt::Let { pattern, .. } if pattern.len() == 1 && pattern[0].is_some())).unwrap_or(false);
                    if arm_tail_rfb_unit && arm_last_let {
                        if let Some(Stmt::Let { pattern, value }) = arm_body.stmts.last() {
                            let temp = pattern[0].clone().unwrap();
                            // Build a local scope from the outer body's
                            // stmts AND the arm body's preceding stmts
                            // so `type_of(value)` resolves inner
                            // `Var(local)` references. Mirror of the
                            // fix in the main branch below.
                            let mut local_scope = scope.clone();
                            for s in &body.stmts {
                                if let Stmt::Let {
                                    pattern: p,
                                    value: v,
                                } = s
                                {
                                    for entry in p.iter() {
                                        if let Some(var) = entry {
                                            let t = type_of(v, &local_scope, ctx.program)
                                                .expect("value must be typeable to size the synthetic helper signature");
                                            local_scope.insert(var.clone(), t);
                                        }
                                    }
                                }
                            }
                            // Walk arm_body.stmts EXCEPT the trailing
                            // let (which carries `value`).
                            let arm_stmts_no_last = arm_body
                                .stmts
                                .iter()
                                .take(arm_body.stmts.len().saturating_sub(1));
                            for s in arm_stmts_no_last {
                                if let Stmt::Let {
                                    pattern: p,
                                    value: v,
                                } = s
                                {
                                    for entry in p.iter() {
                                        if let Some(var) = entry {
                                            let t = type_of(v, &local_scope, ctx.program)
                                                .expect("value must be typeable to size the synthetic helper signature");
                                            local_scope.insert(var.clone(), t);
                                        }
                                    }
                                }
                            }
                            let ty = type_of(value, &local_scope, ctx.program).expect(
                                "value must be typeable to size the synthetic helper signature",
                            );
                            Some((temp, ty))
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

        if (tail_is_value_unit || tail_is_rfb_level_0_unit) && last_is_let {
            let stmt = body.stmts.pop().unwrap();
            if let Stmt::Let { pattern, value } = stmt {
                let temp = pattern[0].clone().unwrap();
                // Build a local scope from the body's preceding stmts
                // so `type_of` can resolve the popped value's type even
                // when it's `Var(inner_local)`. Without this, a chain
                // like `let $t17 = true; let $t2 = $t17; RFB(0, Unit)`
                // computes type_of(Var($t17), outer_scope) = None,
                // defaults to Unit, and the helper's signature becomes
                // `-> ()` despite the body returning a Bool. Affects
                // any labeled_block whose trailing let value is a
                // local-var reference rather than a direct Call/Const.
                let mut local_scope = scope.clone();
                for s in &body.stmts {
                    if let Stmt::Let {
                        pattern: p,
                        value: v,
                    } = s
                    {
                        for entry in p.iter() {
                            if let Some(var) = entry {
                                let t = type_of(v, &local_scope, ctx.program).expect(
                                    "value must be typeable to size the synthetic helper signature",
                                );
                                local_scope.insert(var.clone(), t);
                            }
                        }
                    }
                }
                let ty = type_of(&value, &local_scope, ctx.program)
                    .expect("value must be typeable to size the synthetic helper signature");
                if tail_is_value_unit {
                    body.tail = BlockTail::Value(value);
                } else {
                    // Preserve ReturnFromBlock shape so step 2's
                    // rewrite_returns_in_block converts it to
                    // BlockTail::Return(value) along with every other
                    // inner ReturnFromBlock.
                    body.tail = BlockTail::ReturnFromBlock {
                        level: 0,
                        value: Box::new(value),
                    };
                }
                result_temp = Some(temp);
                result_ty = ty;
            } else {
                unreachable!()
            }
        } else if let Some((temp, ty)) = aborts_match_info {
            // .aborts Match-tail shape: pop the let from the NoAbort
            // arm body, change the arm's tail to `Value(let_value)`
            // so the Match-arm value type carries V's type. The
            // Aborted arm's `Return(__c)` is dead code in this
            // pattern (the inner aborts-check returns NoAbort for
            // the labeled_block's natural-exit operations, which
            // are pure for find_index!-style macros). To keep the
            // helper's Match arms type-compatible, rewrite the
            // Aborted arm's tail to `Abort { code: 0 }` -- the
            // renderer emits `default` for Abort tails, which
            // matches any return type.
            if let BlockTail::Value(Expr::Match { cases, .. }) = &mut body.tail {
                for arm in cases.iter_mut() {
                    if arm.variant == 0 && arm.bindings.is_empty() {
                        // NoAbort arm: pop the trailing let, set tail
                        // to Value(let_value).
                        if let Some(Stmt::Let {
                            value: let_value, ..
                        }) = arm.body.stmts.pop()
                        {
                            arm.body.tail = BlockTail::Value(let_value);
                        }
                    } else {
                        // Aborted arm (or any other arm): replace
                        // Return tail with Abort so the renderer
                        // emits `default`. The Return's payload
                        // carries AbortResult, mismatching the
                        // helper's value-typed return; the .aborts
                        // pipeline doesn't actually need to
                        // propagate the inner abort because the
                        // labeled_block's body operations are pure
                        // (see comment above).
                        if matches!(&arm.body.tail, BlockTail::Return(_)) {
                            arm.body.tail = BlockTail::Abort {
                                code: Box::new(Expr::Const(Const::UInt {
                                    bits: 64,
                                    value: ethnum::U256::from(0u64),
                                })),
                            };
                        }
                    }
                }
            }
            result_temp = Some(temp);
            result_ty = ty;
        } else if let BlockTail::Value(e) = &body.tail {
            // No trailing let, but we still have a Value tail; use its type.
            result_temp = None;
            result_ty = type_of(e, scope, ctx.program)
                .expect("value must be typeable to size the synthetic helper signature");
        } else if let BlockTail::ReturnFromBlock { value, .. } = &body.tail {
            // RFB tail with no preceding let -- result type comes from
            // the RFB's value (likely a literal or call).
            result_temp = None;
            result_ty = type_of(value, scope, ctx.program)
                .expect("value must be typeable to size the synthetic helper signature");
        } else {
            result_temp = None;
            result_ty = Type::Unit;
        }
    }

    // 2. Rewrite inner ReturnFromBlock{level:0} → Return; for inner
    //    levels, decrement.
    rewrite_returns_in_block(&mut body);

    // 2b. Live-out threading. When the labeled block binds vars used
    // AFTER it (live_out) and its own result is discarded by the
    // caller (`result_temp` is None, e.g. an `.aborts` init block
    // whose `low`/`high` flow into the loop helper), make the helper
    // RETURN those live-out values instead of its dropped result.
    // Every exit is a `Return` (post rewrite_returns_in_block) and the
    // live-out vars are bound before all exits, so substituting the
    // live-out tuple at each Return is well-formed. Sidesteps the
    // result-type question entirely (the discarded result is dropped).
    let use_live_out = !live_out.is_empty() && result_temp.is_none();
    let helper_ret_ty: Type = if use_live_out {
        // Type the live-out vars by folding the body's top-level lets.
        let mut ls = scope.clone();
        for s in &body.stmts {
            if let Stmt::Let { pattern, value } = s {
                let vt = type_of(value, &ls, ctx.program)
                    .expect("value must be typeable to size the synthetic helper signature");
                if pattern.len() == 1 {
                    if let Some(v) = &pattern[0] {
                        let t = match &vt {
                            Type::Tuple(es) if es.len() == 1 => es[0].clone(),
                            _ => vt.clone(),
                        };
                        ls.insert(v.clone(), t);
                    }
                } else if let Type::Tuple(es) = &vt {
                    if es.len() == pattern.len() {
                        for (slot, t) in pattern.iter().zip(es) {
                            if let Some(v) = slot {
                                ls.insert(v.clone(), t.clone());
                            }
                        }
                    }
                }
            }
        }
        let live_out_tys: Vec<Type> = live_out
            .iter()
            .map(|v| {
                ls.get(v)
                    .cloned()
                    .expect("live-out var is typed in the labeled-block scope")
            })
            .collect();
        let tuple_expr = if live_out.len() == 1 {
            Expr::Var(live_out[0].clone())
        } else {
            Expr::Tuple(live_out.iter().map(|v| Expr::Var(v.clone())).collect())
        };
        replace_return_values(&mut body, &tuple_expr);
        if live_out_tys.len() == 1 {
            live_out_tys.into_iter().next().unwrap()
        } else {
            Type::Tuple(live_out_tys)
        }
    } else {
        result_ty.clone()
    };

    // 3. Compute body's free vars → helper params. Filter to only
    // vars that are actually in the outer scope; free_vars's
    // walk_block snapshot/restore can incorrectly include header-
    // bound cond temps (mirroring loop_extract's pattern).
    let raw_free: BTreeSet<VarId> = free_vars(&body);
    let body_free: BTreeSet<VarId> = raw_free
        .into_iter()
        .filter(|v| scope.contains_key(v))
        .collect();
    if std::env::var_os("FOXY_DEBUG_LABELED").is_some() {
        eprintln!("[labeled_block_extract] body_free={:?}", body_free);
    }
    let mut params: Vec<Param> = Vec::new();
    let mut args: Vec<Expr> = Vec::new();
    for v in &body_free {
        let ty = scope
            .get(v)
            .cloned()
            .expect("labeled-block capture var is in scope (filtered by scope.contains_key)");
        params.push(Param {
            name: v.to_string(),
            var: v.clone(),
            ty: ty.clone(),
        });
        args.push(Expr::Var(v.clone()));
    }

    // 4. Allocate helper FunId.
    let slot = *ctx.slot_counters.entry(ctx.parent_fid).or_insert(0);
    ctx.slot_counters.insert(ctx.parent_fid, slot + 1);
    let helper_fid = ctx.next_fid;
    ctx.next_fid += 1;

    // 5. Build helper Function.
    let helper_name = crate::ir::names::labeled_name(&ctx.parent_name, slot);
    let helper_fn = Function {
        module: ctx.parent_module,
        name: helper_name,
        signature: Signature {
            type_params: ctx.parent_type_params.to_vec(),
            params,
            return_type: helper_ret_ty.clone(),
        },
        body,
        kind: FunctionKind::Synthetic,
        // Provisional; stage 8 closes world_writes over synthetic helpers.
        effects: Effects {
            aborts: AbortBit::Partial,
            det: DetBit::Det,
            mutation: MutLevel::NoMut,
            world_writes: false,
        },
        explicit_pure: false,
    };
    ctx.program.functions.insert(helper_fid, helper_fn);

    // 6. Build Call replacement.
    let type_args: Vec<Type> = ctx
        .parent_type_params
        .iter()
        .enumerate()
        .map(|(i, _)| Type::TypeParam(i as u16))
        .collect();
    let call = Expr::Call {
        fun: helper_fid,
        type_args,
        args,
    };

    if use_live_out {
        // Bind the helper's returned live-out tuple to the live-out
        // var names so subsequent code (e.g. the loop helper call)
        // resolves them.
        let pattern: Vec<Option<VarId>> = live_out.iter().map(|v| Some(v.clone())).collect();
        Ok(Stmt::Let {
            pattern,
            value: call,
        })
    } else if let Some(temp) = result_temp {
        Ok(Stmt::Let {
            pattern: vec![Some(temp)],
            value: call,
        })
    } else {
        Ok(Stmt::Eval(call))
    }
}

/// Walk `b` and convert `BlockTail::ReturnFromBlock{level:0}` to
/// `BlockTail::Return`. For `level > 0`, decrement by 1 (we just popped
/// one labeled-scope frame). Also: when the preceding stmt is a
/// `Stmt::Let{[Some(_)], V_let}` AND the ReturnFromBlock's value is
/// Unit, swap the let's value into the Return (and drop the let).
fn rewrite_returns_in_block(b: &mut Block) {
    // First recurse into stmts (for inner blocks)
    for s in b.stmts.iter_mut() {
        match s {
            Stmt::Let { value, .. } | Stmt::Eval(value) => rewrite_returns_in_expr(value),
        }
    }
    // Then handle the tail. If the tail is ReturnFromBlock{level:0,value:Unit}
    // AND the last stmt is `Stmt::Let{[Some(_)], V_let}`, splice the let's
    // value into the Return.
    let preceding_let_value: Option<Expr> = {
        let tail_is_unit_return_from_block_level_0 = matches!(
            &b.tail,
            BlockTail::ReturnFromBlock { level: 0, value: v } if matches!(v.as_ref(), Expr::Unit)
        );
        if tail_is_unit_return_from_block_level_0 {
            if let Some(Stmt::Let { pattern, .. }) = b.stmts.last() {
                if pattern.len() == 1 && pattern[0].is_some() {
                    let stmt = b.stmts.pop().unwrap();
                    if let Stmt::Let { value, .. } = stmt {
                        Some(value)
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
    };
    rewrite_returns_in_tail(&mut b.tail, preceding_let_value);
}

fn rewrite_returns_in_tail(t: &mut BlockTail, preceding_let_value: Option<Expr>) {
    match t {
        BlockTail::ReturnFromBlock { level, value } => {
            if *level == 0 {
                let v = if let Some(let_v) = preceding_let_value {
                    let_v
                } else {
                    std::mem::replace(value.as_mut(), Expr::Unit)
                };
                *t = BlockTail::Return(Box::new(v));
            } else {
                *level -= 1;
                rewrite_returns_in_expr(value);
            }
        }
        BlockTail::Value(e) => rewrite_returns_in_expr(e),
        BlockTail::Return(e) => rewrite_returns_in_expr(e),
        BlockTail::Break { value, .. } | BlockTail::Continue { value, .. } => {
            rewrite_returns_in_expr(value)
        }
        BlockTail::Abort { code } => rewrite_returns_in_expr(code),
    }
}

fn rewrite_returns_in_expr(e: &mut Expr) {
    match e {
        Expr::If {
            cond,
            then_branch,
            else_branch,
        } => {
            rewrite_returns_in_expr(cond);
            rewrite_returns_in_block(then_branch);
            rewrite_returns_in_block(else_branch);
        }
        Expr::Match {
            selector, cases, ..
        } => {
            rewrite_returns_in_expr(selector);
            for arm in cases.iter_mut() {
                rewrite_returns_in_block(&mut arm.body);
            }
        }
        Expr::While {
            header, cond, body, ..
        } => {
            rewrite_returns_in_block(header);
            rewrite_returns_in_expr(cond);
            rewrite_returns_in_block(body);
        }
        Expr::Quantifier { body, .. } => rewrite_returns_in_block(body),
        Expr::LabeledBlock { .. } => {
            // Don't recurse into nested LabeledBlocks here; their inner
            // ReturnFromBlock{level:0} belongs to the inner block, not
            // this one. A correct full implementation would track
            // depth; for now, the find_index! shape doesn't nest.
        }
        Expr::Call { args, .. } | Expr::Tuple(args) | Expr::Pack { fields: args, .. } => {
            for a in args.iter_mut() {
                rewrite_returns_in_expr(a);
            }
        }
        Expr::Unpack { value, .. }
        | Expr::Field { base: value, .. }
        | Expr::ReadRef(value)
        | Expr::ToProp(value)
        | Expr::ToBool(value)
        | Expr::UnOp { operand: value, .. } => rewrite_returns_in_expr(value),
        Expr::BinOp { lhs, rhs, .. } => {
            rewrite_returns_in_expr(lhs);
            rewrite_returns_in_expr(rhs);
        }
        Expr::WriteRef { reference, value } => {
            rewrite_returns_in_expr(reference);
            rewrite_returns_in_expr(value);
        }
        _ => {}
    }
}
