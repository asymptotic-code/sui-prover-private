//! Slice B: per-While extraction into `LoopBody` + `LoopAfter`
//! helpers.
//!
//! See `plans/lean-pipeline/stage-07-dejumps.md` "Phase 1 -- dejumps".
//!
//! For each `Stmt::Let { pattern, value: Expr::While { .. } }`
//! (or `Stmt::Eval(Expr::While { .. })`) at position `i` of some
//! enclosing `Block`:
//!
//! 1. Allocate `LoopBody { parent, slot }` and
//!    `LoopAfter { parent, slot }` FunIds.
//! 2. Build `LoopAfter`:
//!    - params = `pattern` (alpha-renamed post-loop names),
//!      typed via the iter_locals' init expressions.
//!    - body  = `Block { stmts: stmts[i+1..], tail: original_tail }`.
//!    - Recurse into LoopAfter's body for further extractions
//!      (sequential whiles, whiles inside If/Match arms).
//! 3. Build `LoopBody`:
//!    - params = iter_locals binders, same types.
//!    - body   = `Block { stmts: header.stmts, tail: Value(If { cond,
//!        then_branch: <recursed body, with Continue/Break tails
//!          rewritten to tail-Calls>,
//!        else_branch: Value(Call(LoopAfter, iter_local_args)) }) }`.
//!    - Recurse into LoopBody's body with a `LoopFrame` pushed
//!      so cross-level break/continue from inner whiles resolve
//!      against this loop.
//! 4. Replace the enclosing block:
//!    - `block.stmts = stmts[..i]`
//!    - `block.tail  = Value(Call(LoopBody, iter_local_inits))`
//!
//! After slice B, processed bodies contain no `Expr::While`; each loop is a
//! direct call-recursive `LoopBody` plus its `LoopAfter` continuation. The
//! stage postcondition rejects `While` in non-helper bodies but still tolerates
//! the historical synthetic-While helper shape. Every source loop site has
//! matching `LoopBody` + `LoopAfter` siblings.

use std::collections::BTreeMap;

#[allow(unused_imports)]
use crate::ir::analysis::free_vars::free_vars;
use crate::ir::analysis::type_of::{bind_pattern, type_of, TypeOfError};
#[allow(unused_imports)]
use crate::ir::expr::{Block, BlockTail, Expr, MatchArm, Stmt};
use crate::ir::function::{Function, FunctionKind, Param, Signature};
use crate::ir::quant::QuantDomain;
use crate::ir::ty::Type;
use crate::ir::{FunId, ModId, Program, StructId, VarId};
#[allow(unused_imports)]
use std::collections::BTreeSet;

use super::{current_world_var, find_world_struct_id, Stage7Error};

/// Extract every `Expr::While` in every non-native, non-helper,
/// non-Spec function body in `program` into `LoopBody` + `LoopAfter`
/// helpers.
pub fn run(program: &mut Program) -> Result<(), Stage7Error> {
    // Look up world struct once -- shared by every extraction.
    // `None` means stage 4 did not run; stage 4 registers World even when
    // no translated function ultimately needs it.
    let world_id = find_world_struct_id(program);

    // Snapshot fids: helpers get added during extraction; we don't
    // re-process them. Skip LoopBody / LoopAfter (already helpers)
    // and Spec(Requires) / Spec(Ensures) (pure predicate bodies with
    // no loops). DO process Spec(Aborts) -- phase 1 cloned the
    // source body into the .aborts variant, so any Expr::While the
    // source had also exists in the .aborts body and needs
    // extraction.
    let initial_fids: Vec<FunId> = program.functions.keys().copied().collect();
    for fid in initial_fids {
        let f = program.functions.get(&fid).expect("fid present");
        let skip = matches!(
            f.kind,
            FunctionKind::LoopBody { .. } | FunctionKind::LoopAfter { .. }
        ) || matches!(
            f.kind,
            FunctionKind::Spec {
                kind: crate::ir::function::SpecKind::Requires
                    | crate::ir::function::SpecKind::Ensures,
                ..
            }
        );
        if skip {
            continue;
        }

        let parent_module = f.module;
        let parent_return_type = f.signature.return_type.clone();
        let parent_type_params = f.signature.type_params.clone();
        // Initial scope: function params.
        let mut scope: BTreeMap<VarId, Type> = f
            .signature
            .params
            .iter()
            .map(|p| (p.var.clone(), p.ty.clone()))
            .collect();

        // Detach body so we can mutate program.functions while we
        // walk. Replace with placeholder; restore at the end.
        let placeholder_body = Block {
            stmts: vec![],
            tail: BlockTail::Value(Expr::Unit),
        };
        let mut body = std::mem::replace(
            &mut program.functions.get_mut(&fid).unwrap().body,
            placeholder_body,
        );

        // FunId namespace is shared between `program.functions` and
        // `program.natives.decls`. Stage 10's bounded-nat synth
        // natives (e.g. `BoundedU64_add`) live in `natives.decls`
        // and run BEFORE stage 7; ignoring them when seeding the
        // counter would make stage 7 hand a fresh LoopBody helper
        // the same FunId as an already-registered native, breaking
        // every call site that resolves through the native's FunId
        // (e.g. a `BinOp::Add` on `u64` lowered by stage 10
        // becoming `Call(<that FunId>, [a, b])`, which would then
        // resolve as the wrong function throughout later stages).
        let next_fid = program.next_function_id();
        let mut ctx = ExtractCtx {
            program,
            parent_fid: fid,
            parent_module,
            parent_return_type,
            parent_type_params,
            world_id,
            next_slot: 0,
            next_fid,
            loop_stack: Vec::new(),
        };
        rewrite_block(&mut body, &mut ctx, &mut scope)?;

        program.functions.get_mut(&fid).unwrap().body = body;
    }
    Ok(())
}

/// Per-extraction working state.
struct ExtractCtx<'p> {
    program: &'p mut Program,
    parent_fid: FunId,
    parent_module: ModId,
    parent_return_type: Type,
    parent_type_params: Vec<String>,
    /// Synthetic World struct id (registered by stage 4). `None`
    /// when stage 4 didn't run (e.g. hand-built test programs).
    /// Used by `extract_while` to detect already-augmented post-loop
    /// tails and to augment helper return types when the parent
    /// threads world.
    world_id: Option<StructId>,
    next_slot: u32,
    /// Monotonic FunId counter. Seeded above the shared translated/native
    /// function namespace; advanced by every helper allocation. Counter is
    /// per parent function, and `run()` reseeds it after intervening inserts.
    next_fid: FunId,
    /// Active loop nest. `loop_stack[len-1]` is innermost.
    loop_stack: Vec<LoopFrame>,
}

#[derive(Debug, Clone)]
struct LoopFrame {
    body_id: FunId,
    after_id: FunId,
    /// Names of the LoopBody/LoopAfter params (one per
    /// iter_locals binder). Used to size `Tuple` payloads when
    /// rewriting `Break`/`Continue` value expressions.
    iter_local_count: usize,
    /// Free vars (loop-invariant) captured into the LoopBody's
    /// signature beyond `iter_local_count` params. At every
    /// Call(body_id, ..) site, these get appended as `Var(c)` after
    /// the iter-local args. Same for LoopAfter (captures vector
    /// stored separately because LoopAfter's captures may be a
    /// subset of LoopBody's).
    body_captures: Vec<VarId>,
    after_captures: Vec<VarId>,
}

/// Walk `b` top-down. Extract any `Stmt::Let { value: While }`
/// or `Stmt::Eval(While)` it finds. Recurse into nested blocks
/// (`If` arms, `Match` arms, `While` bodies) along the way.
///
/// `scope` tracks the current locals' types for `type_of`.
fn rewrite_block(
    b: &mut Block,
    ctx: &mut ExtractCtx,
    scope: &mut BTreeMap<VarId, Type>,
) -> Result<(), Stage7Error> {
    // Walk stmts left-to-right. When we hit a While stmt, EXTRACT
    // and stop processing further stmts (they're hoisted into
    // LoopAfter, which is processed recursively).
    let mut i = 0;
    while i < b.stmts.len() {
        // Check if stmt[i] hosts a While at the top level.
        let while_info = stmt_top_while_info(&b.stmts[i]);
        if let Some(WhileSite { post_loop_names }) = while_info {
            // Take stmt[i] out by mem::replace.
            let placeholder = Stmt::Eval(Expr::Unit);
            let owned_stmt = std::mem::replace(&mut b.stmts[i], placeholder);
            let while_expr = take_while_expr(owned_stmt);
            // Steal stmts[i+1..] and the original tail into a
            // post-loop continuation block.
            let post_stmts: Vec<Stmt> = b.stmts.drain(i + 1..).collect();
            // Drop the placeholder at index i.
            b.stmts.truncate(i);
            let post_tail = std::mem::replace(&mut b.tail, BlockTail::Value(Expr::Unit));
            let post_block = Block {
                stmts: post_stmts,
                tail: post_tail,
            };

            // Run the extraction.
            let extracted_call =
                extract_while(while_expr, post_loop_names, post_block, ctx, scope)?;

            // The block's new tail is the LoopBody-call.
            b.tail = BlockTail::Value(extracted_call);
            return Ok(());
        }
        // Otherwise recurse into the stmt's value, then add
        // pattern bindings to scope.
        rewrite_stmt(&mut b.stmts[i], ctx, scope)?;
        i += 1;
    }
    rewrite_tail(&mut b.tail, ctx, scope)?;
    Ok(())
}

/// If a `Stmt` directly hosts an `Expr::While` (Eval(While) or
/// Let { value: While }), return the post-loop binding names from
/// the Let pattern (or `vec![]` for Eval).
struct WhileSite {
    post_loop_names: Vec<Option<VarId>>,
}

fn stmt_top_while_info(s: &Stmt) -> Option<WhileSite> {
    match s {
        Stmt::Eval(Expr::While { .. }) => Some(WhileSite {
            post_loop_names: vec![],
        }),
        Stmt::Let {
            pattern,
            value: Expr::While { .. },
        } => Some(WhileSite {
            post_loop_names: pattern.clone(),
        }),
        _ => None,
    }
}

fn take_while_expr(s: Stmt) -> Expr {
    match s {
        Stmt::Eval(e) => e,
        Stmt::Let { value, .. } => value,
    }
}

/// Recurse into a stmt's value expression, then update `scope` with
/// any bindings the stmt introduces. Does NOT descend into a top-level
/// `While` here -- that's caught in `rewrite_block` at the stmt level.
fn rewrite_stmt(
    s: &mut Stmt,
    ctx: &mut ExtractCtx,
    scope: &mut BTreeMap<VarId, Type>,
) -> Result<(), Stage7Error> {
    match s {
        Stmt::Let { pattern, value } => {
            // Infer type BEFORE recursing, since recursion may rewrite
            // the value (turning a While into a Call). For most non-While
            // values this is the same answer; for While, the Call result
            // type equals the While's loop_state shape, which is what
            // type_of already returns for While. So this is consistent.
            let val_ty = match type_of(value, scope, ctx.program) {
                Ok(t) => t,
                Err(_) => Type::Unit, // permissive: skip lets we can't type
            };
            rewrite_expr(value, ctx, scope)?;
            let _ = bind_pattern(pattern, &val_ty, scope);
        }
        Stmt::Eval(e) => rewrite_expr(e, ctx, scope)?,
    }
    Ok(())
}

fn rewrite_tail(
    t: &mut BlockTail,
    ctx: &mut ExtractCtx,
    scope: &mut BTreeMap<VarId, Type>,
) -> Result<(), Stage7Error> {
    match t {
        BlockTail::Value(e) => rewrite_expr(e, ctx, scope),
        BlockTail::Abort { code } => rewrite_expr(code, ctx, scope),
        BlockTail::Break { value, .. }
        | BlockTail::Continue { value, .. }
        | BlockTail::Return(value)
        | BlockTail::ReturnFromBlock { value, .. } => rewrite_expr(value, ctx, scope),
    }
}

fn rewrite_expr(
    e: &mut Expr,
    ctx: &mut ExtractCtx,
    scope: &mut BTreeMap<VarId, Type>,
) -> Result<(), Stage7Error> {
    match e {
        Expr::Borrow { step, base } => {
            for __pe in step.exprs_mut() {
                rewrite_expr(__pe, ctx, scope)?;
            }
            rewrite_expr(base, ctx, scope)
        }
        Expr::Update { step, base, value } => {
            for __pe in step.exprs_mut() {
                rewrite_expr(__pe, ctx, scope)?;
            }
            rewrite_expr(base, ctx, scope)?;
            rewrite_expr(value, ctx, scope)
        }
        Expr::Var(_)
        | Expr::Const(_)
        | Expr::Unit
        | Expr::BorrowLoc(_)
        | Expr::BorrowGlobal(_)
        | Expr::WriteBack { .. }
        | Expr::IsParent { .. } => Ok(()),
        Expr::BinOp { lhs, rhs, .. } => {
            rewrite_expr(lhs, ctx, scope)?;
            rewrite_expr(rhs, ctx, scope)
        }
        Expr::UnOp { operand, .. } => rewrite_expr(operand, ctx, scope),
        Expr::BitOp(op) => match op {
            crate::ir::ops::BitOp::Extract { operand, .. }
            | crate::ir::ops::BitOp::ZeroExtend { operand, .. }
            | crate::ir::ops::BitOp::SignExtend { operand, .. } => {
                rewrite_expr(operand, ctx, scope)
            }
            crate::ir::ops::BitOp::Concat { high, low } => {
                rewrite_expr(high, ctx, scope)?;
                rewrite_expr(low, ctx, scope)
            }
        },
        Expr::Call { args, .. } | Expr::Tuple(args) | Expr::Pack { fields: args, .. } => {
            for a in args {
                rewrite_expr(a, ctx, scope)?;
            }
            Ok(())
        }
        Expr::Unpack { value, .. }
        | Expr::Field { base: value, .. }
        | Expr::ReadRef(value)
        | Expr::ToProp(value)
        | Expr::ToBool(value) => rewrite_expr(value, ctx, scope),
        Expr::If {
            cond,
            then_branch,
            else_branch,
        } => {
            rewrite_expr(cond, ctx, scope)?;
            // Fresh scope per arm (mirrors free_vars).
            let mut s_then = scope.clone();
            rewrite_block(then_branch, ctx, &mut s_then)?;
            let mut s_else = scope.clone();
            rewrite_block(else_branch, ctx, &mut s_else)?;
            Ok(())
        }
        Expr::Match {
            selector, cases, ..
        } => {
            rewrite_expr(selector, ctx, scope)?;
            for arm in cases.iter_mut() {
                let mut s_arm = scope.clone();
                // Don't bother typing arm bindings -- scope only matters
                // if the arm body itself contains a While that needs
                // type_of, and arm bindings rarely flow into init exprs.
                for v in &arm.bindings {
                    s_arm.insert(v.clone(), Type::Unit);
                }
                rewrite_block(&mut arm.body, ctx, &mut s_arm)?;
            }
            Ok(())
        }
        Expr::While { .. } => {
            // Sub-expression While (not at top of a Stmt). Should be
            // rare after stage 5 (which lifts While to Stmt position
            // for loop_state synthesis). Defensive: leave alone for
            // now -- the postcondition will catch it if we miss.
            Ok(())
        }
        Expr::WriteRef { reference, value } => {
            rewrite_expr(reference, ctx, scope)?;
            rewrite_expr(value, ctx, scope)
        }
        Expr::Quantifier { domain, body, .. } => {
            match domain {
                QuantDomain::Unbounded => {}
                QuantDomain::Range { start, end } => {
                    rewrite_expr(start, ctx, scope)?;
                    rewrite_expr(end, ctx, scope)?;
                }
                QuantDomain::Collection(c) => rewrite_expr(c, ctx, scope)?,
                QuantDomain::VecRange { vec, start, end } => {
                    rewrite_expr(vec, ctx, scope)?;
                    rewrite_expr(start, ctx, scope)?;
                    rewrite_expr(end, ctx, scope)?;
                }
            }
            // Fresh scope inside quantifier body.
            let mut s_q = scope.clone();
            rewrite_block(body, ctx, &mut s_q)?;
            Ok(())
        }
        Expr::LabeledBlock { body, .. } => rewrite_block(body, ctx, scope),
    }
}

/// Core extraction. Builds LoopBody + LoopAfter; returns the
/// `Call(LoopBody, [iter_local_inits])` expression to substitute at
/// the original While site.
fn extract_while(
    while_expr: Expr,
    post_loop_names: Vec<Option<VarId>>,
    post_block: Block,
    ctx: &mut ExtractCtx,
    scope: &mut BTreeMap<VarId, Type>,
) -> Result<Expr, Stage7Error> {
    let (mut header, cond, mut body, iter_locals, header_exit_locals, live_out) = match while_expr {
        Expr::While {
            header,
            cond,
            body,
            iter_locals,
            header_exit_locals,
            live_out,
        } => (
            *header,
            *cond,
            *body,
            iter_locals,
            header_exit_locals,
            live_out,
        ),
        _ => unreachable!("extract_while: not a While"),
    };

    let slot = ctx.next_slot;
    ctx.next_slot += 1;
    let body_id = ctx.alloc_fid();
    // Reserve LoopBody before allocating LoopAfter so ids are
    // monotonic.
    insert_placeholder(
        ctx,
        body_id,
        FunctionKind::LoopBody {
            parent: ctx.parent_fid,
            slot,
        },
    );
    let after_id = ctx.alloc_fid();
    insert_placeholder(
        ctx,
        after_id,
        FunctionKind::LoopAfter {
            parent: ctx.parent_fid,
            slot,
        },
    );

    // Compute iter_locals' types via type_of on init expressions.
    let mut binder_types: Vec<Type> = Vec::with_capacity(iter_locals.len());
    let mut init_exprs: Vec<Expr> = Vec::with_capacity(iter_locals.len());
    let mut binder_names: Vec<VarId> = Vec::with_capacity(iter_locals.len());
    for (binder, init) in iter_locals {
        // When type inference fails (e.g. an SSA-renamed body-local
        // var leaked into the iter_locals init via a stage-5
        // miscompile), fall back to `Type::Unit` rather than failing
        // the whole pipeline. The generated helper's signature ends
        // up with a wrong type for that param; downstream rendering
        // may produce malformed Lean for the affected function, but
        // the rest of the package continues to compile. Without this
        // fallback, a single broken function in a 4000-function
        // package bricks the whole sweep.
        let ty = match type_of(&init, scope, ctx.program) {
            Ok(t) => t,
            Err(err) => {
                eprintln!(
                    "stage7 extract_while: type_of failed for binder={:?} init={:?} in fid={} (err={:?}); falling back to Type::Unit",
                    binder, init, ctx.parent_fid, err,
                );
                Type::Unit
            }
        };
        binder_types.push(ty);
        init_exprs.push(init);
        binder_names.push(binder);
    }
    if header_exit_locals.len() != binder_names.len() {
        return Err(Stage7Error::HeaderExitArityMismatch {
            function: ctx.parent_fid,
            function_name: parent_name(ctx),
            expected: binder_names.len(),
            found: header_exit_locals.len(),
        });
    }

    // Recover live-out var types by folding the loop header's `let`s
    // in a scope seeded with the iter-local binders (the header
    // references them). Each live-out is `(in_loop_name, post_name)`:
    // `post_name` becomes an extra `LoopAfter` param (typed here) and
    // `in_loop_name` is the matching exit-call arg appended below.
    // Empty `live_out` (ordinary loops) makes all of this inert.
    let live_out_types: Vec<Type> = {
        let mut hdr_scope: BTreeMap<VarId, Type> = scope.clone();
        for (name, ty) in binder_names.iter().zip(&binder_types) {
            hdr_scope.insert(name.clone(), ty.clone());
        }
        for s in &header.stmts {
            if let Stmt::Let { pattern, value } = s {
                if let Ok(vt) = type_of(value, &hdr_scope, ctx.program) {
                    let _ = bind_pattern(pattern, &vt, &mut hdr_scope);
                }
            }
        }
        live_out
            .iter()
            .map(|(in_loop, _post)| {
                hdr_scope
                    .get(in_loop)
                    .cloned()
                    .expect("live-out var is typed in the loop-header scope")
            })
            .collect()
    };

    // After-block param names from post_loop_names (or fall back to
    // binder_names when post_loop_names slots are None).
    let after_param_names: Vec<VarId> = post_loop_names
        .iter()
        .enumerate()
        .map(|(i, slot)| match slot {
            Some(v) => v.clone(),
            None => binder_names
                .get(i)
                .cloned()
                .unwrap_or_else(|| VarId::from(format!("_p{i}"))),
        })
        .collect();

    // ---- Pre-compute initial free_vars of body+header BEFORE processing.
    //
    // Nested-while extraction inside `body` later turns inner Whiles
    // into Call(inner_body_id, [iter_inits ++ inner_captures]) -- the
    // same outer-scope vars appear in both shapes, so free_vars's
    // result is stable across the rewrite. We snapshot it here so we
    // can build LoopFrame's captures list BEFORE processing the body
    // (the frame's captures are needed by rewrite_jump_tails and
    // rewrite_implicit_continues, both of which run after body
    // processing).
    let binders_set: BTreeSet<VarId> = binder_names.iter().cloned().collect();
    let mut body_initial_free: BTreeSet<VarId> = free_vars(&body);
    for v in free_vars(&header) {
        body_initial_free.insert(v);
    }
    // The cond expression's free vars are subsumed by header.tail =
    // Value(Unit) -> stage 5 ensures cond reads the header's locals,
    // which are themselves in scope here. But cond is not a Block, so
    // free_vars doesn't visit it from `free_vars(&header)`. Capture
    // them directly.
    for v in crate::ir::analysis::free_vars::free_vars_of_expr(&cond) {
        body_initial_free.insert(v);
    }

    // ---- Process post_block (LoopAfter body).
    //
    // Run rewrite_block on it FIRST (before pushing this loop's
    // frame) so any nested whiles inside post_block don't see this
    // loop in their enclosing chain. Then compute after_captures
    // from the processed result.
    let mut after_scope: BTreeMap<VarId, Type> = scope.clone();
    for (name, ty) in after_param_names.iter().zip(&binder_types) {
        after_scope.insert(name.clone(), ty.clone());
    }
    // Live-out post-names are extra LoopAfter params (appended after
    // iter-local params + after_captures below); make them visible to
    // the after-body walk and its return-type inference.
    for ((_in_loop, post), ty) in live_out.iter().zip(&live_out_types) {
        after_scope.insert(post.clone(), ty.clone());
    }
    let mut after_body = post_block;
    rewrite_block(&mut after_body, ctx, &mut after_scope)?;
    // If this loop is nested inside another, the after_body may carry
    // EXPLICIT `Break` / `Continue` tails referring to one of the
    // enclosing outer loops (e.g. `find::while_1` whose post-block
    // ends with an implicit "continue the outer loop" that stage 1
    // / stage 2 lifted as `BlockTail::Continue { level: 0 }`,
    // indexing into ctx.loop_stack[len-1] = the outer while frame).
    // Resolve those into tail-Calls now, BEFORE pushing our own
    // frame -- the same way `rewrite_jump_tails` does for the loop
    // body. Without this, the explicit jump survives into the
    // standalone `<f>.while_N.after` helper whose own loop_depth is
    // 0, and the BaseValidator's `JumpLevelOutOfBounds { level: 0,
    // depth: 0 }` check fires on render (cascading through every
    // surviving stage postcondition that re-runs the validator).
    if !ctx.loop_stack.is_empty() {
        rewrite_jump_tails(&mut after_body, ctx)?;
    }
    // Then wrap any remaining `Value(V)` tail as an implicit-continue
    // for the enclosing outer loop. (Tails that `rewrite_jump_tails`
    // already converted to `Value(Call(outer_body_id, ...))` are
    // skipped via the `is_known_loop_helper` guard.) Without this
    // the inner LoopAfter would return a raw
    // `Tuple([outer_iter_locals_next])` that doesn't match its
    // declared `parent_return_type` and breaks the outer iteration
    // chain entirely.
    if !ctx.loop_stack.is_empty() {
        rewrite_implicit_continues(&mut after_body, ctx)?;
    }

    // Phase C: a parent with a World-typed input must pass that environment
    // through its extracted helpers so their existing threaded calls and
    // tails have the right value in scope. Capturing World says only that the
    // helper depends on it; the independent world_writes bit says whether the
    // helper may change it.
    // The naive `free_vars`-based capture probe only picks up world
    // when the body / post-loop block directly references it. That misses the
    // pass-through environment needed by sibling helper calls.
    //
    // When World is not an iter-local, capture the newest canonical SSA value:
    // it is the live lifecycle channel needed by sibling helper calls. When the
    // loop already threads that live channel as an iter-local, preserve the
    // oldest outer World instead. That stable entry snapshot defines the bottom
    // of read-only partial fixpoints and is part of the durable helper ABI.
    let forced_world_capture = pass_through_world_capture(scope, &binder_types, ctx.world_id);
    // Loop helpers capture through a `BTreeSet<VarId>` too, so they
    // carry the same binder-spelling order the continuation lift did.
    // See `return_lift::order_captures`.
    let parent_ghost_params = super::return_lift::ghost_params_of(ctx.program, ctx.parent_fid);
    let after_binders: BTreeSet<VarId> = after_param_names.iter().cloned().collect();
    let after_captures: Vec<VarId> = {
        let mut set: BTreeSet<VarId> = free_vars(&after_body)
            .into_iter()
            .filter(|v| !after_binders.contains(v) && scope.contains_key(v))
            .collect();
        if let Some(wv) = &forced_world_capture {
            set.insert(wv.clone());
        }
        super::return_lift::order_captures(set, &parent_ghost_params)
    };

    // ---- Body captures: anything free in body+header that is NOT an
    // iter_local binder, UNION after_captures (so body can forward
    // them when it calls LoopAfter), restricted to vars visible in
    // the outer `scope` (others are likely locals introduced by
    // earlier stmts and won't typecheck as captures).
    let mut body_captures_set: BTreeSet<VarId> = body_initial_free
        .into_iter()
        .filter(|v| !binders_set.contains(v) && scope.contains_key(v))
        .collect();
    for c in &after_captures {
        body_captures_set.insert(c.clone());
    }
    if let Some(wv) = &forced_world_capture {
        body_captures_set.insert(wv.clone());
    }
    let body_captures = super::return_lift::order_captures(body_captures_set, &parent_ghost_params);

    // ---- Derive the shared helper return type BEFORE processing the
    // body: `after_body` is final from here on. This computation IS
    // Phase B (see its comment below), hoisted so the real type can be
    // patched onto the placeholder signatures before nested extraction
    // reads them: an inner loop's after-tail re-enters this loop via
    // `Call(body_id, ..)`, and its own Phase B resolves that call off
    // the placeholder -- which `insert_placeholder` stamped with the
    // parent FUNCTION's return type, correct only for a while in
    // function-tail position. A loop in an `if` arm whose value tuple
    // differs (e.g. a `&mut` field projection held live across the
    // loop by an early exit -- sui-system's `insertion_sort_by!`
    // expansion in `process_pending_removals`) mis-typed every inner
    // helper in the nest.
    let helper_return_type = {
        let t = after_tail_return_type(&after_body.tail, &after_scope, ctx);
        // For .aborts variants and their continuations (which return
        // Option<MoveAbortCode>), the after-body's tail-Value(Unit) is
        // a placeholder for "the inner loop didn't abort"; the helper
        // must still return AbortResult so the caller's match-on-Option
        // type-checks. Override Unit -> parent_return_type whenever
        // they disagree on Unit-ness.
        if matches!(t, Type::Unit) && !matches!(ctx.parent_return_type, Type::Unit) {
            ctx.parent_return_type.clone()
        } else {
            t
        }
    };
    for id in [body_id, after_id] {
        ctx.program
            .functions
            .get_mut(&id)
            .expect("loop-helper placeholder inserted at allocation")
            .signature
            .return_type = helper_return_type.clone();
    }

    // ---- Push frame, process body, rewrite tails.
    ctx.loop_stack.push(LoopFrame {
        body_id,
        after_id,
        iter_local_count: binder_names.len(),
        body_captures: body_captures.clone(),
        after_captures: after_captures.clone(),
    });

    let mut body_scope: BTreeMap<VarId, Type> = scope.clone();
    for (name, ty) in binder_names.iter().zip(&binder_types) {
        body_scope.insert(name.clone(), ty.clone());
    }
    // The structured header executes before the condition and its bindings
    // remain in scope throughout the body. Nested loops in that body may
    // capture those values in their `.after` continuations (Sui voting
    // power's nested `do!` expansion is the corpus case). If the header
    // bindings are absent here, nested extraction filters them out as
    // apparently out-of-scope free variables and emits an unbound helper.
    for stmt in &header.stmts {
        if let Stmt::Let { pattern, value } = stmt {
            if let Ok(ty) = type_of(value, &body_scope, ctx.program) {
                let _ = bind_pattern(pattern, &ty, &mut body_scope);
            }
        }
    }
    rewrite_block(&mut body, ctx, &mut body_scope)?;
    // The `loop { ...; if C { break }; if c2 { upd; continue } else { upd;
    // continue } }` shape leaves the updating if (whose arms carry the
    // loop's REAL back-edges with the updated loop-state) as a non-tail
    // `Stmt::Eval(LabeledBlock/If)` followed by an UNREACHABLE
    // `Value(<loop-state>)` body tail (stage 5's implicit-continue
    // placeholder). Without lifting the diverging eval into tail position,
    // `rewrite_jump_tails` threads the real (state-updating) continues as
    // DISCARDED recursive calls and `rewrite_implicit_continues` turns the
    // dead tail into the actual recurse -- with STALE loop-state -> the loop
    // never makes progress (diverging under `partial_fixpoint`). Lift it
    // so the updating continues land in tail position and thread correctly.
    lift_trailing_diverging_eval(&mut body);
    rewrite_jump_tails(&mut body, ctx)?;
    rewrite_implicit_continues(&mut body, ctx)?;

    // A structured loop header can carry explicit `Continue` / `Break`
    // (e.g. `if cond { ...; continue }` skip-to-next-iteration in
    // `binary_search`). The header becomes LoopBody's leading
    // statements, so those jumps must also be lowered to recursive
    // `while_N` / `while_N.after` calls. Run ONLY jump-rewriting, NOT
    // implicit-continue wrapping: the header's own `Value(Unit)` tail
    // is a fall-through to the cond check, not an implicit continue.
    rewrite_jump_tails(&mut header, ctx)?;

    ctx.loop_stack.pop();

    // ---- Build LoopAfter with augmented params.
    let mut after_params: Vec<Param> = after_param_names
        .iter()
        .zip(&binder_types)
        .map(|(name, ty)| Param {
            name: name.to_string(),
            var: name.clone(),
            ty: ty.clone(),
        })
        .collect();
    for c in &after_captures {
        let ty = scope
            .get(c)
            .cloned()
            .expect("loop-helper capture var is in scope (filtered by scope membership)");
        after_params.push(Param {
            name: c.to_string(),
            var: c.clone(),
            ty,
        });
    }
    // Live-out params: post-loop names typed via the header fold.
    // These align positionally with the extra exit-call args appended
    // to `after_call_args` below (loop-internal names).
    for ((_in_loop, post), ty) in live_out.iter().zip(&live_out_types) {
        after_params.push(Param {
            name: post.to_string(),
            var: post.clone(),
            ty: ty.clone(),
        });
    }
    // Phase B (computed above, before the frame push -- nested
    // extraction reads it off the LoopFrame): derive the helper
    // return type from the post-loop continuation's actual tail. The
    // previous hard-coded
    // `ctx.parent_return_type` happened to work only when the while
    // was at the function-body top-level. Nested whiles inside an
    // `if` / `match` arm hoist an inner-block tail into the helper,
    // whose natural value type is what the surrounding parent
    // continuation expects -- not the function's full return type.
    // With Phase A lifting captures into iter_locals, the helper's
    // true return shape is whatever the post-loop continuation
    // value is; a helper claiming `parent_return_type` while
    // delivering an inner-block tail breaks downstream type-
    // checking at every call site in the parent that consumes the
    // loop's value as the inner type.
    //
    // We do NOT automatically World-augment this natural continuation type.
    // The parent's surrounding code (e.g. the `if`'s arms
    // whose unified value type drives a `Stmt::Let` destructure)
    // expects the natural (non-world) shape, and augmenting here
    // would introduce a Tuple-vs-scalar mismatch the parent's
    // already-augmented stage-4 IR cannot reconcile. A read-only helper may
    // therefore take World while returning only this natural value. Stage 8
    // closes world_writes over the final helper graph; if a helper can write,
    // the final postcondition requires an updated World result and rejects a
    // helper whose extracted shape would drop it.
    //
    // Strategy:
    //   - Value(e):                use type_of(e) in after_scope.
    //   - Return/Abort:            keep parent_return_type (helper's
    //     declared return type is unused at runtime but must
    //     structurally match downstream callers' expectations; the
    //     tail propagates up the call chain unchanged).
    //   - Break/Continue:          same fallback as before
    //     (cross-level jump out of an extracted-helper boundary
    //     isn't exercised by any current client).
    // Belt-and-braces: if helper_return_type is a Tuple but the
    // current tail value is a non-Tuple (e.g. natural was
    // Tuple([T]) singleton from a pattern destructure but the tail
    // expression is a bare Var of that singleton type), wrap so the
    // rendered function body matches its declared return type. This
    // mirrors the former normalize-after-tail behaviour for the
    // cases it actually covered (preserving the always-Tuple
    // invariant some upstream stages rely on).
    if let BlockTail::Value(ref mut e) = &mut after_body.tail {
        if matches!(helper_return_type, Type::Tuple(_)) && !matches!(e, Expr::Tuple(_)) {
            let taken = std::mem::replace(e, Expr::Unit);
            *e = Expr::Tuple(vec![taken]);
        }
    }

    let after_fn = Function {
        module: ctx.parent_module,
        name: crate::ir::names::after_name(&parent_name(ctx), slot),
        signature: Signature {
            type_params: ctx.parent_type_params.clone(),
            params: after_params,
            return_type: helper_return_type.clone(),
        },
        body: after_body,
        kind: FunctionKind::LoopAfter {
            parent: ctx.parent_fid,
            slot,
        },
        // Provisional metadata: extraction starts helpers at Effects::PURE;
        // stage 8 closes world_writes over the final helper graph. Stage 4's
        // executable lifecycle checks still apply here, and a writer or a
        // helper that returns World must satisfy the full World ABI and tails.
        effects: crate::ir::Effects::PURE,
        explicit_pure: false,
    };
    ctx.program.functions.insert(after_id, after_fn);

    // ---- Build LoopBody with augmented params.
    let mut body_params: Vec<Param> = binder_names
        .iter()
        .zip(&binder_types)
        .map(|(name, ty)| Param {
            name: name.to_string(),
            var: name.clone(),
            ty: ty.clone(),
        })
        .collect();
    for c in &body_captures {
        let ty = scope
            .get(c)
            .cloned()
            .expect("loop-helper capture var is in scope (filtered by scope membership)");
        body_params.push(Param {
            name: c.to_string(),
            var: c.clone(),
            ty,
        });
    }

    // else_branch (cond=false exit) -- the header has already executed, so
    // pass its latest carried values rather than the iteration-entry binders.
    let mut after_call_args: Vec<Expr> = header_exit_locals
        .iter()
        .map(|n| Expr::Var(n.clone()))
        .collect();
    for c in &after_captures {
        after_call_args.push(Expr::Var(c.clone()));
    }
    // Live-out exit args: loop-internal (header) names, in scope at
    // this cond-false exit because `header.stmts` are LoopBody's
    // leading statements. Positionally match the live-out LoopAfter
    // params appended above.
    for (in_loop, _post) in &live_out {
        after_call_args.push(Expr::Var(in_loop.clone()));
    }
    let else_block = Block {
        stmts: vec![],
        tail: BlockTail::Value(Expr::Call {
            fun: after_id,
            type_args: ctx
                .parent_type_params
                .iter()
                .enumerate()
                .map(|(i, _)| Type::TypeParam(i as u16))
                .collect(),
            args: after_call_args,
        }),
    };
    let wrapped_body = Block {
        stmts: header.stmts,
        tail: BlockTail::Value(Expr::If {
            cond: Box::new(cond),
            then_branch: Box::new(body),
            else_branch: Box::new(else_block),
        }),
    };

    let body_fn = Function {
        module: ctx.parent_module,
        name: crate::ir::names::while_name(&parent_name(ctx), slot),
        signature: Signature {
            type_params: ctx.parent_type_params.clone(),
            params: body_params,
            // LoopBody and LoopAfter share a return type: LoopBody's
            // else-branch tail-calls LoopAfter, so the unified arm
            // type of the wrapped `if cond then body else
            // Call(after_id, ...)` is whatever LoopAfter returns.
            return_type: helper_return_type.clone(),
        },
        body: wrapped_body,
        kind: FunctionKind::LoopBody {
            parent: ctx.parent_fid,
            slot,
        },
        // See `after_fn` above for the provisional Effects::PURE metadata.
        effects: crate::ir::Effects::PURE,
        explicit_pure: false,
    };
    ctx.program.functions.insert(body_id, body_fn);
    retype_placeholder_typed_nested_helpers(ctx, after_id);

    // Top-level call: init args + Var(capture) for each body capture.
    let mut top_args: Vec<Expr> = init_exprs;
    for c in &body_captures {
        top_args.push(Expr::Var(c.clone()));
    }
    Ok(Expr::Call {
        fun: body_id,
        type_args: ctx
            .parent_type_params
            .iter()
            .enumerate()
            .map(|(i, _)| Type::TypeParam(i as u16))
            .collect(),
        args: top_args,
    })
}

/// Phase B derivation (see the comment at the computation site in
/// `extract_while`): the helper return type from the post-loop
/// continuation's tail. A `Value` tail has the type it computes --
/// including a tail call to an enclosing loop's helper, which resolves
/// off that helper's placeholder signature, kept accurate by the
/// patch at the computation site. Every diverging tail keeps the
/// parent function's return type (structurally unused at runtime, but
/// it must match downstream callers' expectations).
fn after_tail_return_type(
    tail: &BlockTail,
    after_scope: &BTreeMap<VarId, Type>,
    ctx: &ExtractCtx,
) -> Type {
    match tail {
        BlockTail::Value(e) => match type_of(e, after_scope, ctx.program) {
            Ok(t) => t,
            Err(_) => Type::Unit,
        },
        BlockTail::Return(_) | BlockTail::Abort { .. } => ctx.parent_return_type.clone(),
        BlockTail::Break { .. } | BlockTail::Continue { .. } => ctx.parent_return_type.clone(),
        BlockTail::ReturnFromBlock { .. } => ctx.parent_return_type.clone(),
    }
}

/// Walk `b` looking for `BlockTail::Continue/Break { level: 0 }` and
/// rewrite each to `Value(Call(LoopBody/LoopAfter, [args]))`. Cross-
/// level (level > 0) consults `ctx.loop_stack`.
///
/// This rewrite happens AFTER `rewrite_block` has already extracted
/// inner whiles; so by the time we look at a tail, any inner whiles
/// have collapsed to Value(Call(...)) tails (which we don't touch).
/// If a block's LAST stmt is `Stmt::Eval(E)` where `E` is an
/// `If`/`Match`/`LabeledBlock` ALL of whose control-flow paths diverge
/// (every leaf tail is a loop jump `Continue`/`Break`, or `Return`/`Abort`),
/// then the block's own tail is unreachable. Lift `E` into tail position
/// (`tail = Value(E)`) and drop the dead tail. See the call site in
/// `extract_while` for why loop bodies need this.
///
/// `ReturnFromBlock` leaves are treated CONSERVATIVELY as non-diverging
/// (they may complete a labeled block CONTAINED in `E`), so the lift never
/// fires when a `ReturnFromBlock` is reachable -- only the all-`Continue` /
/// all-`Break` / all-`Return` / all-`Abort` (and nestings thereof) shapes.
fn lift_trailing_diverging_eval(b: &mut Block) {
    let last_diverges = matches!(
        b.stmts.last(),
        Some(Stmt::Eval(e)) if expr_all_paths_diverge(e)
    );
    if last_diverges {
        if let Some(Stmt::Eval(e)) = b.stmts.pop() {
            b.tail = BlockTail::Value(e);
        }
    }
}

fn expr_all_paths_diverge(e: &Expr) -> bool {
    match e {
        Expr::If {
            then_branch,
            else_branch,
            ..
        } => block_all_paths_diverge(then_branch) && block_all_paths_diverge(else_branch),
        Expr::Match { cases, .. } => {
            !cases.is_empty() && cases.iter().all(|c| block_all_paths_diverge(&c.body))
        }
        Expr::LabeledBlock { body, .. } => block_all_paths_diverge(body),
        _ => false,
    }
}

fn block_all_paths_diverge(b: &Block) -> bool {
    match &b.tail {
        BlockTail::Continue { .. }
        | BlockTail::Break { .. }
        | BlockTail::Return(_)
        | BlockTail::Abort { .. } => true,
        // Conservative: a `ReturnFromBlock` may target a labeled block
        // contained in the expression being lifted, in which case control
        // resumes and the expression does NOT diverge. Never lift then.
        BlockTail::ReturnFromBlock { .. } => false,
        BlockTail::Value(e) => expr_all_paths_diverge(e),
    }
}

#[derive(Clone, Copy)]
enum JumpHandoff {
    BlockValue,
    EarlyReturn,
    UnsupportedOperand,
}

fn rewrite_jump_tails(b: &mut Block, ctx: &ExtractCtx) -> Result<(), Stage7Error> {
    rewrite_jump_block(b, ctx, JumpHandoff::BlockValue)
}

fn rewrite_jump_block(
    b: &mut Block,
    ctx: &ExtractCtx,
    handoff: JumpHandoff,
) -> Result<(), Stage7Error> {
    for s in b.stmts.iter_mut() {
        rewrite_jump_in_stmt(s, ctx, handoff)?;
    }
    rewrite_jump_in_tail(&mut b.tail, ctx, handoff)?;
    Ok(())
}

fn rewrite_jump_in_stmt(
    s: &mut Stmt,
    ctx: &ExtractCtx,
    enclosing_handoff: JumpHandoff,
) -> Result<(), Stage7Error> {
    let handoff = match enclosing_handoff {
        JumpHandoff::UnsupportedOperand => JumpHandoff::UnsupportedOperand,
        JumpHandoff::BlockValue | JumpHandoff::EarlyReturn => JumpHandoff::EarlyReturn,
    };
    match s {
        Stmt::Let { value, .. } => rewrite_jump_in_expr(value, ctx, handoff),
        Stmt::Eval(e) => rewrite_jump_in_expr(e, ctx, handoff),
    }
}

fn rewrite_jump_in_tail(
    t: &mut BlockTail,
    ctx: &ExtractCtx,
    handoff: JumpHandoff,
) -> Result<(), Stage7Error> {
    let new_tail = match t {
        BlockTail::Value(e) => {
            rewrite_jump_in_expr(e, ctx, handoff)?;
            return Ok(());
        }
        BlockTail::Abort { code } => {
            rewrite_jump_in_expr(code, ctx, JumpHandoff::UnsupportedOperand)?;
            return Ok(());
        }
        BlockTail::Return(value) => {
            rewrite_jump_in_expr(value, ctx, JumpHandoff::UnsupportedOperand)?;
            return Ok(());
        }
        BlockTail::ReturnFromBlock { value, .. } => {
            rewrite_jump_in_expr(value, ctx, JumpHandoff::UnsupportedOperand)?;
            return Ok(());
        }
        BlockTail::Break { level, value } => {
            if matches!(handoff, JumpHandoff::UnsupportedOperand) {
                return Err(Stage7Error::JumpInOperand);
            }
            let frame = ctx.loop_stack.iter().rev().nth(*level as usize).ok_or(
                Stage7Error::JumpLevelOutOfBounds {
                    level: *level,
                    depth: ctx.loop_stack.len() as u32,
                },
            )?;
            let mut args = unpack_jump_args(value.as_ref(), frame.iter_local_count)?;
            for c in &frame.after_captures {
                args.push(Expr::Var(c.clone()));
            }
            let call = Expr::Call {
                fun: frame.after_id,
                type_args: ctx
                    .parent_type_params
                    .iter()
                    .enumerate()
                    .map(|(i, _)| Type::TypeParam(i as u16))
                    .collect(),
                args,
            };
            match handoff {
                JumpHandoff::BlockValue => BlockTail::Value(call),
                JumpHandoff::EarlyReturn => BlockTail::Return(Box::new(call)),
                JumpHandoff::UnsupportedOperand => unreachable!(),
            }
        }
        BlockTail::Continue { level, value } => {
            if matches!(handoff, JumpHandoff::UnsupportedOperand) {
                return Err(Stage7Error::JumpInOperand);
            }
            let frame = ctx.loop_stack.iter().rev().nth(*level as usize).ok_or(
                Stage7Error::JumpLevelOutOfBounds {
                    level: *level,
                    depth: ctx.loop_stack.len() as u32,
                },
            )?;
            let mut args = unpack_jump_args(value.as_ref(), frame.iter_local_count)?;
            for c in &frame.body_captures {
                args.push(Expr::Var(c.clone()));
            }
            let call = Expr::Call {
                fun: frame.body_id,
                type_args: ctx
                    .parent_type_params
                    .iter()
                    .enumerate()
                    .map(|(i, _)| Type::TypeParam(i as u16))
                    .collect(),
                args,
            };
            match handoff {
                JumpHandoff::BlockValue => BlockTail::Value(call),
                JumpHandoff::EarlyReturn => BlockTail::Return(Box::new(call)),
                JumpHandoff::UnsupportedOperand => unreachable!(),
            }
        }
    };
    *t = new_tail;
    Ok(())
}

fn rewrite_jump_in_expr(
    e: &mut Expr,
    ctx: &ExtractCtx,
    handoff: JumpHandoff,
) -> Result<(), Stage7Error> {
    match e {
        Expr::Borrow { step, base } => {
            for __pe in step.exprs_mut() {
                rewrite_jump_in_expr(__pe, ctx, JumpHandoff::UnsupportedOperand)?;
            }
            rewrite_jump_in_expr(base, ctx, JumpHandoff::UnsupportedOperand)
        }
        Expr::Update { step, base, value } => {
            for __pe in step.exprs_mut() {
                rewrite_jump_in_expr(__pe, ctx, JumpHandoff::UnsupportedOperand)?;
            }
            rewrite_jump_in_expr(base, ctx, JumpHandoff::UnsupportedOperand)?;
            rewrite_jump_in_expr(value, ctx, JumpHandoff::UnsupportedOperand)
        }
        Expr::Var(_)
        | Expr::Const(_)
        | Expr::Unit
        | Expr::BorrowLoc(_)
        | Expr::BorrowGlobal(_)
        | Expr::WriteBack { .. }
        | Expr::IsParent { .. } => Ok(()),
        Expr::BinOp { lhs, rhs, .. } => {
            rewrite_jump_in_expr(lhs, ctx, JumpHandoff::UnsupportedOperand)?;
            rewrite_jump_in_expr(rhs, ctx, JumpHandoff::UnsupportedOperand)
        }
        Expr::UnOp { operand, .. } => {
            rewrite_jump_in_expr(operand, ctx, JumpHandoff::UnsupportedOperand)
        }
        Expr::BitOp(op) => match op {
            crate::ir::ops::BitOp::Extract { operand, .. }
            | crate::ir::ops::BitOp::ZeroExtend { operand, .. }
            | crate::ir::ops::BitOp::SignExtend { operand, .. } => {
                rewrite_jump_in_expr(operand, ctx, JumpHandoff::UnsupportedOperand)
            }
            crate::ir::ops::BitOp::Concat { high, low } => {
                rewrite_jump_in_expr(high, ctx, JumpHandoff::UnsupportedOperand)?;
                rewrite_jump_in_expr(low, ctx, JumpHandoff::UnsupportedOperand)
            }
        },
        Expr::Call { args, .. } | Expr::Tuple(args) | Expr::Pack { fields: args, .. } => {
            for a in args {
                rewrite_jump_in_expr(a, ctx, JumpHandoff::UnsupportedOperand)?;
            }
            Ok(())
        }
        Expr::Unpack { value, .. }
        | Expr::Field { base: value, .. }
        | Expr::ReadRef(value)
        | Expr::ToProp(value)
        | Expr::ToBool(value) => rewrite_jump_in_expr(value, ctx, JumpHandoff::UnsupportedOperand),
        Expr::If {
            cond,
            then_branch,
            else_branch,
        } => {
            rewrite_jump_in_expr(cond, ctx, JumpHandoff::UnsupportedOperand)?;
            rewrite_jump_block(then_branch, ctx, handoff)?;
            rewrite_jump_block(else_branch, ctx, handoff)
        }
        Expr::Match {
            selector, cases, ..
        } => {
            rewrite_jump_in_expr(selector, ctx, JumpHandoff::UnsupportedOperand)?;
            for arm in cases.iter_mut() {
                rewrite_jump_block(&mut arm.body, ctx, handoff)?;
            }
            Ok(())
        }
        Expr::While { .. } => {
            // After stage 7 has run on this body, any While here
            // would have already been extracted (collapsed to a
            // Call). Don't descend.
            Ok(())
        }
        Expr::WriteRef { reference, value } => {
            rewrite_jump_in_expr(reference, ctx, JumpHandoff::UnsupportedOperand)?;
            rewrite_jump_in_expr(value, ctx, JumpHandoff::UnsupportedOperand)
        }
        Expr::Quantifier { body, .. } => {
            rewrite_jump_block(body, ctx, JumpHandoff::UnsupportedOperand)
        }
        Expr::LabeledBlock { body, .. } => rewrite_jump_block(body, ctx, handoff),
    }
}

/// Convert a `Break/Continue { value }` payload into the Call args
/// for the matching helper.
///
/// - `count == 0`: payload should be `Unit`-shaped; emit `[]`.
/// - `count == 1`: payload IS the single arg.
/// - `count > 1`: payload must be a `Tuple` of matching arity; splat.
///
/// Returns `Err(Stage7Error::JumpValueArityMismatch)` for mismatched
/// shapes -- silently dropping args would produce a malformed
/// downstream Call that the renderer can't lower.
fn unpack_jump_args(value: &Expr, count: usize) -> Result<Vec<Expr>, Stage7Error> {
    if count == 0 {
        return Ok(vec![]);
    }
    if count == 1 {
        // Single-arg loops accept either the bare value or a 1-tuple.
        if let Expr::Tuple(elems) = value {
            if elems.len() == 1 {
                return Ok(elems.clone());
            }
        }
        return Ok(vec![value.clone()]);
    }
    // count > 1: must be a Tuple of matching arity.
    if let Expr::Tuple(elems) = value {
        if elems.len() == count {
            return Ok(elems.clone());
        }
    }
    Err(Stage7Error::JumpValueArityMismatch {
        expected: count,
        carried: format!("{value:?}"),
    })
}

fn parent_name(ctx: &ExtractCtx) -> String {
    ctx.program.functions[&ctx.parent_fid].name.clone()
}

/// Rewrite the body's outermost `Value(V)` leaf tails as
/// `Value(Call(body_id, args))` -- the IR's implicit-continue
/// convention.
///
/// Per `plans/lean-pipeline/ir.md` "Body tail convention (post-stage-5)":
/// stage 5 normalises a `BlockTail::Continue { level: 0, value: V }` at
/// the loop body's outermost tail to `BlockTail::Value(V)`. Stage 7
/// must un-normalise it: any `Value(V)` leaf inside the body that
/// isn't already a Call to a known loop helper is an implicit
/// continue, and gets wrapped into `Value(Call(body_id, args))` where
/// `args` is `V` splatted to the iter-local arity plus the body's
/// captures forwarded as `Var(c)`.
///
/// Leaves are detected as tails whose `Value(e)` `e` is neither
/// `If`/`Match` (recurse into arms) nor a Call to a known loop
/// helper (already an exit/recurse). Non-Value tails are left alone
/// -- they're handled by `rewrite_jump_tails` (Break/Continue) or
/// pass through (Return/Abort).
fn rewrite_implicit_continues(b: &mut Block, ctx: &ExtractCtx) -> Result<(), Stage7Error> {
    rewrite_implicit_continues_tail(&mut b.tail, ctx)
}

fn rewrite_implicit_continues_tail(t: &mut BlockTail, ctx: &ExtractCtx) -> Result<(), Stage7Error> {
    let value_e = match t {
        BlockTail::Value(e) => e,
        _ => return Ok(()),
    };
    match value_e {
        Expr::If {
            then_branch,
            else_branch,
            ..
        } => {
            rewrite_implicit_continues(then_branch, ctx)?;
            rewrite_implicit_continues(else_branch, ctx)?;
            Ok(())
        }
        Expr::Match { cases, .. } => {
            for MatchArm { body, .. } in cases.iter_mut() {
                rewrite_implicit_continues(body, ctx)?;
            }
            Ok(())
        }
        Expr::Call { fun, .. } if is_known_loop_helper(*fun, ctx) => Ok(()),
        _ => {
            // Implicit continue -- replace the Value(V) tail with
            // Value(Call(body_id, [V splatted] ++ captures)).
            let frame = ctx
                .loop_stack
                .last()
                .expect("rewrite_implicit_continues called inside extract_while; frame pushed");
            let v = std::mem::replace(value_e, Expr::Unit);
            let mut args = unpack_jump_args(&v, frame.iter_local_count)?;
            for c in &frame.body_captures {
                args.push(Expr::Var(c.clone()));
            }
            *t = BlockTail::Value(Expr::Call {
                fun: frame.body_id,
                type_args: ctx
                    .parent_type_params
                    .iter()
                    .enumerate()
                    .map(|(i, _)| Type::TypeParam(i as u16))
                    .collect(),
                args,
            });
            Ok(())
        }
    }
}

/// True if `fid` is a Call target that should be treated as already
/// handled by stage 7 and not re-wrapped as an implicit continue.
///
/// This covers two cases:
///
/// 1. Body/after FunIds of any loop currently in `loop_stack` -- direct
///    continue/break sites in the loop being processed.
///
/// 2. **Any** LoopBody/LoopAfter helper extracted from the same parent
///    function. When stage 7 processes the outer of a nested loop pair,
///    `rewrite_block` has already collapsed the inner While into a
///    `Value(Call(inner_body_id, ...))` tail. That Call is a tail-call
///    handoff to the inner loop helper (which transitively continues
///    or terminates the outer loop via its own LoopAfter chain), not a
///    raw "iteration value" that needs splatting into the outer
///    body_id. Without this clause, `rewrite_implicit_continues` would
///    try to splat the Call as a Tuple of outer iter-locals and fail
///    with `JumpValueArityMismatch` -- the symptom that surfaced on
///    navi/lending's `get_user_claimable_rewards`.
fn is_known_loop_helper(fid: FunId, ctx: &ExtractCtx) -> bool {
    if ctx
        .loop_stack
        .iter()
        .any(|f| f.body_id == fid || f.after_id == fid)
    {
        return true;
    }
    if let Some(f) = ctx.program.functions.get(&fid) {
        if let FunctionKind::LoopBody { parent, .. } | FunctionKind::LoopAfter { parent, .. } =
            &f.kind
        {
            return *parent == ctx.parent_fid;
        }
    }
    false
}

impl<'p> ExtractCtx<'p> {
    /// O(1) FunId allocation. The counter was seeded in `run()`
    /// from the program's max-existing-id + 1; this just hands
    /// out the next slot.
    fn alloc_fid(&mut self) -> FunId {
        let id = self.next_fid;
        self.next_fid = self
            .next_fid
            .checked_add(1)
            .expect("FunId counter overflowed");
        id
    }
}

/// Nested-loop helpers were typed from the enclosing loop's placeholder, i.e.
/// `parent_return_type` (see [`insert_placeholder`]); wrong when the enclosing
/// loop is not the function tail. Now that the enclosing helpers are real, give
/// each such helper the type of the loop helper its tail calls. Descending id
/// order resolves a chain (`while_1` -> `while_1.after` -> `while_0`) in one pass.
fn retype_placeholder_typed_nested_helpers(ctx: &mut ExtractCtx, after_id: FunId) {
    fn tail_callees(t: &BlockTail, out: &mut Vec<FunId>) {
        let BlockTail::Value(e) = t else { return };
        match e {
            Expr::Tuple(items) if items.len() == 1 => {
                tail_callees(&BlockTail::Value(items[0].clone()), out)
            }
            Expr::Call { fun, .. } => out.push(*fun),
            Expr::If {
                then_branch,
                else_branch,
                ..
            } => {
                tail_callees(&then_branch.tail, out);
                tail_callees(&else_branch.tail, out);
            }
            Expr::Match { cases, .. } => cases.iter().for_each(|c| tail_callees(&c.body.tail, out)),
            _ => {}
        }
    }
    let parent = ctx.parent_fid;
    let is_loop_helper = |f: &Function| matches!(f.kind, FunctionKind::LoopBody { parent: p, .. } | FunctionKind::LoopAfter { parent: p, .. } if p == parent);
    let nested: Vec<FunId> = ctx
        .program
        .functions
        .range(after_id + 1..)
        .filter(|(_, f)| is_loop_helper(f) && f.signature.return_type == ctx.parent_return_type)
        .map(|(id, _)| *id)
        .rev()
        .collect();
    for id in nested {
        let mut callees = Vec::new();
        tail_callees(&ctx.program.functions[&id].body.tail, &mut callees);
        let ty = callees
            .into_iter()
            .filter(|c| *c != id)
            .find_map(|c| ctx.program.functions.get(&c).filter(|f| is_loop_helper(f)))
            .map(|f| f.signature.return_type.clone());
        if let Some(ty) = ty {
            ctx.program
                .functions
                .get_mut(&id)
                .unwrap()
                .signature
                .return_type = ty;
        }
    }
}

/// Insert a placeholder so `alloc_fid` for sibling helpers picks up
/// fresh ids without colliding. Stage 7 overwrites this immediately
/// once the real Function is built.
fn insert_placeholder(ctx: &mut ExtractCtx, id: FunId, kind: FunctionKind) {
    let placeholder = Function {
        module: ctx.parent_module,
        name: format!("placeholder_{id}"),
        signature: Signature {
            type_params: vec![],
            params: vec![],
            // Use the parent function's return type, not `Unit`. When
            // an INNER nested while is extracted, its
            // `rewrite_implicit_continues` wraps its after-block's
            // tail as `Call(outer_body_id, ...)`. The inner's
            // `helper_return_type` is then derived from `type_of` on
            // that Call -- which looks up `outer_body_id` in
            // `program.functions` and reads the placeholder's
            // signature. With a `Unit` placeholder, the inner's
            // helper is typed `Unit` (wrong), and downstream type-
            // checking fails: the outer's body tail-calls the inner
            // expecting the outer's `RetType`, gets `Unit`. The real
            // outer body's `helper_return_type` is derived from its
            // own after_body's tail later, which in practice equals
            // the parent function's return type whenever the outer
            // while sits at function-tail position (the common case
            // that bites Skip_list / Linked_table / Switchboard
            // Aggregator). For non-tail-position outer whiles the
            // real type may differ; downstream type-of resolution
            // may still produce a fixable diff but at least the
            // common case stops mis-typing inner helpers as `Unit`.
            return_type: ctx.parent_return_type.clone(),
        },
        body: Block {
            stmts: vec![],
            tail: BlockTail::Value(Expr::Unit),
        },
        kind,
        effects: crate::ir::Effects::CONSERVATIVE,
        explicit_pure: false,
    };
    ctx.program.functions.insert(id, placeholder);
}

fn map_type_err(err: TypeOfError) -> Stage7Error {
    // For now, conflate all type-of failures into a single error.
    // A richer mapping can be added if specific failures need
    // differentiation at the postcondition / driver level.
    if std::env::var("FOXY_TRACE_STAGE7").is_ok() {
        eprintln!("stage7 map_type_err: {:?}", err);
    }
    Stage7Error::UnexpectedWhile
}

fn pass_through_world_capture(
    scope: &BTreeMap<VarId, Type>,
    binder_types: &[Type],
    world_id: Option<StructId>,
) -> Option<VarId> {
    let world_id = world_id?;
    if !binder_types
        .iter()
        .any(|ty| crate::stage_04_effects::common::is_world_type(ty, world_id))
    {
        return current_world_var(scope, world_id);
    }
    scope
        .iter()
        .filter(|(_, ty)| crate::stage_04_effects::common::is_world_type(ty, world_id))
        .filter_map(|(var, _)| {
            crate::ir::names::world_ssa_generation(var.as_ref()).map(|generation| (generation, var))
        })
        .min_by(|(left_generation, left), (right_generation, right)| {
            left_generation
                .cmp(right_generation)
                .then_with(|| left.cmp(right))
        })
        .map(|(_, var)| var.clone())
        .or_else(|| {
            scope
                .iter()
                .find(|(_, ty)| crate::stage_04_effects::common::is_world_type(ty, world_id))
                .map(|(var, _)| var.clone())
        })
}

#[cfg(test)]
mod world_capture_tests {
    use super::*;

    #[test]
    fn current_world_uses_numeric_ssa_generation() {
        let world_id = 7;
        let world_ty = Type::Struct {
            struct_id: world_id,
            type_args: Vec::new(),
        };
        let scope = BTreeMap::from([
            (VarId::from("world_2"), world_ty.clone()),
            (VarId::from("world_10"), world_ty),
            (VarId::from("value"), Type::UInt(64)),
        ]);

        assert_eq!(
            current_world_var(&scope, world_id).as_deref(),
            Some("world_10")
        );
    }

    #[test]
    fn world_iter_local_preserves_entry_snapshot_instead_of_live_snapshot() {
        let world_id = 7;
        let world_ty = Type::Struct {
            struct_id: world_id,
            type_args: Vec::new(),
        };
        let scope = BTreeMap::from([
            (VarId::from("world_0"), world_ty.clone()),
            (VarId::from("world_1"), world_ty.clone()),
        ]);

        assert_eq!(
            pass_through_world_capture(&scope, &[Type::UInt(64)], Some(world_id)).as_deref(),
            Some("world_1")
        );
        assert_eq!(
            pass_through_world_capture(&scope, &[world_ty], Some(world_id)),
            Some(VarId::from("world_0"))
        );
    }
}
