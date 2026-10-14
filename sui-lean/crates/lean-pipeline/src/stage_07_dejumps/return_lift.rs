//! Inner-Return lift via continuation tail-function extraction.
//!
//! See `plans/lean-pipeline/stage-07-rewrite.md` task #26.
//!
//! ## Problem
//!
//! Phase 1's callee-aborts splice produces inner `BlockTail::Return(v)`
//! at the Aborted arm of a Match. Inner Returns cannot be represented
//! faithfully in a pure Lean expression, so both the postcondition and
//! renderer reject any that survive this pass.
//!
//! ## Algorithm
//!
//! For `.aborts` companions and source/test/helper bodies with early returns,
//! iteratively lift supported inner Returns out of their surrounding context.
//! The normal strategy extracts a continuation helper. When doing that would
//! sever a nested mutable borrow, statement-position control flow instead uses
//! an in-place `AbortResult<return_type>` carrier and runs the continuation
//! exactly once on fallthrough. Any unsupported residual is rejected at the
//! stage boundary.
//!
//! The unit of lifting: a `Stmt::Eval(<expr>)` whose `<expr>`
//! contains a Match-with-Return-arm. We split the enclosing block
//! at this stmt, allocate a continuation helper `f.cont_N` for the
//! post-stmt code, and rewrite the enclosing block:
//!
//! - `stmts` becomes pre-stmts only.
//! - `tail` becomes `Value(<expr_with_lifted_Match>)`, where the
//!   Match's arms are rewritten:
//!   - Return-arm: `Block { tail: Value(payload) }` (delivers the
//!     payload as the block's value -- which propagates to the
//!     function tail via subsequent lifts if needed).
//!   - Non-Return-arm: `Block { tail: Value(Call(f.cont_N,
//!     captures)) }` (tail-calls the helper to continue execution).
//!
//! If `<expr>` is an If/Match wrapping the Match-with-Return (e.g.
//! `If { then: Block{tail: Value(Match...)}, else: Block{tail: Value(Match...)} }`),
//! we recurse into the arms, lifting each Match independently. All
//! arms then deliver AbortResult; the wrapping If/Match's value
//! unifies at AbortResult.
//!
//! After lifting, the block's tail-value is AbortResult instead of
//! whatever-it-was-before. This may require lifting at the
//! enclosing level too (recursive bubble-up). The iteration loops
//! until no inner Returns remain.

use std::collections::{BTreeMap, BTreeSet};

use crate::ir::analysis::type_of::{strip_singleton_tuple, substitute_type_params, type_of};
use crate::ir::expr::{Block, BlockTail, Expr, MatchArm, Stmt};
use crate::ir::function::{Function, FunctionKind, Param, Signature, SpecKind};
use crate::ir::ty::Type;
use crate::ir::{Effects, FunId, Program, StructId, VarId};

use super::option_aborts::{
    ensure_return_flow_struct, is_abort_result_type, ABORT_CODE_QUALIFIED_NAME, OPTION_NONE_TAG,
    OPTION_QUALIFIED_NAME, OPTION_SOME_TAG, RETURN_FLOW_CONTINUE_TAG, RETURN_FLOW_RETURNED_TAG,
};
use super::{find_world_struct_id, Stage7Error};

pub fn run(program: &mut Program) -> Result<(), Stage7Error> {
    let option_id = match program.struct_id_by_qualified_name(OPTION_QUALIFIED_NAME) {
        Some(id) => id,
        None => return Ok(()),
    };
    let abort_code_id = match program.struct_id_by_qualified_name(ABORT_CODE_QUALIFIED_NAME) {
        Some(id) => id,
        None => return Ok(()),
    };
    let return_flow_id = ensure_return_flow_struct(program);

    let mut processed: BTreeSet<FunId> = BTreeSet::new();
    const OUTER_MAX_ITER: usize = 64;
    for _ in 0..OUTER_MAX_ITER {
        let pending: Vec<FunId> = program
            .functions
            .iter()
            .filter_map(|(id, f)| {
                if processed.contains(id) {
                    return None;
                }
                match f.kind {
                    // The .aborts companion itself.
                    FunctionKind::Spec {
                        kind: SpecKind::Aborts,
                        ..
                    } => Some(*id),
                    // Source or test bodies carrying an inner `Return` -- an early
                    // `return` nested inside a non-tail statement-position
                    // `if`/`match`. The renderer only delivers an inner
                    // `Return` correctly when it sits in a *tail* position;
                    // a `Return` inside a discarded `Stmt::Eval(If { .. })`
                    // used to be silently dropped (the whole if rendered as
                    // `()`), so the function fell through to its real tail and
                    // returned the WRONG value. The renderer now rejects any
                    // residual. `oracle::strategy::
                    // validate_price_range_and_history`'s third
                    // `return false` (nested two `if`s deep) is the
                    // motivating case. Lifting routes every inner return
                    // through the same continuation extraction the
                    // .aborts companions use; the make_no_abort
                    // tail-handler is gated on the AbortResult return
                    // type below, so a source body keeps its real tail
                    // value.
                    //
                    // Effectful (`LocalMut`/`GlobalMut`) source/test bodies are
                    // ELIGIBLE too: stage_04_effects already augments their
                    // inner returns with the threaded mutables + world
                    // (`return ($v, $cfg, $oracle, world_n)`), so the lift
                    // only needs to PRESERVE those tuples. Statement-position
                    // shapes that cannot safely capture those threads use the
                    // in-place early-return carrier; unsupported value-binding
                    // shapes remain fail-closed.
                    //
                    // The one whole-function exclusion lives here: a
                    // self-recursive body (calls itself by name). Splitting an
                    // inner return out of it hoists the recursive call into a
                    // `.cont_*` helper, breaking the by-name self-call cycle
                    // the renderer relies on to emit `partial def` (Lean's
                    // termination check then rejects the `def`).
                    // `sui::priority_queue::max_heapify_recursive` (reached via
                    // SuiSystem staking in every volo test) is the case.
                    FunctionKind::Source | FunctionKind::Test { .. }
                        if block_contains_match_with_return_arm(&f.body)
                            && !crate::render::function::body_calls_self_by_name(
                                &f.body, &f.module, &f.name, program,
                            ) =>
                    {
                        Some(*id)
                    }
                    // Synthetic continuations created by an earlier
                    // lift (they inherit AbortResult return type
                    // from their parent .aborts).
                    FunctionKind::Synthetic
                        if is_abort_result_type(
                            &f.signature.return_type,
                            option_id,
                            abort_code_id,
                        ) || block_contains_match_with_return_arm(&f.body) =>
                    {
                        Some(*id)
                    }
                    // LoopBody / LoopAfter helpers of an .aborts
                    // companion. After loop_extract runs ahead of
                    // return_lift (phase 3a), these helpers inherit
                    // the parent's return type via loop_extract's
                    // Unit -> parent_return_type override. Any inner
                    // Return inside what used to be a while body now
                    // sits inside one of these helpers and needs the
                    // same continuation lift the .aborts companion
                    // gets.
                    FunctionKind::LoopBody { .. } | FunctionKind::LoopAfter { .. }
                        if is_abort_result_type(
                            &f.signature.return_type,
                            option_id,
                            abort_code_id,
                        ) || block_contains_match_with_return_arm(&f.body) =>
                    {
                        // Either an .aborts loop helper (AbortResult return),
                        // OR a REGULAR loop helper carrying an inner Return
                        // that the renderer would otherwise drop -- e.g.
                        // cetus `is_right_order`'s `while_0`, whose in-loop
                        // `return false` is masked inside the loop body. The
                        // generic let-lift path delivers the Return value as
                        // the helper's (= function's) result; the make_no_abort
                        // tail-handler is gated on .aborts below so a non-aborts
                        // body keeps its real tail value.
                        Some(*id)
                    }
                    _ => None,
                }
            })
            .collect();
        if pending.is_empty() {
            break;
        }
        for fid in pending {
            lift_function(program, fid, option_id, abort_code_id, return_flow_id)?;
            processed.insert(fid);
        }
    }
    Ok(())
}

fn lift_function(
    program: &mut Program,
    fid: FunId,
    option_id: StructId,
    abort_code_id: StructId,
    return_flow_id: StructId,
) -> Result<(), Stage7Error> {
    let world_id = find_world_struct_id(program);
    // Iterate: keep lifting one inner Return at a time until stable.
    // Cap iterations to avoid infinite loops on pathological IR.
    //
    // `next_cont_slot` MUST persist across iterations so that
    // successive lifts of the same parent function produce
    // distinctly-named continuations (`f.cont_0`, `f.cont_1`, ...).
    // It also doubles as the `__ac_N` var-name counter; both naming
    // schemes share the slot so collisions across function and
    // variable identifiers in the rendered Lean are avoided.
    let mut next_cont_slot: u32 = 0;
    // Taken ONCE, from the whole body, before anything is lifted. Each
    // lift MOVES code into a `cont_N` helper, so a set recomputed per
    // iteration stops seeing the `*v` that has already migrated out --
    // and it is precisely the migrated ones that become continuation
    // parameters. navi `incentive::base_claim_reward.aborts` is that
    // shape: `$t10_2` is bound in the parent, its only `*$t10_2` ends up
    // two continuations deep.
    let deref_vars = dereferenced_vars(&program.functions[&fid].body);
    const MAX_ITER: usize = 1024;
    for _ in 0..MAX_ITER {
        let parent_name = program.functions[&fid].name.clone();
        let parent_module = program.functions[&fid].module;
        let parent_type_params = program.functions[&fid].signature.type_params.clone();
        let ret_type = program.functions[&fid].signature.return_type.clone();
        // Typed scope: var -> type. Seed with function params.
        let initial_scope: BTreeMap<VarId, Type> = program.functions[&fid]
            .signature
            .params
            .iter()
            .map(|p| (p.var.clone(), p.ty.clone()))
            .collect();
        // Stage-7 merge expressions can be intentionally non-inferable in
        // the forward direction (an early-return arm has the function result
        // type while the normal arm supplies a multi-slot local tuple). The
        // renderer's backward target analysis recovers those SSA slot types
        // from their downstream uses; seed them here as supplementary facts.
        // SSA variable ids are unique, so this cannot capture or shadow a
        // different binding.
        let target_types = crate::render::rendered_var_target_types(
            &program.functions[&fid].body,
            &program.functions[&fid].signature.return_type,
        );
        let next_fid = program.next_function_id();

        let mut body = std::mem::replace(
            &mut program.functions.get_mut(&fid).unwrap().body,
            Block {
                stmts: Vec::new(),
                tail: BlockTail::Value(Expr::Unit),
            },
        );
        let parent_ghost_params = ghost_params_of(program, fid);
        let mut ctx = LiftCtx {
            program,
            parent_name,
            parent_ghost_params,
            parent_module,
            parent_type_params,
            ret_type,
            option_id,
            abort_code_id,
            return_flow_id,
            world_id,
            next_fid,
            next_cont_slot,
            target_types,
            deref_vars: deref_vars.clone(),
        };
        // A loop-abort propagation pass can retype a value-producing helper
        // after the first return-lift run.  Its call then appears as one arm
        // of a source-valued If/Match (the other arm still produces the
        // source value).  Treat that AbortResult-valued arm as the early exit
        // it represents so the ordinary lift below sends only the source arm
        // through the continuation.  Repeating this normalization on each
        // iteration lets the exit bubble through nested conditionals.
        promote_mixed_abort_value_arms(&mut body, &ctx);
        let lifted = walk_block(&mut body, &initial_scope, &mut ctx);
        next_cont_slot = ctx.next_cont_slot;
        program.functions.get_mut(&fid).unwrap().body = body;
        if !lifted {
            return Ok(());
        }
    }
    // Hit the iteration cap. Leave the residue for the stage postcondition,
    // which rejects it before rendering.
    Ok(())
}

fn promote_mixed_abort_value_arms(b: &mut Block, ctx: &LiftCtx) {
    for stmt in &mut b.stmts {
        match stmt {
            Stmt::Let { value, .. } | Stmt::Eval(value) => {
                promote_mixed_abort_value_expr(value, ctx)
            }
        }
    }
    match &mut b.tail {
        BlockTail::Value(value) => promote_mixed_abort_value_expr(value, ctx),
        BlockTail::Return(value)
        | BlockTail::Break { value, .. }
        | BlockTail::Continue { value, .. }
        | BlockTail::ReturnFromBlock { value, .. } => promote_mixed_abort_value_expr(value, ctx),
        BlockTail::Abort { code } => promote_mixed_abort_value_expr(code, ctx),
    }
}

fn promote_mixed_abort_value_expr(e: &mut Expr, ctx: &LiftCtx) {
    match e {
        Expr::If {
            then_branch,
            else_branch,
            ..
        } => {
            promote_mixed_abort_value_arms(then_branch, ctx);
            promote_mixed_abort_value_arms(else_branch, ctx);
            let then_abort = matches!(
                &then_branch.tail,
                BlockTail::Value(value) if value_is_abort_result(value, ctx)
            );
            let else_abort = matches!(
                &else_branch.tail,
                BlockTail::Value(value) if value_is_abort_result(value, ctx)
            );
            if then_abort != else_abort {
                if then_abort {
                    value_tail_to_return(then_branch);
                } else {
                    value_tail_to_return(else_branch);
                }
            }
        }
        Expr::Match { cases, .. } => {
            for arm in cases.iter_mut() {
                promote_mixed_abort_value_arms(&mut arm.body, ctx);
            }
            let abort_arms: Vec<bool> = cases
                .iter()
                .map(|arm| {
                    matches!(
                        &arm.body.tail,
                        BlockTail::Value(value) if value_is_abort_result(value, ctx)
                    )
                })
                .collect();
            if abort_arms.iter().any(|is_abort| *is_abort)
                && abort_arms.iter().any(|is_abort| !*is_abort)
            {
                for (arm, is_abort) in cases.iter_mut().zip(abort_arms) {
                    if is_abort {
                        value_tail_to_return(&mut arm.body);
                    }
                }
            }
        }
        _ => {}
    }
}

fn value_tail_to_return(b: &mut Block) {
    let old_tail = std::mem::replace(&mut b.tail, BlockTail::Value(Expr::Unit));
    b.tail = match old_tail {
        BlockTail::Value(value) => BlockTail::Return(Box::new(value)),
        other => other,
    };
}

struct LiftCtx<'p> {
    program: &'p mut Program,
    parent_name: String,
    /// The parent's ghost parameters, in the order stage 4 appended
    /// them (`stage_04_ghost::sort_ghost_set` -- the marker set's own
    /// order). Continuation captures are collected into a
    /// `BTreeSet<VarId>`, i.e. ordered by binder SPELLING, and that
    /// disagrees with the set order whenever one marker's name is a
    /// prefix of another's: with the SSA suffix,
    /// `__ghost_<X>Exists_0` sorts before `__ghost_<X>_0` because
    /// `'E'` (0x45) precedes `'_'` (0x5F). The two orders agreed only
    /// while the binders were `__ghost_<struct_id>` -- numeric and
    /// monotone with the set -- so the agreement was luck, and any
    /// rename of a ghost key struct would have broken it. Reordering
    /// the ghost captures against this list restores one ordering.
    parent_ghost_params: Vec<VarId>,
    parent_module: crate::ir::ModId,
    parent_type_params: Vec<String>,
    ret_type: Type,
    option_id: StructId,
    abort_code_id: StructId,
    return_flow_id: StructId,
    world_id: Option<StructId>,
    next_fid: FunId,
    next_cont_slot: u32,
    /// Backward consumer types are fallbacks only. They must never be mixed
    /// into the lexical RHS scope: doing so lets a future use retype the
    /// value currently being produced.
    target_types: BTreeMap<VarId, Type>,
    /// Vars this function already dereferences (`ReadRef(Var(v))`), taken
    /// from the body ONCE before the first lift. See
    /// [`stable_ssa_pattern_type`]: a slot the program has already been
    /// normalized against as a reference may not be retyped to the value.
    deref_vars: BTreeSet<VarId>,
}

impl<'p> LiftCtx<'p> {
    fn alloc_fid(&mut self) -> FunId {
        let id = self.next_fid;
        self.next_fid += 1;
        id
    }

    fn fresh_return_lift_var(&mut self) -> VarId {
        let slot = self.next_cont_slot;
        self.next_cont_slot += 1;
        format!("__return_lift_{slot}").into()
    }
}

/// Walk `b` looking for the first liftable Stmt::Eval (one whose
/// expression contains an inner Match-with-Return). Returns true if
/// a lift was performed. `scope` maps in-scope var ids to their
/// types (so we can size capture params correctly during a lift).
fn walk_block(b: &mut Block, scope: &BTreeMap<VarId, Type>, ctx: &mut LiftCtx) -> bool {
    // Find the first liftable stmt, accumulating the scope so we can size
    // bindings and choose a continuation strategy that preserves borrows.
    let mut lift_scope = scope.clone();
    let mut lift_site: Option<(usize, LiftStrategy)> = None;
    let mut blocked = BTreeSet::new();
    for (i, stmt) in b.stmts.iter().enumerate() {
        if stmt_contains_inner_return_match(stmt) {
            match lift_strategy(b, i, stmt, &lift_scope, ctx) {
                LiftDecision::Use(strategy) => {
                    lift_site = Some((i, strategy));
                    break;
                }
                LiftDecision::Block => {
                    blocked.insert(i);
                }
            }
        }
        extend_scope_with_stmt(
            stmt,
            &mut lift_scope,
            &ctx.target_types,
            &ctx.deref_vars,
            ctx.program,
        );
    }
    if let Some((i, strategy)) = lift_site {
        perform_lift(b, i, &lift_scope, ctx, strategy);
        return true;
    }
    // No top-level lift. Recurse into stmts' sub-expressions.
    let mut sub_scope = scope.clone();
    for (i, stmt) in b.stmts.iter_mut().enumerate() {
        if !blocked.contains(&i) && walk_stmt(stmt, &sub_scope, ctx) {
            return true;
        }
        extend_scope_with_stmt(
            stmt,
            &mut sub_scope,
            &ctx.target_types,
            &ctx.deref_vars,
            ctx.program,
        );
    }
    walk_tail(&mut b.tail, &sub_scope, ctx)
}

#[derive(Clone, Copy)]
enum LiftStrategy {
    ExtractContinuation,
    EarlyReturnCarrier,
    ValueReturnCarrier,
}

enum LiftDecision {
    Use(LiftStrategy),
    Block,
}

/// A continuation helper cannot safely capture a nested `&mut`: passing the
/// child borrow as an independent parameter detaches it from its parent and
/// can drop the write-back. A statement-position trigger in a function that
/// threads `&mut` state also cannot be lifted from an inner guard first: the
/// asymmetric-arm recovery can attach the shared continuation to only one
/// outer branch.
///
/// For either statement-position shape, encode the trigger's result as
/// `AbortResult<return_type>`: `Aborted(value)` means early return and
/// `NoAbort` means fall through. A single tail match then runs the original
/// continuation in place. The continuation is neither captured nor duplicated.
/// A real value-position let cannot use this carrier because its normal value
/// must survive; if it would sever a nested borrow, leave it for the fail-closed
/// stage postcondition.
fn lift_strategy(
    b: &Block,
    i: usize,
    stmt: &Stmt,
    scope: &BTreeMap<VarId, Type>,
    ctx: &LiftCtx,
) -> LiftDecision {
    if is_abort_result_type(&ctx.ret_type, ctx.option_id, ctx.abort_code_id) {
        return LiftDecision::Use(LiftStrategy::ExtractContinuation);
    }
    let severs_nested_borrow = lift_severs_nested_borrow(b, i, scope);
    if stmt_routes_to_eval_lift(stmt) && (severs_nested_borrow || ty_threads_mut(&ctx.ret_type)) {
        let expr = match stmt {
            Stmt::Eval(expr) | Stmt::Let { value: expr, .. } => expr,
        };
        return if carrier_conversion_supported(expr) {
            LiftDecision::Use(LiftStrategy::EarlyReturnCarrier)
        } else {
            LiftDecision::Use(LiftStrategy::ValueReturnCarrier)
        };
    }
    if severs_nested_borrow {
        if matches!(stmt, Stmt::Let { pattern, .. } if pattern.iter().any(Option::is_some)) {
            return LiftDecision::Use(LiftStrategy::ValueReturnCarrier);
        }
        return LiftDecision::Block;
    }
    LiftDecision::Use(LiftStrategy::ExtractContinuation)
}

/// Would lifting the inner Return at `b.stmts[i]` sever an outstanding
/// nested mutable borrow? The continuation (`stmts[i+1..]` + tail)'s free
/// vars that are bound in `scope` become `cont_N` parameters; if any of
/// them is a `MutableRef` whose `root` differs from its `inner` (a borrow
/// into a still-live parent, e.g. `&pool.validators[i]`), passing it as an
/// independent parameter detaches it from that parent and drops the
/// write-back. Vars bound *inside* the continuation are not free in it, so
/// a borrow created after the return point (which the cont owns outright)
/// does not trip this check.
fn lift_severs_nested_borrow(b: &Block, i: usize, scope: &BTreeMap<VarId, Type>) -> bool {
    let cont_body = Block {
        stmts: b.stmts[i + 1..].to_vec(),
        tail: b.tail.clone(),
    };
    crate::ir::analysis::free_vars::free_vars(&cont_body)
        .iter()
        .any(|v| matches!(scope.get(v), Some(Type::MutableRef { inner, root }) if inner != root))
}

fn ty_threads_mut(ty: &Type) -> bool {
    match ty {
        Type::MutableRef { .. } => true,
        Type::Tuple(elements) => elements.iter().any(ty_threads_mut),
        Type::Reference(inner) | Type::Vector(inner) => ty_threads_mut(inner),
        Type::Struct { type_args, .. } => type_args.iter().any(ty_threads_mut),
        _ => false,
    }
}

fn stmt_routes_to_eval_lift(stmt: &Stmt) -> bool {
    match stmt {
        Stmt::Eval(_) => true,
        Stmt::Let { pattern, .. } => !pattern.iter().any(Option::is_some),
    }
}

fn carrier_conversion_supported(expr: &Expr) -> bool {
    match expr {
        Expr::If {
            then_branch,
            else_branch,
            ..
        } => {
            carrier_block_conversion_supported(then_branch)
                && carrier_block_conversion_supported(else_branch)
        }
        Expr::Match { cases, .. } => cases
            .iter()
            .all(|arm| carrier_block_conversion_supported(&arm.body)),
        _ => true,
    }
}

fn carrier_block_conversion_supported(block: &Block) -> bool {
    for stmt in &block.stmts {
        if stmt_contains_inner_return_match(stmt) && !stmt_routes_to_eval_lift(stmt) {
            return false;
        }
        let expr = match stmt {
            Stmt::Eval(expr) | Stmt::Let { value: expr, .. } => expr,
        };
        if !carrier_conversion_supported(expr) {
            return false;
        }
    }
    match &block.tail {
        BlockTail::Value(expr) => carrier_conversion_supported(expr),
        _ => true,
    }
}

fn extend_scope_with_stmt(
    stmt: &Stmt,
    scope: &mut BTreeMap<VarId, Type>,
    target_types: &BTreeMap<VarId, Type>,
    deref_vars: &BTreeSet<VarId>,
    program: &Program,
) {
    if let Stmt::Let { pattern, value } = stmt {
        // Infer the value's type to size each pattern slot.
        let val_ty = infer_let_value_type(pattern, value, scope, target_types, deref_vars, program);
        bind_pattern(pattern, &val_ty, scope);
    }
}

/// Infer the type a `Stmt::Let`'s pattern is bound to.
///
/// The straightforward answer is `type_of(value)`. But a loop body's
/// merge `let [s0,..,sN] := If { then: <state branch>, else: <tail-call
/// branch> }` defeats it: the two branches have *different* tail types
/// (one delivers the `Tuple([..N..])` of carried state, the other
/// tail-calls a `Bool`-returning helper), so `type_of`'s
/// first-typeable-arm heuristic returns the scalar tail-call type
/// instead of the state tuple. Binding an N-slot pattern from that
/// scalar drops every slot to `Unit`, and those `Unit`s later become
/// mistyped continuation parameters (Lean "application type mismatch").
///
/// So: when the pattern is multi-slot and `type_of` does not yield a
/// `Tuple` of matching arity, look for the `If`/`Match` branch whose
/// tail *is* such a tuple (the state branch) and use it.
fn infer_let_value_type(
    pattern: &[Option<VarId>],
    value: &Expr,
    scope: &BTreeMap<VarId, Type>,
    target_types: &BTreeMap<VarId, Type>,
    deref_vars: &BTreeSet<VarId>,
    program: &Program,
) -> Type {
    // Backward target typing may pre-seed the SSA variables this very `let`
    // defines. They are not in scope on the RHS; leaving them visible makes
    // a branch tuple appear to have its future consumer type rather than the
    // value actually produced by that branch.
    let mut rhs_scope = scope.clone();
    for var in pattern.iter().flatten() {
        rhs_scope.remove(var);
    }
    let direct = type_of(value, &rhs_scope, program).ok();
    let stable_slot_type = stable_ssa_pattern_type(pattern, &rhs_scope);
    if let Some(t) = &direct {
        if pattern.len() == 1 {
            return stable_slot_type
                .filter(|stable| {
                    corrects_borrow_skew(t, stable)
                        && !strands_a_dereference(pattern, t, stable, deref_vars)
                })
                .unwrap_or_else(|| t.clone());
        }
        if let Type::Tuple(es) = t {
            if es.len() == pattern.len() {
                return stable_slot_type
                    .filter(|stable| {
                        corrects_borrow_skew(t, stable)
                            && !strands_a_dereference(pattern, t, stable, deref_vars)
                    })
                    .unwrap_or_else(|| t.clone());
            }
        }
    }
    // Stage-7 SSA bindings are unique, and `lift_function` seeds `scope`
    // with the renderer's backward target-type analysis.  When an early
    // return makes the RHS itself untypeable, recover the binding type from
    // those already-known pattern targets.  This is especially important for
    // generated writeback merges: their ordinary arm produces the local
    // state tuple while the other arm returns from the enclosing function.
    let target_type = if pattern.len() == 1 {
        pattern[0]
            .as_ref()
            .and_then(|var| target_types.get(var))
            .cloned()
    } else {
        pattern
            .iter()
            .map(|slot| slot.as_ref().and_then(|var| target_types.get(var)).cloned())
            .collect::<Option<Vec<_>>>()
            .map(Type::Tuple)
    };
    if pattern.len() > 1 {
        if let Some(t) = branch_tuple_type(
            value,
            pattern.len(),
            &rhs_scope,
            target_types,
            deref_vars,
            program,
        ) {
            return t;
        }
    }
    if let Some(ty) = target_type {
        return ty;
    }
    direct.unwrap_or_else(|| {
        panic!(
            "let value type must be inferable to size the lifted binding: pattern={pattern:?} value={value:#?} lexical_scope={rhs_scope:?} target_types={target_types:?}"
        )
    })
}

/// The stable-generation type is a CORRECTION for exactly one skew -- a merge
/// arm holding a BORROW of a carried slot (`&u64`) whose carrier is the value
/// (`u64`) -- so it may only replace a directly inferred type that agrees with
/// it once every reference wrapper is erased.
///
/// Without that guard the name-only heuristic in `stable_ssa_pattern_type`
/// retypes bindings that are not SSA generations of each other at all. Stage
/// 7's callee-abort temporaries are numbered `__c_0`, `__c_1`, ... from ONE
/// global counter (`aborts_variant`), not per-variable generations, so they
/// share the stem `__c` while holding unrelated types: every
/// `let __c_n = if __c_n+1 { Aborted .. } else { NoAbort }` was bound as the
/// preceding `*_aborts` predicate's `Bool`. `type_of` then failed on the
/// `match __c_n : AbortResult` that follows, `build_continuation_block` read
/// that failure as "this continuation is not AbortResult-typed", and discarded
/// the whole continuation tail into a `Stmt::Eval` behind a constant `NoAbort`
/// -- silently dropping the abort verdict AND the loop back-edge (momentum
/// `binary_search.aborts` / `write.aborts`, 26 continuations in one package).
fn corrects_borrow_skew(direct: &Type, stable: &Type) -> bool {
    direct != stable && erase_references(direct) == erase_references(stable)
}

/// ...and even a correction of exactly that shape may only be applied to a
/// slot NOTHING has already dereferenced.
///
/// `operand_normalization` (Move's auto-deref, `NormalizeMode::Aborting`)
/// runs post-SSA and BEFORE this stage. It wraps every reference-typed
/// arithmetic operand in a `ReadRef` using `type_of`'s reading of the slot
/// -- so by the time we get here the program has already been committed to
/// that reading. Demoting `&T` to `T` afterwards leaves the `ReadRef`
/// standing on a value and `ir-type-inference-succeeds` fails with
/// `MalformedAccess { ReadRef of non-reference type .. }`; the renderer
/// erases references, so nothing downstream ever reports the disagreement.
///
/// navi `lending_core::incentive` is the measured case, six functions in one
/// package. `earned`'s `let user_acc_rewards_paid = 0; if (..) {
/// user_acc_rewards_paid = *table::borrow(..) }` is an SSA merge of a
/// `&u256` arm and a `u256` arm; stage 2 elides Move's implicit deref, so
/// `type_of` answers `&u256` off the borrow arm, `operand_normalization`
/// emits `BoundedU256_sub(*$t35_0, *$t12_2)`, and the correction below then
/// retyped `$t12_2` to `u256` as it became `earned.aborts.while_0.cont_0`'s
/// parameter. The `*` was left behind.
///
/// Declining is always safe: it restores exactly the pre-correction type,
/// which is the one every earlier stage already used.
fn strands_a_dereference(
    pattern: &[Option<VarId>],
    direct: &Type,
    stable: &Type,
    deref_vars: &BTreeSet<VarId>,
) -> bool {
    let dereferenced = |slot: &Option<VarId>| slot.as_ref().is_some_and(|v| deref_vars.contains(v));
    if !pattern.iter().any(dereferenced) {
        return false;
    }
    let (Some(direct_slots), Some(stable_slots)) = (
        slot_types(direct, pattern.len()),
        slot_types(stable, pattern.len()),
    ) else {
        // The two shapes do not line up slot-for-slot, so which binder the
        // demotion lands on is unknowable. Some binder is dereferenced;
        // decline.
        return true;
    };
    pattern
        .iter()
        .zip(direct_slots)
        .zip(stable_slots)
        .any(|((slot, from), to)| dereferenced(slot) && is_reference(from) && !is_reference(to))
}

fn slot_types(ty: &Type, arity: usize) -> Option<Vec<&Type>> {
    match ty {
        _ if arity == 1 => Some(vec![ty]),
        Type::Tuple(elements) if elements.len() == arity => Some(elements.iter().collect()),
        _ => None,
    }
}

fn is_reference(t: &Type) -> bool {
    matches!(t, Type::Reference(_) | Type::MutableRef { .. })
}

/// Vars the body reads through an explicit `*v`. This is the shape
/// `operand_normalization::wrap_if_ref` produces for a bare `Var` operand,
/// and the only one a slot retype can invalidate: a `ReadRef` over any
/// larger expression re-derives its own type from that expression.
fn dereferenced_vars(body: &Block) -> BTreeSet<VarId> {
    #[derive(Default)]
    struct Collect(BTreeSet<VarId>);

    impl crate::ir::visit::Visitor for Collect {
        fn visit_expr(&mut self, expr: &Expr) {
            if let Expr::ReadRef(inner) = expr {
                if let Expr::Var(v) = inner.as_ref() {
                    self.0.insert(v.clone());
                }
            }
            crate::ir::visit::walk_expr_default(self, expr);
        }
    }

    let mut collect = Collect::default();
    crate::ir::visit::Visitor::visit_block(&mut collect, body);
    collect.0
}

fn erase_references(t: &Type) -> Type {
    match t {
        Type::Reference(inner) | Type::MutableRef { inner, .. } => erase_references(inner),
        Type::Vector(inner) => Type::Vector(Box::new(erase_references(inner))),
        Type::Tuple(elems) => Type::Tuple(elems.iter().map(erase_references).collect()),
        Type::Struct {
            struct_id,
            type_args,
        } => Type::Struct {
            struct_id: *struct_id,
            type_args: type_args.iter().map(erase_references).collect(),
        },
        other => other.clone(),
    }
}

/// Loop extraction gives each carried slot a fresh numeric SSA suffix while
/// preserving its Move type.  A merge arm can temporarily hold a borrow of a
/// slot (for example `&u64`) even though the carried slot itself remains the
/// value (`u64`).  Recover that stable slot type from an earlier generation
/// instead of letting the borrow arm retype the carrier. Only applied through
/// `corrects_borrow_skew`, which refuses any candidate that is not that same
/// slot modulo reference wrappers.
fn stable_ssa_pattern_type(
    pattern: &[Option<VarId>],
    scope: &BTreeMap<VarId, Type>,
) -> Option<Type> {
    if pattern.is_empty() {
        return None;
    }
    let mut types = Vec::with_capacity(pattern.len());
    for slot in pattern {
        let var = slot.as_ref()?;
        let name: &str = var.as_ref();
        let (stem, suffix) = name.rsplit_once('_')?;
        suffix.parse::<u32>().ok()?;
        let ty = scope
            .iter()
            .filter_map(|(candidate, ty)| {
                let candidate: &str = candidate.as_ref();
                let (candidate_stem, candidate_suffix) = candidate.rsplit_once('_')?;
                if candidate_stem != stem {
                    return None;
                }
                Some((candidate_suffix.parse::<u32>().ok()?, ty))
            })
            .max_by_key(|(generation, _)| *generation)
            .map(|(_, ty)| ty.clone())?;
        types.push(ty);
    }
    if types.len() == 1 {
        types.pop()
    } else {
        Some(Type::Tuple(types))
    }
}

/// Find an `If`/`Match` branch whose tail value is a `Tuple` of exactly
/// `arity` elements (the loop-state branch of a merge `let`). Returns
/// that tuple type, or `None` if no branch matches.
fn branch_tuple_type(
    value: &Expr,
    arity: usize,
    scope: &BTreeMap<VarId, Type>,
    target_types: &BTreeMap<VarId, Type>,
    deref_vars: &BTreeSet<VarId>,
    program: &Program,
) -> Option<Type> {
    let consider = |b: &Block| -> Option<Type> {
        match block_value_type_lenient(b, scope, target_types, deref_vars, program) {
            Some(Type::Tuple(es)) if es.len() == arity => Some(Type::Tuple(es)),
            _ => find_tuple_type_in_block(b, arity, scope, target_types, deref_vars, program),
        }
    };
    match value {
        Expr::If {
            then_branch,
            else_branch,
            ..
        } => {
            let (normal, returning) = if !super::cont_inline::block_contains_return(then_branch) {
                (then_branch, else_branch)
            } else {
                (else_branch, then_branch)
            };
            consider(normal).or_else(|| consider(returning))
        }
        Expr::Match { cases, .. } => cases
            .iter()
            .filter(|arm| !super::cont_inline::block_contains_return(&arm.body))
            .chain(
                cases
                    .iter()
                    .filter(|arm| super::cont_inline::block_contains_return(&arm.body)),
            )
            .find_map(|arm| consider(&arm.body)),
        _ => None,
    }
}

fn find_tuple_type_in_block(
    block: &Block,
    arity: usize,
    scope: &BTreeMap<VarId, Type>,
    target_types: &BTreeMap<VarId, Type>,
    deref_vars: &BTreeSet<VarId>,
    program: &Program,
) -> Option<Type> {
    let mut local = scope.clone();
    for stmt in &block.stmts {
        let (pattern, value) = match stmt {
            Stmt::Let { pattern, value } => (Some(pattern.as_slice()), value),
            Stmt::Eval(value) => (None, value),
        };
        if let Some(found) =
            find_tuple_type_in_expr(value, arity, &local, target_types, deref_vars, program)
        {
            return Some(found);
        }
        if let Some(pattern) = pattern {
            let ty =
                infer_let_value_type(pattern, value, &local, target_types, deref_vars, program);
            bind_pattern(pattern, &ty, &mut local);
        }
    }
    match &block.tail {
        BlockTail::Value(value) => {
            find_tuple_type_in_expr(value, arity, &local, target_types, deref_vars, program)
        }
        BlockTail::Return(value)
        | BlockTail::Abort { code: value }
        | BlockTail::Break { value, .. }
        | BlockTail::Continue { value, .. }
        | BlockTail::ReturnFromBlock { value, .. } => {
            find_tuple_type_in_expr(value, arity, &local, target_types, deref_vars, program)
        }
    }
}

fn find_tuple_type_in_expr(
    expr: &Expr,
    arity: usize,
    scope: &BTreeMap<VarId, Type>,
    target_types: &BTreeMap<VarId, Type>,
    deref_vars: &BTreeSet<VarId>,
    program: &Program,
) -> Option<Type> {
    if let Ok(Type::Tuple(items)) = type_of(expr, scope, program) {
        if items.len() == arity {
            return Some(Type::Tuple(items));
        }
    }
    match expr {
        Expr::If {
            then_branch,
            else_branch,
            ..
        } => find_tuple_type_in_block(then_branch, arity, scope, target_types, deref_vars, program)
            .or_else(|| {
                find_tuple_type_in_block(
                    else_branch,
                    arity,
                    scope,
                    target_types,
                    deref_vars,
                    program,
                )
            }),
        Expr::Match { cases, .. } => cases.iter().find_map(|arm| {
            find_tuple_type_in_block(&arm.body, arity, scope, target_types, deref_vars, program)
        }),
        Expr::LabeledBlock { body, .. } => {
            find_tuple_type_in_block(body, arity, scope, target_types, deref_vars, program)
        }
        _ => None,
    }
}

/// Like `type_of::block_value_type`, but binds each `Stmt::Let` via
/// [`infer_let_value_type`] (so nested loop-state merge `let`s -- whose
/// value is an `If`/`Match` with divergent branch tails -- bind their
/// pattern from the state branch's tuple instead of erroring). Returns
/// `None` for a non-`Value` tail or any unresolved inner type. Mutually
/// recursive with `infer_let_value_type` over strictly smaller blocks.
fn block_value_type_lenient(
    b: &Block,
    scope: &BTreeMap<VarId, Type>,
    target_types: &BTreeMap<VarId, Type>,
    deref_vars: &BTreeSet<VarId>,
    program: &Program,
) -> Option<Type> {
    let mut local = scope.clone();
    for s in &b.stmts {
        if let Stmt::Let { pattern, value } = s {
            let vt =
                infer_let_value_type(pattern, value, &local, target_types, deref_vars, program);
            bind_pattern(pattern, &vt, &mut local);
        }
    }
    match &b.tail {
        BlockTail::Value(e) => type_of(e, &local, program).ok(),
        _ => None,
    }
}

/// Bind pattern slots into scope using inferred RHS type. Mirrors
/// the helper in stage_07_dejumps::loop_extract.
fn bind_pattern(pattern: &[Option<VarId>], val_ty: &Type, scope: &mut BTreeMap<VarId, Type>) {
    if pattern.len() == 1 {
        if let Some(v) = &pattern[0] {
            let bound = match val_ty {
                Type::Tuple(es) if es.len() == 1 => es[0].clone(),
                other => other.clone(),
            };
            scope.insert(v.clone(), bound);
        }
        return;
    }
    if let Type::Tuple(elems) = val_ty {
        if elems.len() == pattern.len() {
            for (slot, ty) in pattern.iter().zip(elems) {
                if let Some(v) = slot {
                    scope.insert(v.clone(), ty.clone());
                }
            }
        }
    }
}

fn walk_stmt(s: &mut Stmt, scope: &BTreeMap<VarId, Type>, ctx: &mut LiftCtx) -> bool {
    match s {
        Stmt::Let { value, .. } => walk_expr(value, scope, ctx),
        Stmt::Eval(e) => walk_expr(e, scope, ctx),
    }
}

fn walk_tail(t: &mut BlockTail, scope: &BTreeMap<VarId, Type>, ctx: &mut LiftCtx) -> bool {
    match t {
        BlockTail::Value(e) => walk_expr(e, scope, ctx),
        BlockTail::Abort { code } => walk_expr(code, scope, ctx),
        BlockTail::Return(v)
        | BlockTail::Break { value: v, .. }
        | BlockTail::Continue { value: v, .. } => walk_expr(v, scope, ctx),
        BlockTail::ReturnFromBlock { .. } => unreachable!(
            "BlockTail::ReturnFromBlock should be eliminated by stage 7 helper extraction"
        ),
    }
}

fn walk_expr(e: &mut Expr, scope: &BTreeMap<VarId, Type>, ctx: &mut LiftCtx) -> bool {
    match e {
        Expr::If {
            cond: _,
            then_branch,
            else_branch,
        } => walk_block(then_branch, scope, ctx) || walk_block(else_branch, scope, ctx),
        Expr::Match {
            struct_id,
            selector,
            cases,
        } => {
            // Arm bindings introduce fresh vars in scope. Type them from
            // the matched enum variant's field types (substituted with the
            // selector's type-args) -- NOT Type::Unit. A Unit-typed binding
            // later captured by a continuation lift produces a cont_N
            // parameter whose type disagrees with the variable actually
            // threaded at the call site (Lean "application type mismatch").
            // Mirrors `type_of`'s `Unpack` variant-field handling.
            let sid = *struct_id;
            let mut arm_binding_types: Vec<Vec<Type>> = Vec::with_capacity(cases.len());
            for arm in cases.iter() {
                arm_binding_types.push(variant_binding_types(
                    ctx,
                    sid,
                    selector,
                    arm.variant,
                    scope,
                ));
            }
            for (arm, binding_types) in cases.iter_mut().zip(arm_binding_types) {
                let mut arm_scope = scope.clone();
                for (idx, binding) in arm.bindings.iter().enumerate() {
                    let ty = binding_types
                        .get(idx)
                        .cloned()
                        .expect("match-arm binding has a resolved variant-field type");
                    arm_scope.insert(binding.clone(), ty);
                }
                if walk_block(&mut arm.body, &arm_scope, ctx) {
                    return true;
                }
            }
            false
        }
        // `Expr::While` is impossible at this phase: `loop_extract`
        // runs ahead of `return_lift` (phase 3a), so every while loop
        // has been hoisted into LoopBody/LoopAfter helpers before we
        // see the function body. If a While did survive, treating it
        // as "no-trigger" is harmless -- the postcondition check
        // catches stray Whiles in helper bodies.
        _ => false,
    }
}

/// Types of a Match arm's bindings: the matched enum variant's field
/// types, substituted with the selector's type-args. Falls back to the
/// unsubstituted field types when the selector type can't be resolved,
/// and to an empty vec for unknown structs / variants. A missing slot is an
/// internal invariant violation at the caller. Mirrors `type_of`'s `Unpack`
/// variant-field logic.
fn variant_binding_types(
    ctx: &LiftCtx,
    struct_id: StructId,
    selector: &Expr,
    variant: usize,
    scope: &BTreeMap<VarId, Type>,
) -> Vec<Type> {
    let s = match ctx.program.structs.get(&struct_id) {
        Some(s) => s,
        None => return Vec::new(),
    };
    let fields = match &s.variants {
        Some(_) => match s.variant_by_tag(variant) {
            Some(v) => &v.fields,
            None => return Vec::new(),
        },
        None => &s.fields,
    };
    let type_args = match type_of(selector, scope, ctx.program) {
        Ok(t) => enum_type_args(&t),
        Err(_) => Vec::new(),
    };
    fields
        .iter()
        .map(|f| substitute_type_params(&f.field_type, &type_args))
        .collect()
}

/// Extract an enum's type-args from a (possibly reference-wrapped,
/// singleton-tuple-wrapped) `Struct` type. Empty for non-struct types.
fn enum_type_args(t: &Type) -> Vec<Type> {
    match strip_singleton_tuple(t) {
        Type::Struct { type_args, .. } => type_args.clone(),
        Type::Reference(inner) | Type::MutableRef { inner, .. } => enum_type_args(inner),
        _ => Vec::new(),
    }
}

/// Does `stmt` contain (at any depth through nested If/Match
/// wrapping) an If or Match arm whose `BlockTail` is `Return`?
/// Triggers the inner-Return lift. Both `Stmt::Eval` and `Stmt::Let`
/// positions are detected:
///
/// - `Stmt::Eval` (or `Stmt::Let` with all-discard pattern): routed
///   to `perform_lift_eval`. The expression's value is dropped, so
///   the surrounding block's tail can become a Match/If producing
///   AbortResult directly, with Return-arms delivering their payload
///   and non-Return arms tail-Calling the continuation.
///
/// - `Stmt::Let { pat: [v..], value: SOURCE_EXPR }` with at least
///   one bound slot: routed to `perform_lift_let`. The let-bound
///   var(s) become parameters of the continuation `cont_N`; each
///   Return-arm of SOURCE_EXPR delivers AbortResult as the
///   surrounding block's tail, and each non-Return arm tail-Calls
///   `cont_N` with the arm value bound as the trailing arg.
fn stmt_contains_inner_return_match(s: &Stmt) -> bool {
    match s {
        Stmt::Eval(e) => expr_contains_match_with_return_arm(e),
        Stmt::Let { value, .. } => expr_contains_match_with_return_arm(value),
    }
}

/// Does `e` contain (at any depth, through nested If/Match wrapping)
/// an If or Match arm whose `BlockTail` is a `Return`? This is the
/// trigger for the inner-Return lift.
///
/// The check fires on:
///   - `Match { arms: ... arm.tail = Return(_) }`            (direct)
///   - `If { then.tail = Return(_) }` or `else.tail = Return(_)` (direct)
///   - `If` wrapping any of the above in either arm's block   (recursive)
fn expr_contains_match_with_return_arm(e: &Expr) -> bool {
    match e {
        Expr::Match { cases, .. } => {
            cases
                .iter()
                .any(|arm| matches!(&arm.body.tail, BlockTail::Return(_)))
                || cases
                    .iter()
                    .any(|arm| block_contains_match_with_return_arm(&arm.body))
        }
        Expr::If {
            then_branch,
            else_branch,
            ..
        } => {
            matches!(&then_branch.tail, BlockTail::Return(_))
                || matches!(&else_branch.tail, BlockTail::Return(_))
                || block_tail_is_match_with_return_arm(then_branch)
                || block_tail_is_match_with_return_arm(else_branch)
                || block_contains_match_with_return_arm(then_branch)
                || block_contains_match_with_return_arm(else_branch)
        }
        _ => false,
    }
}

fn block_tail_is_match_with_return_arm(b: &Block) -> bool {
    match &b.tail {
        BlockTail::Value(Expr::Match { cases, .. }) => cases
            .iter()
            .any(|arm| matches!(&arm.body.tail, BlockTail::Return(_))),
        _ => false,
    }
}

fn block_contains_match_with_return_arm(b: &Block) -> bool {
    for s in &b.stmts {
        if stmt_contains_inner_return_match(s) {
            return true;
        }
    }
    matches!(&b.tail, BlockTail::Value(expr) if expr_contains_match_with_return_arm(expr))
}

/// Perform the lift: split `b` at index `i` and rewrite. The exact
/// transform depends on the trigger stmt kind:
///
/// - `Stmt::Eval(<expr>)`: split the following code into one continuation
///   helper. Return arms deliver their payload; fallthrough arms call the
///   helper.
///
/// - `Stmt::Let { pat, value: <expr> }`: split the following code into one
///   continuation helper that takes the bound values as parameters. Return
///   arms deliver their payload; value arms call the helper with the values.
///
/// The mutable statement-position strategy is selected above this function
/// and instead uses one in-place early-return carrier.
fn perform_lift(
    b: &mut Block,
    i: usize,
    scope: &BTreeMap<VarId, Type>,
    ctx: &mut LiftCtx,
    strategy: LiftStrategy,
) {
    if matches!(strategy, LiftStrategy::EarlyReturnCarrier) {
        perform_lift_carrier(b, i, scope, ctx);
        return;
    }
    if matches!(strategy, LiftStrategy::ValueReturnCarrier) {
        perform_lift_value_carrier(b, i, scope, ctx);
        return;
    }

    // `Stmt::Let` with an all-discard pattern (e.g. `let _ := ...`)
    // is semantically equivalent to `Stmt::Eval` — there's no
    // binding to preserve downstream. Route it through the simpler Eval path;
    // the real-Let path exists only to forward bound values into its
    // continuation helper.
    let trigger_is_real_let = match &b.stmts[i] {
        Stmt::Let { pattern, .. } => pattern.iter().any(Option::is_some),
        _ => false,
    };
    if trigger_is_real_let {
        perform_lift_let(b, i, scope, ctx);
    } else {
        // Stmt::Eval OR Stmt::Let with all-discard pattern.
        // Normalise the latter to Stmt::Eval before dispatching so
        // perform_lift_eval can pattern-match on Stmt::Eval directly.
        if let Stmt::Let { value, .. } = &b.stmts[i] {
            let value = value.clone();
            b.stmts[i] = Stmt::Eval(value);
        }
        perform_lift_eval(b, i, scope, ctx);
    }
}

/// Rank a capture among the parent's ghost parameters, if it is one.
///
/// A capture is the SSA-renamed form of a parent ghost binder
/// (`__ghost_<tag>` -> `__ghost_<tag>_3`), so the match strips at most
/// one trailing `_<digits>` and then compares for EQUALITY. Prefix
/// matching would be ambiguous for exactly the marker pairs this fix
/// exists for (`SpecTransferAddress` is a prefix of
/// `SpecTransferAddressExists`).
/// The ghost parameters of `fid`, in the order stage 4 appended them.
pub(super) fn ghost_params_of(program: &Program, fid: FunId) -> Vec<VarId> {
    program
        .functions
        .get(&fid)
        .map(|f| {
            f.signature
                .params
                .iter()
                .filter(|p| p.var.starts_with("__ghost"))
                .map(|p| p.var.clone())
                .collect()
        })
        .unwrap_or_default()
}

pub(super) fn ghost_rank(v: &VarId, parent_ghost_params: &[VarId]) -> Option<usize> {
    if !v.starts_with("__ghost") {
        return None;
    }
    let base = match v.rsplit_once('_') {
        Some((head, tail)) if !tail.is_empty() && tail.chars().all(|c| c.is_ascii_digit()) => head,
        _ => v.as_ref(),
    };
    parent_ghost_params
        .iter()
        .position(|g| g.as_ref() == v.as_ref() || g.as_ref() == base)
}

/// Capture order: name order for everything, EXCEPT that ghost
/// captures are placed in the parent's ghost-set order.
///
/// The ghost captures keep the POSITIONS name order gave them and only
/// their contents are permuted, so a program whose ghost binders sort
/// the same way both ways -- every program before the binders carried
/// datatype names -- renders byte-identically.
pub(super) fn order_captures(
    capture_set: BTreeSet<VarId>,
    parent_ghost_params: &[VarId],
) -> Vec<VarId> {
    let mut captures: Vec<VarId> = capture_set.into_iter().collect();
    let mut slots: Vec<usize> = Vec::new();
    let mut ghosts: Vec<(usize, VarId)> = Vec::new();
    for (i, v) in captures.iter().enumerate() {
        if let Some(rank) = ghost_rank(v, parent_ghost_params) {
            slots.push(i);
            ghosts.push((rank, v.clone()));
        }
    }
    ghosts.sort_by(|a, b| a.0.cmp(&b.0).then_with(|| a.1.cmp(&b.1)));
    for (slot, (_, v)) in slots.into_iter().zip(ghosts) {
        captures[slot] = v;
    }
    captures
}

/// The Stmt::Eval case — the simpler one. (Previously the entire
/// body of perform_lift.)
fn perform_lift_eval(b: &mut Block, i: usize, scope: &BTreeMap<VarId, Type>, ctx: &mut LiftCtx) {
    let trigger = std::mem::replace(&mut b.stmts[i], Stmt::Eval(Expr::Unit));
    let post_stmts: Vec<Stmt> = b.stmts.drain(i + 1..).collect();
    b.stmts.truncate(i);
    let orig_tail = std::mem::replace(&mut b.tail, BlockTail::Value(Expr::Unit));

    let cont_body = build_continuation_block(post_stmts, orig_tail, scope, ctx);
    let free = crate::ir::analysis::free_vars::free_vars(&cont_body);
    let scope_keys: BTreeSet<VarId> = scope.keys().cloned().collect();
    let capture_set: BTreeSet<_> = free.intersection(&scope_keys).cloned().collect();
    let captures = order_captures(capture_set, &ctx.parent_ghost_params);

    let cont_fid = alloc_cont_fid(ctx, &captures, scope, cont_body);

    let expr = match trigger {
        Stmt::Eval(e) => e,
        _ => unreachable!("perform_lift_eval called on non-Eval stmt"),
    };
    let lifted_expr = lift_expr(expr, cont_fid, &captures, ctx);
    b.tail = BlockTail::Value(lifted_expr);
}

fn perform_lift_carrier(b: &mut Block, i: usize, scope: &BTreeMap<VarId, Type>, ctx: &mut LiftCtx) {
    let supported = match &b.stmts[i] {
        Stmt::Eval(expr) | Stmt::Let { value: expr, .. } => carrier_conversion_supported(expr),
    };
    debug_assert!(supported, "carrier conversion must be preflighted");
    let trigger = std::mem::replace(&mut b.stmts[i], Stmt::Eval(Expr::Unit));
    let post_stmts: Vec<Stmt> = b.stmts.drain(i + 1..).collect();
    b.stmts.truncate(i);
    let orig_tail = std::mem::replace(&mut b.tail, BlockTail::Value(Expr::Unit));
    let continuation = build_continuation_block(post_stmts, orig_tail, scope, ctx);
    let expr = match trigger {
        Stmt::Eval(expr) | Stmt::Let { value: expr, .. } => expr,
    };
    let carrier = lift_expr_to_carrier(expr, ctx);
    b.tail = BlockTail::Value(consume_carrier(carrier, continuation, ctx));
}

/// Lift a value-producing statement without capturing outstanding mutable
/// borrows. `ReturnFlow<T, R>` carries either the statement's ordinary value
/// `T` or the enclosing function's early-return value `R`; a local match runs
/// the original continuation only in the ordinary case.
fn perform_lift_value_carrier(
    b: &mut Block,
    i: usize,
    scope: &BTreeMap<VarId, Type>,
    ctx: &mut LiftCtx,
) {
    let trigger = std::mem::replace(&mut b.stmts[i], Stmt::Eval(Expr::Unit));
    let (pattern, value) = match trigger {
        Stmt::Let { pattern, value } => (pattern, value),
        Stmt::Eval(value) => (Vec::new(), value),
    };
    let value_ty = if pattern.is_empty() {
        Type::Unit
    } else {
        infer_let_value_type(
            &pattern,
            &value,
            scope,
            &ctx.target_types,
            &ctx.deref_vars,
            ctx.program,
        )
    };
    let post_stmts: Vec<Stmt> = b.stmts.drain(i + 1..).collect();
    b.stmts.truncate(i);
    let orig_tail = std::mem::replace(&mut b.tail, BlockTail::Value(Expr::Unit));
    let flow = lift_expr_to_value_flow(value, &value_ty, scope, ctx);
    let normal = ctx.fresh_return_lift_var();
    let returned = ctx.fresh_return_lift_var();
    let mut continuation_stmts = Vec::new();
    if !pattern.is_empty() {
        continuation_stmts.push(Stmt::Let {
            pattern: pattern.clone(),
            value: Expr::Var(normal.clone()),
        });
    }
    continuation_stmts.extend(post_stmts);
    let continuation = Block {
        stmts: continuation_stmts,
        tail: orig_tail,
    };
    b.tail = BlockTail::Value(Expr::Match {
        struct_id: ctx.return_flow_id,
        selector: Box::new(flow),
        cases: vec![
            MatchArm {
                variant: RETURN_FLOW_CONTINUE_TAG,
                bindings: vec![normal],
                body: Box::new(continuation),
            },
            MatchArm {
                variant: RETURN_FLOW_RETURNED_TAG,
                bindings: vec![returned.clone()],
                body: Box::new(Block::just(Expr::Var(returned))),
            },
        ],
    });
}

fn lift_expr_to_value_flow(
    expr: Expr,
    normal_ty: &Type,
    scope: &BTreeMap<VarId, Type>,
    ctx: &mut LiftCtx,
) -> Expr {
    match expr {
        Expr::If {
            cond,
            then_branch,
            else_branch,
        } => Expr::If {
            cond,
            then_branch: Box::new(lift_block_to_value_flow(
                *then_branch,
                normal_ty,
                scope,
                ctx,
            )),
            else_branch: Box::new(lift_block_to_value_flow(
                *else_branch,
                normal_ty,
                scope,
                ctx,
            )),
        },
        Expr::Match {
            struct_id,
            selector,
            cases,
        } => {
            let binding_types: Vec<Vec<Type>> = cases
                .iter()
                .map(|arm| variant_binding_types(ctx, struct_id, &selector, arm.variant, scope))
                .collect();
            Expr::Match {
                struct_id,
                selector,
                cases: cases
                    .into_iter()
                    .zip(binding_types)
                    .map(|(arm, tys)| {
                        let mut arm_scope = scope.clone();
                        for (binding, ty) in arm.bindings.iter().zip(tys) {
                            arm_scope.insert(binding.clone(), ty);
                        }
                        MatchArm {
                            variant: arm.variant,
                            bindings: arm.bindings,
                            body: Box::new(lift_block_to_value_flow(
                                *arm.body, normal_ty, &arm_scope, ctx,
                            )),
                        }
                    })
                    .collect(),
            }
        }
        other => make_value_flow_continue(other, normal_ty, scope, ctx),
    }
}

fn lift_block_to_value_flow(
    mut block: Block,
    normal_ty: &Type,
    scope: &BTreeMap<VarId, Type>,
    ctx: &mut LiftCtx,
) -> Block {
    let mut local_scope = scope.clone();
    let trigger = block.stmts.iter().enumerate().find_map(|(i, stmt)| {
        if stmt_contains_inner_return_match(stmt) {
            Some(i)
        } else {
            extend_scope_with_stmt(
                stmt,
                &mut local_scope,
                &ctx.target_types,
                &ctx.deref_vars,
                ctx.program,
            );
            None
        }
    });
    if let Some(i) = trigger {
        let mut suffix = block.stmts.split_off(i);
        let stmt = suffix.remove(0);
        let (pattern, value) = match stmt {
            Stmt::Let { pattern, value } => (pattern, value),
            Stmt::Eval(value) => (Vec::new(), value),
        };
        let value_ty = if pattern.is_empty() {
            Type::Unit
        } else {
            infer_let_value_type(
                &pattern,
                &value,
                &local_scope,
                &ctx.target_types,
                &ctx.deref_vars,
                ctx.program,
            )
        };
        let value_flow = lift_expr_to_value_flow(value, &value_ty, &local_scope, ctx);
        let normal = ctx.fresh_return_lift_var();
        let returned = ctx.fresh_return_lift_var();
        let mut continued_scope = local_scope.clone();
        // `normal` is a fresh binding introduced by the ReturnFlow match
        // below. We recursively transform its arm before that Match exists in
        // the outer IR, so ordinary match-arm scope discovery cannot supply
        // its type yet. Thread the already-known Continue payload type
        // explicitly for the synthetic `let pattern := normal`.
        continued_scope.insert(normal.clone(), value_ty.clone());
        bind_pattern(&pattern, &value_ty, &mut continued_scope);
        let mut continued_stmts = Vec::new();
        if !pattern.is_empty() {
            continued_stmts.push(Stmt::Let {
                pattern,
                value: Expr::Var(normal.clone()),
            });
        }
        continued_stmts.extend(suffix);
        let continued = lift_block_to_value_flow(
            Block {
                stmts: continued_stmts,
                tail: block.tail,
            },
            normal_ty,
            &continued_scope,
            ctx,
        );
        block.tail = BlockTail::Value(Expr::Match {
            struct_id: ctx.return_flow_id,
            selector: Box::new(value_flow),
            cases: vec![
                MatchArm {
                    variant: RETURN_FLOW_CONTINUE_TAG,
                    bindings: vec![normal],
                    body: Box::new(continued),
                },
                MatchArm {
                    variant: RETURN_FLOW_RETURNED_TAG,
                    bindings: vec![returned.clone()],
                    body: Box::new(Block::just(make_value_flow_returned(
                        Expr::Var(returned),
                        normal_ty,
                        ctx,
                    ))),
                },
            ],
        });
        return block;
    }

    match block.tail {
        BlockTail::Return(value) => {
            make_value_flow_return_block(block.stmts, *value, normal_ty, ctx)
        }
        BlockTail::Value(expr) => {
            block.tail =
                BlockTail::Value(lift_expr_to_value_flow(expr, normal_ty, &local_scope, ctx));
            block
        }
        terminal => {
            block.tail = terminal;
            block
        }
    }
}

fn make_value_flow_return_block(
    mut stmts: Vec<Stmt>,
    value: Expr,
    normal_ty: &Type,
    ctx: &mut LiftCtx,
) -> Block {
    let Some(return_type) = world_returning_call_type(&value, ctx) else {
        return Block {
            stmts,
            tail: BlockTail::Value(make_value_flow_returned(value, normal_ty, ctx)),
        };
    };
    let arity = match &return_type {
        Type::Tuple(items) => items.len(),
        _ => 1,
    };
    let bindings: Vec<_> = (0..arity).map(|_| ctx.fresh_return_lift_var()).collect();
    stmts.push(Stmt::Let {
        pattern: bindings.iter().cloned().map(Some).collect(),
        value,
    });
    let payload = if matches!(return_type, Type::Tuple(_)) {
        Expr::Tuple(bindings.into_iter().map(Expr::Var).collect())
    } else {
        Expr::Var(bindings.into_iter().next().expect("scalar return binding"))
    };
    Block {
        stmts,
        tail: BlockTail::Value(make_value_flow_returned(payload, normal_ty, ctx)),
    }
}

fn make_value_flow_continue(
    value: Expr,
    normal_ty: &Type,
    scope: &BTreeMap<VarId, Type>,
    ctx: &LiftCtx,
) -> Expr {
    let value = coerce_carried_value(value, normal_ty, scope, ctx.program);
    Expr::Pack {
        struct_id: ctx.return_flow_id,
        type_args: vec![normal_ty.clone(), ctx.ret_type.clone()],
        variant: Some(RETURN_FLOW_CONTINUE_TAG),
        fields: vec![value],
    }
}

fn coerce_carried_value(
    value: Expr,
    expected: &Type,
    scope: &BTreeMap<VarId, Type>,
    program: &Program,
) -> Expr {
    match (value, expected) {
        (Expr::Tuple(values), Type::Tuple(expected_types))
            if values.len() == expected_types.len() =>
        {
            Expr::Tuple(
                values
                    .into_iter()
                    .zip(expected_types)
                    .map(|(value, expected)| coerce_carried_value(value, expected, scope, program))
                    .collect(),
            )
        }
        (value, expected) => match type_of(&value, scope, program) {
            Ok(Type::Reference(inner)) | Ok(Type::MutableRef { inner, .. })
                if inner.as_ref() == expected =>
            {
                Expr::ReadRef(Box::new(value))
            }
            _ => value,
        },
    }
}

fn make_value_flow_returned(value: Expr, normal_ty: &Type, ctx: &LiftCtx) -> Expr {
    Expr::Pack {
        struct_id: ctx.return_flow_id,
        type_args: vec![normal_ty.clone(), ctx.ret_type.clone()],
        variant: Some(RETURN_FLOW_RETURNED_TAG),
        fields: vec![value],
    }
}

fn lift_expr_to_carrier(expr: Expr, ctx: &mut LiftCtx) -> Expr {
    match expr {
        Expr::If {
            cond,
            then_branch,
            else_branch,
        } => Expr::If {
            cond,
            then_branch: Box::new(lift_block_to_carrier(*then_branch, ctx)),
            else_branch: Box::new(lift_block_to_carrier(*else_branch, ctx)),
        },
        Expr::Match {
            struct_id,
            selector,
            cases,
        } => Expr::Match {
            struct_id,
            selector,
            cases: cases
                .into_iter()
                .map(|arm| MatchArm {
                    variant: arm.variant,
                    bindings: arm.bindings,
                    body: Box::new(lift_block_to_carrier(*arm.body, ctx)),
                })
                .collect(),
        },
        other => other,
    }
}

fn lift_block_to_carrier(mut block: Block, ctx: &mut LiftCtx) -> Block {
    if let Some(i) = block
        .stmts
        .iter()
        .position(stmt_contains_inner_return_match)
    {
        if !stmt_routes_to_eval_lift(&block.stmts[i]) {
            return block;
        }
        let mut rest_stmts = block.stmts.split_off(i);
        let trigger = rest_stmts.remove(0);
        let rest = Block {
            stmts: rest_stmts,
            tail: block.tail,
        };
        let no_return = lift_block_to_carrier(rest, ctx);
        let expr = match trigger {
            Stmt::Eval(expr) | Stmt::Let { value: expr, .. } => expr,
        };
        let carrier = lift_expr_to_carrier(expr, ctx);
        block.tail = BlockTail::Value(propagate_carrier(carrier, no_return, ctx));
        return block;
    }

    match block.tail {
        BlockTail::Return(value) => make_carrier_return_block(block.stmts, *value, ctx),
        BlockTail::Value(expr) if expr_contains_match_with_return_arm(&expr) => {
            block.tail = BlockTail::Value(lift_expr_to_carrier(expr, ctx));
            block
        }
        BlockTail::Value(expr) => {
            block.stmts.push(Stmt::Eval(expr));
            block.tail = BlockTail::Value(make_carrier_none(ctx));
            block
        }
        terminal => {
            block.tail = terminal;
            block
        }
    }
}

fn make_carrier_return_block(mut stmts: Vec<Stmt>, value: Expr, ctx: &mut LiftCtx) -> Block {
    let Some(return_type) = world_returning_call_type(&value, ctx) else {
        return Block {
            stmts,
            tail: BlockTail::Value(make_carrier_some(value, ctx)),
        };
    };

    let arity = match &return_type {
        Type::Tuple(items) => items.len(),
        _ => 1,
    };
    let bindings: Vec<_> = (0..arity).map(|_| ctx.fresh_return_lift_var()).collect();
    stmts.push(Stmt::Let {
        pattern: bindings.iter().cloned().map(Some).collect(),
        value,
    });
    let payload = if matches!(return_type, Type::Tuple(_)) {
        Expr::Tuple(bindings.into_iter().map(Expr::Var).collect())
    } else {
        Expr::Var(
            bindings
                .into_iter()
                .next()
                .expect("a scalar call return has one binding"),
        )
    };
    Block {
        stmts,
        tail: BlockTail::Value(make_carrier_some(payload, ctx)),
    }
}

fn world_returning_call_type(value: &Expr, ctx: &LiftCtx<'_>) -> Option<Type> {
    let Expr::Call { fun, type_args, .. } = value else {
        return None;
    };
    let world_id = ctx.world_id?;
    let callee = ctx.program.lookup_callee(*fun)?;
    let return_type = substitute_type_params(&callee.signature().return_type, type_args);
    crate::stage_04_effects::common::type_carries_world(&return_type, world_id)
        .then_some(return_type)
}

fn propagate_carrier(carrier: Expr, no_return: Block, ctx: &mut LiftCtx) -> Expr {
    let payload = ctx.fresh_return_lift_var();
    Expr::Match {
        struct_id: ctx.option_id,
        selector: Box::new(carrier),
        cases: vec![
            MatchArm {
                variant: OPTION_NONE_TAG,
                bindings: Vec::new(),
                body: Box::new(no_return),
            },
            MatchArm {
                variant: OPTION_SOME_TAG,
                bindings: vec![payload.clone()],
                body: Box::new(Block::just(make_carrier_some(Expr::Var(payload), ctx))),
            },
        ],
    }
}

fn consume_carrier(carrier: Expr, continuation: Block, ctx: &mut LiftCtx) -> Expr {
    let payload = ctx.fresh_return_lift_var();
    Expr::Match {
        struct_id: ctx.option_id,
        selector: Box::new(carrier),
        cases: vec![
            MatchArm {
                variant: OPTION_NONE_TAG,
                bindings: Vec::new(),
                body: Box::new(continuation),
            },
            MatchArm {
                variant: OPTION_SOME_TAG,
                bindings: vec![payload.clone()],
                body: Box::new(Block::just(Expr::Var(payload))),
            },
        ],
    }
}

fn make_carrier_none(ctx: &LiftCtx) -> Expr {
    Expr::Pack {
        struct_id: ctx.option_id,
        type_args: vec![ctx.ret_type.clone()],
        variant: Some(OPTION_NONE_TAG),
        fields: Vec::new(),
    }
}

fn make_carrier_some(value: Expr, ctx: &LiftCtx) -> Expr {
    Expr::Pack {
        struct_id: ctx.option_id,
        type_args: vec![ctx.ret_type.clone()],
        variant: Some(OPTION_SOME_TAG),
        fields: vec![value],
    }
}

/// The Stmt::Let case — continuation-extraction transform.
///
/// Input shape:
///   Block {
///     stmts: [..pre.., Stmt::Let { pat: [v], value: SOURCE_EXPR }, ..rest..],
///     tail: original_tail
///   }
///
/// where SOURCE_EXPR contains an inner Match/If arm whose tail is
/// `Return(payload)`.
///
/// Output shape:
///   Block {
///     stmts: [..pre..],
///     tail: Value(<SOURCE_EXPR with arms rewritten as below>)
///   }
///
/// Arm rewriting (recursive over If/Match nesting):
///   - Return(payload)-tail arm  →  Value(payload). The payload is
///     an AbortResult value; the surrounding Match/If's value then
///     unifies at AbortResult.
///   - Non-Return-tail arm with tail = Value(arm_value)  →
///     Value(Call(cont_N, captures.. ++ [arm_value])). cont_N is a
///     new helper that takes the captured vars plus the let-pattern
///     var(s) and contains [..rest.., original_tail].
///   - Value(If/Match) tail  →  recurse into the nested If/Match's
///     arms via lift_let_expr.
///
/// The source expression is walked ONCE (no duplication into
/// abort_check + reconstruct_value), so this transform composes
/// cleanly under nested lifts.
fn perform_lift_let(b: &mut Block, i: usize, scope: &BTreeMap<VarId, Type>, ctx: &mut LiftCtx) {
    let trigger = std::mem::replace(&mut b.stmts[i], Stmt::Eval(Expr::Unit));
    let (pattern, source_expr) = match trigger {
        Stmt::Let { pattern, value } => (pattern, value),
        _ => unreachable!("perform_lift_let called on non-Let stmt"),
    };
    let post_stmts: Vec<Stmt> = b.stmts.drain(i + 1..).collect();
    b.stmts.truncate(i);
    let orig_tail = std::mem::replace(&mut b.tail, BlockTail::Value(Expr::Unit));

    // Infer the let-value's type from the source expression. The
    // let-pattern var(s) get this type as their declared type when
    // they become cont_N parameters.
    let value_type = infer_let_value_type(
        &pattern,
        &source_expr,
        scope,
        &ctx.target_types,
        &ctx.deref_vars,
        ctx.program,
    );

    // cont_N body: everything that ran after the let, with the
    // let-pattern var(s) still in scope (they become cont_N params).
    let cont_body = Block {
        stmts: post_stmts,
        tail: orig_tail,
    };

    // Capture vars used in cont_body that are bound in the outer
    // scope, EXCEPT the let-pattern vars themselves — those are
    // passed as the trailing argument(s) of the Call, not captured.
    let pattern_vars: BTreeSet<VarId> = pattern.iter().filter_map(|s| s.clone()).collect();
    let free = crate::ir::analysis::free_vars::free_vars(&cont_body);
    let scope_keys: BTreeSet<VarId> = scope.keys().cloned().collect();
    let capture_set: BTreeSet<_> = free
        .intersection(&scope_keys)
        .filter(|v| !pattern_vars.contains(*v))
        .cloned()
        .collect();
    let captures = order_captures(capture_set, &ctx.parent_ghost_params);

    let cont_fid = alloc_cont_fid_let(ctx, &captures, scope, &pattern, &value_type, cont_body);

    let lifted_expr = lift_let_expr(source_expr, cont_fid, &captures, &pattern, ctx);
    b.tail = BlockTail::Value(lifted_expr);
}

/// Lift a source expression for the Stmt::Let case: rewrite each
/// arm so that Return-arms deliver the AbortResult payload directly
/// (Value(payload)) and non-Return arms tail-Call `cont_fid` with
/// (captures.., arm_value..). Recurses into nested If/Match.
fn lift_let_expr(
    e: Expr,
    cont_fid: FunId,
    captures: &[VarId],
    pattern: &[Option<VarId>],
    ctx: &LiftCtx,
) -> Expr {
    match e {
        Expr::Match {
            struct_id,
            selector,
            cases,
        } => {
            let new_cases: Vec<MatchArm> = cases
                .into_iter()
                .map(|arm| lift_let_match_arm(arm, cont_fid, captures, pattern, ctx))
                .collect();
            Expr::Match {
                struct_id,
                selector,
                cases: new_cases,
            }
        }
        Expr::If {
            cond,
            then_branch,
            else_branch,
        } => {
            let new_then = lift_let_arm_block(*then_branch, cont_fid, captures, pattern, ctx);
            let new_else = lift_let_arm_block(*else_branch, cont_fid, captures, pattern, ctx);
            Expr::If {
                cond,
                then_branch: Box::new(new_then),
                else_branch: Box::new(new_else),
            }
        }
        other => {
            // Defensive fallback: source expression isn't an If/Match
            // (shouldn't happen because the trigger detector only
            // fires on If/Match-shapes). Wrap as a direct cont_N call.
            let mut args: Vec<Expr> = captures.iter().map(|v| Expr::Var(v.clone())).collect();
            args.push(other);
            Expr::Call {
                fun: cont_fid,
                type_args: ctx
                    .parent_type_params
                    .iter()
                    .enumerate()
                    .map(|(i, _)| Type::TypeParam(i as u16))
                    .collect(),
                args,
            }
        }
    }
}

fn lift_let_match_arm(
    arm: MatchArm,
    cont_fid: FunId,
    captures: &[VarId],
    pattern: &[Option<VarId>],
    ctx: &LiftCtx,
) -> MatchArm {
    let body = *arm.body;
    let new_body = lift_let_arm_block(body, cont_fid, captures, pattern, ctx);
    MatchArm {
        variant: arm.variant,
        bindings: arm.bindings,
        body: Box::new(new_body),
    }
}

/// Rewrite an If/Match arm block in the Let-lift context:
///   - tail = Return(payload)            → tail = Value(payload)
///   - tail = Value(If/Match)            → recurse via lift_let_expr
///   - tail = Value(arm_value) otherwise → tail = Value(Call(cont_N,
///       captures.. ++ arm_value))
fn lift_let_arm_block(
    b: Block,
    cont_fid: FunId,
    captures: &[VarId],
    pattern: &[Option<VarId>],
    ctx: &LiftCtx,
) -> Block {
    match b.tail {
        BlockTail::Return(v) => Block {
            stmts: b.stmts,
            tail: BlockTail::Value(*v),
        },
        BlockTail::Value(Expr::Match { .. }) | BlockTail::Value(Expr::If { .. }) => {
            let v = match b.tail {
                BlockTail::Value(e) => e,
                _ => unreachable!(),
            };
            let lifted = lift_let_expr(v, cont_fid, captures, pattern, ctx);
            Block {
                stmts: b.stmts,
                tail: BlockTail::Value(lifted),
            }
        }
        BlockTail::Value(e) if value_is_abort_result(&e, ctx) => Block {
            // A previous lift may already have converted an early Return into
            // an explicit Aborted value. It remains terminal: sending it to
            // this lift's continuation would swallow the abort as normal
            // fallthrough (typically ending in NoAbort).
            stmts: b.stmts,
            tail: BlockTail::Value(e),
        },
        BlockTail::Value(arm_value) => {
            let mut args: Vec<Expr> = captures.iter().map(|v| Expr::Var(v.clone())).collect();
            let mut stmts = b.stmts;
            // Splat: a multi-slot Let pattern means cont_N has the
            // pattern vars as SEPARATE parameters. The arm value
            // must therefore be flattened into individual args, not
            // passed as a single Tuple expression. The IR's
            // always-Tuple invariant (validate.rs) guarantees that
            // when pattern.len() > 1 the arm value is an Expr::Tuple
            // of matching arity; the singleton-tuple case is a
            // transparent wrapper we unwrap here too.
            if pattern.len() > 1 {
                if let Expr::Tuple(elems) = arm_value {
                    for e in elems {
                        args.push(e);
                    }
                } else if matches!(
                    type_of(&arm_value, &BTreeMap::new(), ctx.program),
                    Ok(Type::Tuple(ref es)) if es.len() == pattern.len()
                ) {
                    // Multi-slot pattern, arm value a non-literal-`Tuple`
                    // expression whose TYPE is a tuple of matching arity
                    // (e.g. a loop helper `while_0` returning
                    // `(BoundedNat (2^64) x Bool)`). Bind it to the pattern
                    // with a destructuring Let and forward the pattern's
                    // vars as the trailing args -- matching cont_N's
                    // trailing params (`alloc_cont_fid_let` appends one per
                    // `Some` slot, in order).
                    for slot in pattern {
                        if let Some(v) = slot {
                            args.push(Expr::Var(v.clone()));
                        }
                    }
                    stmts.push(Stmt::Let {
                        pattern: pattern.to_vec(),
                        value: arm_value,
                    });
                } else {
                    // Multi-slot pattern but the arm value is a SCALAR of a
                    // different type: this arm is an early exit / loop
                    // recursion (e.g. a tail `Call` to the loop's own
                    // `while_N` returning the function's scalar result), NOT
                    // the pattern's carried-state tuple. The post-merge
                    // continuation must not run on this path -- deliver the
                    // value directly as this arm's tail. Destructuring an
                    // N-slot pattern from a scalar emits ill-typed Lean: the
                    // renderer fills the slots with `() : Unit` placeholders
                    // that then clash with cont_N's real parameter types.
                    return Block {
                        stmts,
                        tail: BlockTail::Value(arm_value),
                    };
                }
            } else {
                // Single-slot pattern -- unwrap a singleton Tuple if
                // present (always-Tuple invariant); otherwise push
                // the arm value as-is.
                match arm_value {
                    Expr::Tuple(mut elems) if elems.len() == 1 => {
                        args.push(elems.remove(0));
                    }
                    other => args.push(other),
                }
            }
            let call = Expr::Call {
                fun: cont_fid,
                type_args: ctx
                    .parent_type_params
                    .iter()
                    .enumerate()
                    .map(|(i, _)| Type::TypeParam(i as u16))
                    .collect(),
                args,
            };
            Block {
                stmts,
                tail: BlockTail::Value(call),
            }
        }
        // Abort / Break / Continue: shouldn't appear after phase 1's
        // per-tail rewrites. Conservatively leave alone.
        _ => b,
    }
}

/// Allocate cont_N for the Let-lift case. The signature is:
///   (captures.., let_pattern_vars..) -> parent_return_type
fn alloc_cont_fid_let(
    ctx: &mut LiftCtx,
    captures: &[VarId],
    scope: &BTreeMap<VarId, Type>,
    pattern: &[Option<VarId>],
    value_type: &Type,
    cont_body: Block,
) -> FunId {
    let cont_fid = ctx.alloc_fid();
    let slot = ctx.next_cont_slot;
    ctx.next_cont_slot += 1;
    let cont_name = crate::ir::names::cont_name(&ctx.parent_name, slot);
    let mut cont_params: Vec<Param> = captures
        .iter()
        .map(|v| Param {
            name: v.to_string(),
            var: v.clone(),
            ty: scope.get(v).cloned().expect(
                "continuation capture var is in scope (captures = free vars intersect scope keys)",
            ),
        })
        .collect();
    // Pattern vars become trailing parameters with their slot type.
    for (idx, slot_var) in pattern.iter().enumerate() {
        if let Some(v) = slot_var {
            let ty = if pattern.len() == 1 {
                match value_type {
                    Type::Tuple(es) if es.len() == 1 => es[0].clone(),
                    other => other.clone(),
                }
            } else {
                match value_type {
                    Type::Tuple(es) if es.len() == pattern.len() => es[idx].clone(),
                    _ => Type::Unit,
                }
            };
            cont_params.push(Param {
                name: v.to_string(),
                var: v.clone(),
                ty,
            });
        }
    }
    let cont_fn = Function {
        module: ctx.parent_module,
        name: cont_name,
        signature: Signature {
            type_params: ctx.parent_type_params.clone(),
            params: cont_params,
            return_type: ctx.ret_type.clone(),
        },
        body: cont_body,
        kind: FunctionKind::Synthetic,
        // Provisional; stage 8 closes world_writes over synthetic helpers.
        effects: Effects::PURE,
        explicit_pure: false,
    };
    ctx.program.functions.insert(cont_fid, cont_fn);
    cont_fid
}

fn alloc_cont_fid(
    ctx: &mut LiftCtx,
    captures: &[VarId],
    scope: &BTreeMap<VarId, Type>,
    cont_body: Block,
) -> FunId {
    let cont_fid = ctx.alloc_fid();
    let slot = ctx.next_cont_slot;
    ctx.next_cont_slot += 1;
    let cont_name = crate::ir::names::cont_name(&ctx.parent_name, slot);
    let cont_params: Vec<Param> = captures
        .iter()
        .map(|v| Param {
            name: v.to_string(),
            var: v.clone(),
            ty: scope.get(v).cloned().expect(
                "continuation capture var is in scope (captures = free vars intersect scope keys)",
            ),
        })
        .collect();
    let cont_fn = Function {
        module: ctx.parent_module,
        name: cont_name,
        signature: Signature {
            type_params: ctx.parent_type_params.clone(),
            params: cont_params,
            return_type: ctx.ret_type.clone(),
        },
        body: cont_body,
        kind: FunctionKind::Synthetic,
        // Provisional; stage 8 closes world_writes over synthetic helpers.
        effects: Effects::PURE,
        explicit_pure: false,
    };
    ctx.program.functions.insert(cont_fid, cont_fn);
    cont_fid
}

/// Build the continuation block: post-stmts + a tail that delivers
/// AbortResult. Wraps the original tail's value as a discardable
/// Stmt::Eval if needed.
fn build_continuation_block(
    post_stmts: Vec<Stmt>,
    orig_tail: BlockTail,
    scope: &BTreeMap<VarId, Type>,
    ctx: &LiftCtx,
) -> Block {
    let mut continuation = Block {
        stmts: post_stmts,
        tail: orig_tail,
    };
    match &continuation.tail {
        BlockTail::Value(e) => {
            // If `e` is already AbortResult-typed (e.g. a splice's
            // Match selecting on Option<MoveAbortCode>, or a Call
            // returning Option<MoveAbortCode>, or a Pack of the
            // AbortResult struct), KEEP it as the tail -- it
            // already encodes abort propagation. Otherwise (it's a
            // source-T value), discard via Stmt::Eval and deliver
            // NoAbort.
            let inferred_abort_result = block_value_type_lenient(
                &continuation,
                scope,
                &ctx.target_types,
                &ctx.deref_vars,
                ctx.program,
            )
            .is_some_and(|ty| is_abort_result_type(&ty, ctx.option_id, ctx.abort_code_id));
            if inferred_abort_result
                || value_is_abort_result(e, ctx)
                || !is_abort_result_type(&ctx.ret_type, ctx.option_id, ctx.abort_code_id)
            {
                // AbortResult value -> keep (already encodes abort propagation).
                // Non-.aborts function -> the tail value IS the function's
                // return value, keep it. Only an .aborts companion (whose
                // return is AbortResult) discards it and delivers NoAbort.
                continuation
            } else {
                let BlockTail::Value(value) =
                    std::mem::replace(&mut continuation.tail, BlockTail::Value(make_no_abort(ctx)))
                else {
                    unreachable!("continuation tail was just matched as Value")
                };
                continuation.stmts.push(Stmt::Eval(value));
                continuation
            }
        }
        BlockTail::Return(_)
        | BlockTail::Abort { .. }
        | BlockTail::Break { .. }
        | BlockTail::Continue { .. } => continuation,
        BlockTail::ReturnFromBlock { .. } => unreachable!(
            "BlockTail::ReturnFromBlock should be eliminated by stage 7 helper extraction"
        ),
    }
}

/// Detect whether `e` already produces a value of type
/// `Option<MoveAbortCode>` (the AbortResult type). Conservative:
/// callers must first try scope-aware type inference because a false
/// negative here would discard a real abort continuation. False positives
/// would leave a source-T expr in an AbortResult-expecting position and fail
/// type checking.
fn value_is_abort_result(e: &Expr, ctx: &LiftCtx) -> bool {
    match e {
        // Pack of the AbortResult struct.
        Expr::Pack {
            struct_id,
            type_args,
            ..
        } if *struct_id == ctx.option_id
            && matches!(type_args.as_slice(), [Type::Struct { struct_id, type_args }] if *struct_id == ctx.abort_code_id && type_args.is_empty()) =>
        {
            true
        }
        Expr::Match { cases, .. } => cases
            .iter()
            .all(|arm| block_tail_value_is_abort_result(&arm.body, ctx)),
        // Call to a function whose return type is Option<MoveAbortCode>.
        Expr::Call { fun, .. } => ctx
            .program
            .functions
            .get(fun)
            .map(|f| {
                is_abort_result_type(&f.signature.return_type, ctx.option_id, ctx.abort_code_id)
            })
            .unwrap_or(false),
        // If with both arms producing AbortResult.
        Expr::If {
            then_branch,
            else_branch,
            ..
        } => {
            block_tail_value_is_abort_result(then_branch, ctx)
                && block_tail_value_is_abort_result(else_branch, ctx)
        }
        _ => false,
    }
}

fn block_tail_value_is_abort_result(b: &Block, ctx: &LiftCtx) -> bool {
    match &b.tail {
        BlockTail::Value(e) => value_is_abort_result(e, ctx),
        BlockTail::Return(_) => true, // Returns carry AbortResult after phase 1.
        _ => false,
    }
}

/// Lift an expression's inner Match-with-Return-arm: rewrite the
/// Match's arms so that Return becomes Value(payload) (direct
/// delivery) and non-Return arms tail-Call the continuation helper.
/// Recurses into If/Match wrapping such Matches.
fn lift_expr(e: Expr, cont_fid: FunId, captures: &[VarId], ctx: &LiftCtx) -> Expr {
    match e {
        Expr::Match {
            struct_id,
            selector,
            cases,
        } => {
            let new_cases: Vec<MatchArm> = cases
                .into_iter()
                .map(|arm| lift_match_arm(arm, cont_fid, captures, ctx))
                .collect();
            Expr::Match {
                struct_id,
                selector,
                cases: new_cases,
            }
        }
        Expr::If {
            cond,
            then_branch,
            else_branch,
        } => {
            let new_then = lift_arm_block(*then_branch, cont_fid, captures, ctx);
            let new_else = lift_arm_block(*else_branch, cont_fid, captures, ctx);
            Expr::If {
                cond,
                then_branch: Box::new(new_then),
                else_branch: Box::new(new_else),
            }
        }
        other => other,
    }
}

fn lift_match_arm(arm: MatchArm, cont_fid: FunId, captures: &[VarId], ctx: &LiftCtx) -> MatchArm {
    let body = *arm.body;
    let new_body = lift_arm_block(body, cont_fid, captures, ctx);
    MatchArm {
        variant: arm.variant,
        bindings: arm.bindings,
        body: Box::new(new_body),
    }
}

/// Rewrite a Match/If arm block. If the arm's tail is Return(v),
/// becomes Value(v). Otherwise the arm has a non-Return tail that
/// should continue execution; wrap it to tail-Call the helper.
fn lift_arm_block(b: Block, cont_fid: FunId, captures: &[VarId], ctx: &LiftCtx) -> Block {
    match b.tail {
        BlockTail::Return(v) => Block {
            stmts: b.stmts,
            tail: BlockTail::Value(*v),
        },
        BlockTail::Value(Expr::Match { .. }) | BlockTail::Value(Expr::If { .. }) => {
            // Nested Match/If; recursively lift.
            let v = match b.tail {
                BlockTail::Value(e) => e,
                _ => unreachable!(),
            };
            let lifted = lift_expr(v, cont_fid, captures, ctx);
            Block {
                stmts: b.stmts,
                tail: BlockTail::Value(lifted),
            }
        }
        BlockTail::Value(e) if value_is_abort_result(&e, ctx) => Block {
            // Preserve explicit AbortResult handoffs produced by an earlier
            // nested lift; these are exits, not source values for cont_N.
            stmts: b.stmts,
            tail: BlockTail::Value(e),
        },
        BlockTail::Value(e) if is_abort_result_loop_handoff(&e, ctx) => Block {
            // This arm already exits through an AbortResult-valued handoff,
            // such as a recursive `.aborts.while_N` call. It must not fall
            // through to the continuation with the pre-branch loop state.
            stmts: b.stmts,
            tail: BlockTail::Value(e),
        },
        _ => {
            // Non-Return, non-nested-Match/If arm. Wrap its tail:
            // evaluate the original value (Stmt::Eval), then tail-
            // Call the continuation helper to deliver AbortResult.
            let mut stmts = b.stmts;
            match b.tail {
                BlockTail::Value(e) => stmts.push(Stmt::Eval(e)),
                _ => {}
            }
            let cont_call = Expr::Call {
                fun: cont_fid,
                type_args: ctx
                    .parent_type_params
                    .iter()
                    .enumerate()
                    .map(|(i, _)| Type::TypeParam(i as u16))
                    .collect(),
                args: captures.iter().map(|v| Expr::Var(v.clone())).collect(),
            };
            Block {
                stmts,
                tail: BlockTail::Value(cont_call),
            }
        }
    }
}

fn is_abort_result_loop_handoff(e: &Expr, ctx: &LiftCtx) -> bool {
    let Expr::Call { fun, .. } = e else {
        return false;
    };
    matches!(
        ctx.program.functions.get(fun).map(|f| &f.kind),
        Some(FunctionKind::LoopBody { .. })
    ) && value_is_abort_result(e, ctx)
}

fn make_no_abort(ctx: &LiftCtx) -> Expr {
    Expr::Pack {
        struct_id: ctx.option_id,
        type_args: vec![Type::Struct {
            struct_id: ctx.abort_code_id,
            type_args: Vec::new(),
        }],
        variant: Some(OPTION_NONE_TAG),
        fields: Vec::new(),
    }
}

#[cfg(test)]
mod tests {

    /// The ordering fix must be a NO-OP for every program whose ghost
    /// binders are `__ghost_<struct_id>`: there, name order and the
    /// ghost-set order coincide, which is exactly why the two orderings
    /// agreed before the binders carried datatype names. This is the
    /// property that makes the change safe for every other corpus.
    #[test]
    fn order_captures_is_identity_for_numeric_ghost_binders() {
        let parent: Vec<VarId> = vec!["__ghost_149".into(), "__ghost_150".into()];
        let set: BTreeSet<VarId> = ["__ghost_149_0", "__ghost_150_0", "t_t0_1", "world_0"]
            .into_iter()
            .map(VarId::from)
            .collect();
        let before: Vec<VarId> = set.iter().cloned().collect();
        assert_eq!(order_captures(set, &parent), before);
    }

    /// And it must actually reorder when one marker's name is a prefix
    /// of another's: `__ghost_<X>Exists_0` sorts BEFORE `__ghost_<X>_0`
    /// ('E' 0x45 < '_' 0x5F), which is the defect this fixes. The ghost
    /// captures keep the positions name order gave them.
    #[test]
    fn order_captures_reorders_prefix_colliding_ghost_binders() {
        let parent: Vec<VarId> = vec![
            "__ghost_P__m__SpecTransferAddress".into(),
            "__ghost_P__m__SpecTransferAddressExists".into(),
        ];
        let set: BTreeSet<VarId> = [
            "__ghost_P__m__SpecTransferAddressExists_0",
            "__ghost_P__m__SpecTransferAddress_0",
            "t_t0_1",
        ]
        .into_iter()
        .map(VarId::from)
        .collect();
        // Name order alone would put `...Exists_0` first.
        assert_eq!(
            set.iter().next().map(|v| v.to_string()),
            Some("__ghost_P__m__SpecTransferAddressExists_0".to_string())
        );
        let ordered = order_captures(set, &parent);
        assert_eq!(
            ordered.iter().map(|v| v.to_string()).collect::<Vec<_>>(),
            vec![
                "__ghost_P__m__SpecTransferAddress_0".to_string(),
                "__ghost_P__m__SpecTransferAddressExists_0".to_string(),
                "t_t0_1".to_string(),
            ]
        );
    }
    use super::*;
    use crate::ir::builder::{binop, lit_u64, var};
    use crate::ir::ops::BinOp;

    fn nested_ref() -> Type {
        // `&mut Struct1 [root=Struct2]` -- a borrow into a distinct parent.
        Type::MutableRef {
            inner: Box::new(Type::Struct {
                struct_id: 1,
                type_args: vec![],
            }),
            root: Box::new(Type::Struct {
                struct_id: 2,
                type_args: vec![],
            }),
        }
    }

    fn toplevel_ref() -> Type {
        // `&mut Struct1 [root=Struct1]` -- a decoupled top-level handle
        // (e.g. a cross-function `&mut` return); `root == inner`.
        Type::MutableRef {
            inner: Box::new(Type::Struct {
                struct_id: 1,
                type_args: vec![],
            }),
            root: Box::new(Type::Struct {
                struct_id: 1,
                type_args: vec![],
            }),
        }
    }

    /// Block whose continuation (`stmts[1..]` + tail) references `v`.
    fn block_with_cont_use(v: &str) -> Block {
        Block {
            stmts: vec![
                Stmt::Eval(Expr::Unit), // index 0 -- the "trigger" slot
                Stmt::Eval(Expr::Var(VarId::from(v))),
            ],
            tail: BlockTail::Value(Expr::Unit),
        }
    }

    #[test]
    fn severs_when_cont_captures_nested_borrow() {
        let b = block_with_cont_use("m");
        let mut scope = BTreeMap::new();
        scope.insert(VarId::from("m"), nested_ref());
        assert!(
            lift_severs_nested_borrow(&b, 0, &scope),
            "a continuation capturing a nested `&mut` borrow must be flagged"
        );
    }

    #[test]
    fn safe_when_cont_captures_only_toplevel_ref() {
        let b = block_with_cont_use("m");
        let mut scope = BTreeMap::new();
        scope.insert(VarId::from("m"), toplevel_ref());
        assert!(
            !lift_severs_nested_borrow(&b, 0, &scope),
            "a top-level (`root == inner`) `&mut` handle is safe to capture"
        );
    }

    #[test]
    fn safe_when_nested_borrow_bound_inside_cont() {
        // `m` is bound by a `Let` INSIDE the continuation, so it is not free
        // there -- not a capture -- even though `scope` types it as nested.
        // Mirrors volo's first early-return guard, whose borrow is created
        // only in the continuation it owns.
        let b = Block {
            stmts: vec![
                Stmt::Eval(Expr::Unit), // index 0 -- the "trigger" slot
                Stmt::Let {
                    pattern: vec![Some(VarId::from("m"))],
                    value: Expr::Unit,
                },
                Stmt::Eval(Expr::Var(VarId::from("m"))),
            ],
            tail: BlockTail::Value(Expr::Unit),
        };
        let mut scope = BTreeMap::new();
        scope.insert(VarId::from("m"), nested_ref());
        assert!(
            !lift_severs_nested_borrow(&b, 0, &scope),
            "a borrow bound inside the continuation is not a capture"
        );
    }

    #[test]
    fn eval_lift_preserves_abort_result_loop_handoff() {
        const OPTION_ID: StructId = 10;
        const ABORT_CODE_ID: StructId = 11;
        const LOOP_FID: FunId = 7;
        const CONT_FID: FunId = 8;

        let abort_result = Type::Struct {
            struct_id: OPTION_ID,
            type_args: vec![Type::Struct {
                struct_id: ABORT_CODE_ID,
                type_args: vec![],
            }],
        };
        let mut program = Program::default();
        program.functions.insert(
            LOOP_FID,
            Function {
                module: 0,
                name: "binary_search.aborts.while_0".into(),
                signature: Signature {
                    type_params: vec![],
                    params: vec![
                        Param {
                            name: "end".into(),
                            var: VarId::from("end"),
                            ty: Type::UInt(64),
                        },
                        Param {
                            name: "start".into(),
                            var: VarId::from("start"),
                            ty: Type::UInt(64),
                        },
                    ],
                    return_type: abort_result.clone(),
                },
                body: Block {
                    stmts: vec![],
                    tail: BlockTail::Value(make_no_abort_for_test(OPTION_ID, ABORT_CODE_ID)),
                },
                kind: FunctionKind::LoopBody { parent: 0, slot: 0 },
                effects: Effects::PURE,
                explicit_pure: false,
            },
        );

        let loop_call = Expr::Call {
            fun: LOOP_FID,
            type_args: vec![],
            args: vec![var("end"), var("next_start")],
        };
        let arm = Block {
            stmts: vec![Stmt::Let {
                pattern: vec![Some(VarId::from("next_start"))],
                value: binop(BinOp::Add, var("mid"), lit_u64(1)),
            }],
            tail: BlockTail::Value(loop_call.clone()),
        };
        let ctx = LiftCtx {
            program: &mut program,
            parent_ghost_params: Vec::new(),
            parent_name: "binary_search.aborts.while_0".into(),
            parent_module: 0,
            parent_type_params: vec![],
            ret_type: abort_result,
            option_id: OPTION_ID,
            abort_code_id: ABORT_CODE_ID,
            return_flow_id: 0,
            world_id: None,
            next_fid: CONT_FID + 1,
            next_cont_slot: 0,
            target_types: BTreeMap::new(),
            deref_vars: BTreeSet::new(),
        };

        let lifted = lift_arm_block(arm, CONT_FID, &[VarId::from("old_start")], &ctx);

        assert_eq!(lifted.stmts.len(), 1, "the loop call must not be discarded");
        assert_eq!(lifted.tail, BlockTail::Value(loop_call));
    }

    fn make_no_abort_for_test(option_id: StructId, abort_code_id: StructId) -> Expr {
        Expr::Pack {
            struct_id: option_id,
            type_args: vec![Type::Struct {
                struct_id: abort_code_id,
                type_args: vec![],
            }],
            variant: Some(OPTION_NONE_TAG),
            fields: vec![],
        }
    }

    #[test]
    fn match_binding_types_use_non_dense_variant_tag() {
        let mut program = Program::default();
        program.structs.insert(
            7,
            crate::ir::Struct {
                module_id: 0,
                name: "Carrier".into(),
                qualified_name: "p::m::Carrier".into(),
                type_params: vec!["T".into()],
                fields: Vec::new(),
                variants: Some(vec![crate::ir::Variant {
                    name: "Value".into(),
                    tag: 9,
                    fields: vec![crate::ir::Field {
                        name: "value".into(),
                        field_type: Type::TypeParam(0),
                    }],
                }]),
                is_native: false,
            },
        );
        let selector = Expr::Var("carrier".into());
        let mut scope = BTreeMap::new();
        scope.insert(
            "carrier".into(),
            Type::Struct {
                struct_id: 7,
                type_args: vec![Type::UInt(64)],
            },
        );
        let ctx = LiftCtx {
            program: &mut program,
            parent_ghost_params: Vec::new(),
            parent_name: "source".into(),
            parent_module: 0,
            parent_type_params: Vec::new(),
            ret_type: Type::Unit,
            option_id: 8,
            abort_code_id: 9,
            return_flow_id: 0,
            world_id: None,
            next_fid: 10,
            next_cont_slot: 0,
            target_types: BTreeMap::new(),
            deref_vars: BTreeSet::new(),
        };

        assert_eq!(
            variant_binding_types(&ctx, 7, &selector, 9, &scope),
            vec![Type::UInt(64)]
        );
    }

    #[test]
    fn abort_result_var_tail_is_not_discarded() {
        let option_id = 7;
        let abort_code_id = 8;
        let abort_type = Type::Struct {
            struct_id: option_id,
            type_args: vec![Type::Struct {
                struct_id: abort_code_id,
                type_args: Vec::new(),
            }],
        };
        let verdict = VarId::from("verdict");
        let post_stmts = vec![Stmt::Let {
            pattern: vec![Some(verdict.clone())],
            value: Expr::Pack {
                struct_id: option_id,
                type_args: vec![Type::Struct {
                    struct_id: abort_code_id,
                    type_args: Vec::new(),
                }],
                variant: Some(OPTION_NONE_TAG),
                fields: Vec::new(),
            },
        }];
        let mut program = Program::default();
        let ctx = LiftCtx {
            program: &mut program,
            parent_ghost_params: Vec::new(),
            parent_name: "source.aborts".into(),
            parent_module: 0,
            parent_type_params: Vec::new(),
            ret_type: abort_type,
            option_id,
            abort_code_id,
            return_flow_id: 0,
            world_id: None,
            next_fid: 0,
            next_cont_slot: 0,
            target_types: BTreeMap::new(),
            deref_vars: BTreeSet::new(),
        };

        let continuation = build_continuation_block(
            post_stmts,
            BlockTail::Value(Expr::Var(verdict.clone())),
            &BTreeMap::new(),
            &ctx,
        );

        assert_eq!(continuation.stmts.len(), 1);
        assert!(matches!(
            continuation.tail,
            BlockTail::Value(Expr::Var(var)) if var == verdict
        ));
    }

    fn nested_return_if() -> Expr {
        Expr::If {
            cond: Box::new(Expr::Const(crate::ir::Const::Bool(true))),
            then_branch: Box::new(Block {
                stmts: Vec::new(),
                tail: BlockTail::Return(Box::new(Expr::Unit)),
            }),
            else_branch: Box::new(Block::just(Expr::Unit)),
        }
    }

    #[test]
    fn carrier_preflight_rejects_nested_value_binding() {
        let expr = Expr::If {
            cond: Box::new(Expr::Const(crate::ir::Const::Bool(true))),
            then_branch: Box::new(Block {
                stmts: vec![Stmt::Let {
                    pattern: vec![Some("value".into())],
                    value: nested_return_if(),
                }],
                tail: BlockTail::Value(Expr::Unit),
            }),
            else_branch: Box::new(Block::just(Expr::Unit)),
        };

        assert!(!carrier_conversion_supported(&expr));
    }

    #[test]
    fn tail_match_detects_return_nested_in_arm_statement() {
        let block = Block::just(Expr::Match {
            struct_id: 0,
            selector: Box::new(Expr::Unit),
            cases: vec![MatchArm {
                variant: 0,
                bindings: Vec::new(),
                body: Box::new(Block {
                    stmts: vec![Stmt::Eval(nested_return_if())],
                    tail: BlockTail::Value(Expr::Unit),
                }),
            }],
        });

        assert!(block_contains_match_with_return_arm(&block));
    }

    #[test]
    fn world_returning_carrier_payload_is_hoisted_into_full_let() {
        let world_id = 7;
        let world_type = Type::Struct {
            struct_id: world_id,
            type_args: Vec::new(),
        };
        let return_type = Type::Tuple(vec![Type::UInt(64), world_type.clone()]);
        let mut program = Program::default();
        program.functions.insert(
            1,
            Function {
                module: 0,
                name: "world_step".into(),
                signature: Signature {
                    type_params: Vec::new(),
                    params: vec![Param {
                        name: "world".into(),
                        var: "world".into(),
                        ty: world_type,
                    }],
                    return_type: return_type.clone(),
                },
                body: Block::just(Expr::Unit),
                kind: FunctionKind::Synthetic,
                effects: Effects::WORLD,
                explicit_pure: false,
            },
        );
        let mut ctx = LiftCtx {
            program: &mut program,
            parent_ghost_params: Vec::new(),
            parent_name: "source".into(),
            parent_module: 0,
            parent_type_params: Vec::new(),
            ret_type: return_type,
            option_id: 8,
            abort_code_id: 9,
            return_flow_id: 0,
            world_id: Some(world_id),
            next_fid: 10,
            next_cont_slot: 0,
            target_types: BTreeMap::new(),
            deref_vars: BTreeSet::new(),
        };
        let block = Block {
            stmts: Vec::new(),
            tail: BlockTail::Return(Box::new(Expr::Call {
                fun: 1,
                type_args: Vec::new(),
                args: vec![Expr::Var("world".into())],
            })),
        };

        let lifted = lift_block_to_carrier(block, &mut ctx);

        let [Stmt::Let { pattern, value }] = lifted.stmts.as_slice() else {
            panic!("World-returning payload must be captured before packing")
        };
        assert_eq!(pattern.len(), 2);
        assert!(pattern.iter().all(Option::is_some));
        assert!(matches!(value, Expr::Call { fun: 1, .. }));
        let BlockTail::Value(Expr::Pack { fields, .. }) = &lifted.tail else {
            panic!("lifted return must produce the carrier")
        };
        let [Expr::Tuple(payload)] = fields.as_slice() else {
            panic!("carrier must reconstruct the complete tuple payload")
        };
        let bound: Vec<_> = pattern.iter().flatten().cloned().collect();
        let returned: Vec<_> = payload
            .iter()
            .map(|expr| match expr {
                Expr::Var(var) => var.clone(),
                other => panic!("carrier payload contains non-variable {other:?}"),
            })
            .collect();
        assert_eq!(returned, bound);
    }

    #[test]
    fn real_let_continuation_retains_pattern_world_after_captures() {
        let world_id = 7;
        let world_type = Type::Struct {
            struct_id: world_id,
            type_args: Vec::new(),
        };
        let mut program = Program::default();
        program.structs.insert(
            world_id,
            crate::ir::Struct {
                module_id: 0,
                name: "World".into(),
                qualified_name: crate::stage_04_effects::world::WORLD_QUALIFIED_NAME.into(),
                type_params: Vec::new(),
                fields: Vec::new(),
                variants: None,
                is_native: true,
            },
        );
        let mut scope = BTreeMap::new();
        scope.insert("world_0".into(), world_type.clone());
        scope.insert("world_1".into(), world_type);
        let source = Expr::If {
            cond: Box::new(Expr::Const(crate::ir::Const::Bool(true))),
            then_branch: Box::new(Block {
                stmts: Vec::new(),
                tail: BlockTail::Return(Box::new(Expr::Var("world_1".into()))),
            }),
            else_branch: Box::new(Block::just(Expr::Var("world_1".into()))),
        };
        let mut block = Block {
            stmts: vec![
                Stmt::Let {
                    pattern: vec![Some("world_2".into())],
                    value: source,
                },
                Stmt::Eval(Expr::Var("world_0".into())),
            ],
            tail: BlockTail::Value(Expr::Var("world_2".into())),
        };
        let mut ctx = LiftCtx {
            program: &mut program,
            parent_ghost_params: Vec::new(),
            parent_name: "source".into(),
            parent_module: 0,
            parent_type_params: Vec::new(),
            ret_type: Type::Unit,
            option_id: 8,
            abort_code_id: 9,
            return_flow_id: 0,
            world_id: Some(world_id),
            next_fid: 10,
            next_cont_slot: 0,
            target_types: BTreeMap::new(),
            deref_vars: BTreeSet::new(),
        };

        perform_lift_let(&mut block, 0, &scope, &mut ctx);

        let params: Vec<_> = ctx.program.functions[&10]
            .signature
            .params
            .iter()
            .map(|param| param.var.as_ref())
            .collect();
        assert_eq!(params, ["world_0", "world_2"]);
    }

    #[test]
    fn scalar_ssa_binding_keeps_the_type_of_its_previous_generation() {
        let state = Type::Struct {
            struct_id: 7,
            type_args: Vec::new(),
        };
        let abort = Type::Struct {
            struct_id: 8,
            type_args: Vec::new(),
        };
        let mut scope = BTreeMap::new();
        scope.insert("state_0".into(), state.clone());
        scope.insert("abort_0".into(), abort);

        assert_eq!(
            stable_ssa_pattern_type(&[Some("state_1".into())], &scope),
            Some(state)
        );
    }

    /// ...but a same-stem neighbour that is NOT the same slot must never
    /// retype the binding. Stage 7 numbers its callee-abort temporaries
    /// `__c_0`, `__c_1`, ... from one global counter, so `__c_0` and `__c_1`
    /// share a stem while holding unrelated types. Binding the AbortResult
    /// `__c_0` as the `*_aborts` predicate's `Bool` made `type_of` fail on the
    /// `match __c_0 : AbortResult` that follows, and
    /// `build_continuation_block` then discarded the whole continuation tail
    /// behind a constant `NoAbort`.
    #[test]
    fn synthetic_abort_temporary_is_not_retyped_by_its_stem_neighbour() {
        const OPTION_ID: StructId = 10;
        const ABORT_CODE_ID: StructId = 11;
        let program = Program::default();
        let abort_result = Type::Struct {
            struct_id: OPTION_ID,
            type_args: vec![Type::Struct {
                struct_id: ABORT_CODE_ID,
                type_args: Vec::new(),
            }],
        };
        let mut scope = BTreeMap::new();
        scope.insert(VarId::from("__c_1"), Type::Bool);

        let value = Expr::If {
            cond: Box::new(Expr::Var("__c_1".into())),
            then_branch: Box::new(Block::just(Expr::Pack {
                struct_id: OPTION_ID,
                type_args: vec![Type::Struct {
                    struct_id: ABORT_CODE_ID,
                    type_args: Vec::new(),
                }],
                variant: Some(1),
                fields: vec![Expr::Pack {
                    struct_id: ABORT_CODE_ID,
                    type_args: Vec::new(),
                    variant: None,
                    fields: vec![lit_u64(0)],
                }],
            })),
            else_branch: Box::new(Block::just(Expr::Pack {
                struct_id: OPTION_ID,
                type_args: vec![Type::Struct {
                    struct_id: ABORT_CODE_ID,
                    type_args: Vec::new(),
                }],
                variant: Some(0),
                fields: Vec::new(),
            })),
        };

        // The naming heuristic on its own DOES misfire here -- `__c_1` looks
        // like a later generation of `__c_0`. `corrects_borrow_skew` is the
        // only thing standing between that and a mistyped binding.
        assert_eq!(
            stable_ssa_pattern_type(&[Some("__c_0".into())], &scope),
            Some(Type::Bool)
        );

        assert_eq!(
            infer_let_value_type(
                &[Some("__c_0".into())],
                &value,
                &scope,
                &BTreeMap::new(),
                &BTreeSet::new(),
                &program,
            ),
            abort_result
        );
    }

    /// The deref guard is per-BINDER, not a blanket switch: a `*` somewhere
    /// else in the body must not stop the correction from firing on a slot
    /// nobody dereferences.
    #[test]
    fn the_deref_guard_declines_only_for_the_dereferenced_binder() {
        let program = Program::default();
        let mut scope = BTreeMap::new();
        scope.insert(VarId::from("x_0"), Type::UInt(256));
        scope.insert(VarId::from("r"), Type::Reference(Box::new(Type::UInt(256))));
        // An SSA merge of a `&u256` arm with a `u256` arm -- `type_of` answers
        // off the borrow arm, the stable generation `x_0` says `u256`.
        let merge = Expr::If {
            cond: Box::new(Expr::Const(crate::ir::Const::Bool(true))),
            then_branch: Box::new(Block::just(Expr::Var("r".into()))),
            else_branch: Box::new(Block::just(Expr::Var("x_0".into()))),
        };
        let infer = |deref: &BTreeSet<VarId>| {
            infer_let_value_type(
                &[Some("x_2".into())],
                &merge,
                &scope,
                &BTreeMap::new(),
                deref,
                &program,
            )
        };

        assert_eq!(infer(&BTreeSet::new()), Type::UInt(256));
        assert_eq!(
            infer(&[VarId::from("unrelated_3")].into_iter().collect()),
            Type::UInt(256)
        );
        assert_eq!(
            infer(&[VarId::from("x_2")].into_iter().collect()),
            Type::Reference(Box::new(Type::UInt(256)))
        );
    }
}
