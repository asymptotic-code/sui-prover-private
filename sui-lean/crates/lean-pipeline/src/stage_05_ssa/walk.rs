//! Stage-5 single-pass recursive walker.
//!
//! Handles:
//! - **Phase 1/2**: full alpha-rename of every `Stmt::Let` pattern +
//!   every `Var` / `BorrowLoc` / `WriteBack` reference. Walks each
//!   `If`/`Match`/`While`/`Quantifier` arm with save/restore of
//!   `Ctx::scope` so arm-local bindings don't leak; the counter is
//!   shared (single `&mut Ctx` threaded through) so siblings never
//!   collide.
//! - **Phase 3/4**: explicit phi via Tuple-Let when an `If`/`Match`
//!   appears at statement level (`Stmt::Eval(If/Match)` or
//!   `Stmt::Let { value: If/Match, .. }`). Value arms emit
//!   `Tuple([orig..., phi_vars])`; terminator arms keep their tails;
//!   surrounding `Stmt::Let` pattern is extended with fresh phi
//!   names. Outer scope is updated so post-If references resolve to
//!   the phi names.
//! - **Phase 5/6**: `Expr::While` `loop_state` synthesis + cross-level
//!   `Break`/`Continue` value rewrites.
//!
//! See `plans/lean-pipeline/stage-05-ssa.md` for the design.

use std::collections::{BTreeMap, BTreeSet};

use crate::ir::builder::tuple_or_single;
use crate::ir::visit::{
    walk_expr_default, walk_expr_mut_default, walk_stmt_default, MutVisitor, Visitor,
};
use crate::ir::{
    expr::{Block, BlockTail},
    BorrowNode, Const, Expr, Function, MatchArm, Program, Stmt, Type, VarId,
};

use super::ctx::{Ctx, LoopFrame};
use super::Stage5Error;

/// Rewrite every non-native function in `program`.
pub(crate) fn rewrite_program(program: &mut Program) -> Result<(), Stage5Error> {
    let fids: Vec<_> = program.functions.keys().copied().collect();
    let mut first_err: Option<Stage5Error> = None;
    for fid in fids {
        let func = program.functions.get(&fid).expect("fid from keys()");
        let var_types = super::var_types::collect(func, program);
        match rewrite_function(fid, func, var_types) {
            Ok(new_func) => {
                program.functions.insert(fid, new_func);
            }
            Err(err) => {
                // Per-function failure -- leave this function in its
                // pre-stage-5 form (no SSA rename) and continue with
                // the rest. Without this, an `UnboundReference` from
                // one upstream-buggy function would poison every
                // later function (none would be alpha-renamed) and
                // cascade into the baseline well-formedness
                // invariant complaining about `$t<N>_<M>` references
                // that downstream stages emit. Record the first
                // error so the caller still sees a warning in
                // Permissive mode.
                eprintln!("new-pipeline: stage 5 (SSA) skipping fn {}: {:?}", fid, err);
                if first_err.is_none() {
                    first_err = Some(err);
                }
            }
        }
    }
    match first_err {
        Some(err) => Err(err),
        None => Ok(()),
    }
}

fn rewrite_function(
    fid: crate::ir::FunId,
    func: &Function,
    var_types: std::collections::BTreeMap<VarId, Type>,
) -> Result<Function, Stage5Error> {
    let mut ctx = Ctx::new(fid);
    ctx.var_types = var_types;
    let mut new_params = Vec::with_capacity(func.signature.params.len());
    for p in &func.signature.params {
        let fresh = ctx.fresh(&p.var);
        ctx.bind(p.var.clone(), fresh.clone());
        new_params.push(crate::ir::Param {
            name: p.name.clone(),
            var: fresh,
            ty: p.ty.clone(),
        });
    }
    let new_body = rewrite_block(&func.body, &mut ctx)?;
    Ok(Function {
        module: func.module,
        name: func.name.clone(),
        signature: crate::ir::Signature {
            type_params: func.signature.type_params.clone(),
            params: new_params,
            return_type: func.signature.return_type.clone(),
        },
        body: new_body,
        kind: func.kind.clone(),
        effects: func.effects,
        explicit_pure: func.explicit_pure,
    })
}

// ---------------------------------------------------------------------------
// Block / Stmt / Tail
// ---------------------------------------------------------------------------

fn rewrite_block(block: &Block, ctx: &mut Ctx) -> Result<Block, Stage5Error> {
    let mut new_stmts = Vec::with_capacity(block.stmts.len());
    let n = block.stmts.len();
    for i in 0..n {
        let stmt = &block.stmts[i];
        // While at statement level needs the post-loop continuation
        // (subsequent stmts + tail) for `loop_state` synthesis.
        match stmt {
            Stmt::Eval(Expr::While {
                header, cond, body, ..
            }) => {
                let post_stmts = &block.stmts[i + 1..];
                let new_stmt =
                    rewrite_while_at_stmt(None, header, cond, body, post_stmts, &block.tail, ctx)?;
                new_stmts.push(new_stmt);
            }
            Stmt::Let {
                pattern,
                value: Expr::While {
                    header, cond, body, ..
                },
            } => {
                let post_stmts = &block.stmts[i + 1..];
                let new_stmt = rewrite_while_at_stmt(
                    Some(pattern),
                    header,
                    cond,
                    body,
                    post_stmts,
                    &block.tail,
                    ctx,
                )?;
                new_stmts.push(new_stmt);
            }
            other => new_stmts.push(rewrite_stmt(other, ctx)?),
        }
    }
    let new_tail = rewrite_tail(&block.tail, ctx)?;
    Ok(Block {
        stmts: new_stmts,
        tail: new_tail,
    })
}

fn rewrite_stmt(stmt: &Stmt, ctx: &mut Ctx) -> Result<Stmt, Stage5Error> {
    // Phi handling: an If/Match at the top of a statement's value
    // position triggers phi rewriting (Phases 3-4).
    match stmt {
        Stmt::Eval(Expr::If {
            cond,
            then_branch,
            else_branch,
        }) => phi_rewrite_if(None, cond, then_branch, else_branch, ctx),
        Stmt::Eval(Expr::Match {
            struct_id,
            selector,
            cases,
            ..
        }) => phi_rewrite_match(None, *struct_id, selector, cases, ctx),
        Stmt::Let {
            pattern,
            value:
                Expr::If {
                    cond,
                    then_branch,
                    else_branch,
                },
        } => phi_rewrite_if(Some(pattern), cond, then_branch, else_branch, ctx),
        Stmt::Let {
            pattern,
            value:
                Expr::Match {
                    struct_id,
                    selector,
                    cases,
                    ..
                },
        } => phi_rewrite_match(Some(pattern), *struct_id, selector, cases, ctx),

        // All other Stmt shapes: alpha-rename only.
        Stmt::Let { pattern, value } => {
            // Walk value FIRST with the pre-binding scope (so a
            // `Var(r)` on the RHS resolves to the OLD SSA name when
            // the pattern shadows `r` -- the stage-3 mut-to-let
            // shape).
            let new_value = rewrite_expr(value, ctx)?;
            let new_pattern: Vec<Option<VarId>> = pattern
                .iter()
                .map(|slot| match slot {
                    Some(v) => {
                        let fresh = ctx.fresh(v);
                        ctx.bind(v.clone(), fresh.clone());
                        Some(fresh)
                    }
                    None => None,
                })
                .collect();
            Ok(Stmt::Let {
                pattern: new_pattern,
                value: new_value,
            })
        }
        Stmt::Eval(e) => Ok(Stmt::Eval(rewrite_expr(e, ctx)?)),
    }
}

fn rewrite_tail(tail: &BlockTail, ctx: &mut Ctx) -> Result<BlockTail, Stage5Error> {
    match tail {
        BlockTail::Value(e) => Ok(BlockTail::Value(rewrite_expr(e, ctx)?)),
        BlockTail::Break { level, value } => {
            // Phase 6: rewrite the carried value to the target
            // loop's `loop_state` tuple shape (when loop_state is
            // non-empty). The target is `loop_at(level)`.
            let new_value = rewrite_loop_jump_value(*level, value, ctx)?;
            Ok(BlockTail::Break {
                level: *level,
                value: Box::new(new_value),
            })
        }
        BlockTail::Continue { level, value } => {
            let new_value = rewrite_loop_jump_value(*level, value, ctx)?;
            Ok(BlockTail::Continue {
                level: *level,
                value: Box::new(new_value),
            })
        }
        BlockTail::Return(value) => Ok(BlockTail::Return(Box::new(rewrite_expr(value, ctx)?))),
        BlockTail::ReturnFromBlock { level, value } => Ok(BlockTail::ReturnFromBlock {
            level: *level,
            value: Box::new(rewrite_expr(value, ctx)?),
        }),
        BlockTail::Abort { code } => Ok(BlockTail::Abort {
            code: Box::new(rewrite_expr(code, ctx)?),
        }),
    }
}

/// Rewrite the value carried by a `BlockTail::Break` /
/// `BlockTail::Continue { level }`. If the target loop's
/// `loop_state` is non-empty, the carried value is replaced with
/// `Tuple([loop_state vars in current scope])`. If the original
/// value carries a non-Unit payload AND loop_state is non-empty,
/// the payload is preserved as the first element of the tuple.
fn rewrite_loop_jump_value(level: u32, value: &Expr, ctx: &mut Ctx) -> Result<Expr, Stage5Error> {
    let walked = rewrite_expr(value, ctx)?;
    let loop_state = ctx
        .loop_at(level)
        .map(|f| f.loop_state.clone())
        .unwrap_or_default();
    if loop_state.is_empty() {
        return Ok(walked);
    }
    // Resolve each loop_state var in current scope.
    let mut elems: Vec<Expr> = Vec::with_capacity(loop_state.len());
    for v in &loop_state {
        elems.push(Expr::Var(ctx.lookup(v)?));
    }
    Ok(tuple_or_single(elems))
}

// ---------------------------------------------------------------------------
// Expr (non-stmt-level branching cases)
// ---------------------------------------------------------------------------

/// Alpha-rename every reference in `expr` against the current scope.
/// Thin functional shim over the in-place [`Renamer`] so call sites keep
/// the `&Expr -> Result<Expr>` shape. Statement-level phi / While
/// restructuring lives in `rewrite_block` / `rewrite_stmt` /
/// `rewrite_while_at_stmt`; this only handles SUB-expression positions
/// (alpha-rename, plus the re-entry `While` path).
fn rewrite_expr(expr: &Expr, ctx: &mut Ctx) -> Result<Expr, Stage5Error> {
    let mut cloned = expr.clone();
    let mut renamer = Renamer { ctx, err: None };
    renamer.visit_expr_mut(&mut cloned);
    match renamer.err {
        Some(e) => Err(e),
        None => Ok(cloned),
    }
}

/// In-place alpha-renamer. The mechanical arms (BinOp, Call, Tuple, ...)
/// recurse through `walk_expr_mut_default`; only leaf var-carriers and
/// the scope-bearing control-flow arms are overridden. Control-flow arms
/// delegate sub-block restructuring to the functional `rewrite_block`
/// (which performs phi / loop_state synthesis) -- so every block-bearing
/// variant is overridden and the default block walk is never used.
/// `err` short-circuits the rest of the traversal once a lookup fails.
struct Renamer<'a> {
    ctx: &'a mut Ctx,
    err: Option<Stage5Error>,
}

impl Renamer<'_> {
    fn rename(&mut self, v: &VarId) -> Option<VarId> {
        match self.ctx.lookup(v) {
            Ok(n) => Some(n),
            Err(e) => {
                self.err = Some(e);
                None
            }
        }
    }
}

impl MutVisitor for Renamer<'_> {
    fn visit_expr_mut(&mut self, e: &mut Expr) {
        if self.err.is_some() {
            return;
        }
        match e {
            // ---- Atoms / leaf var carriers ----
            Expr::Var(v) | Expr::BorrowLoc(v) => {
                if let Some(n) = self.rename(v) {
                    *v = n;
                }
            }
            Expr::Borrow { step, base } => {
                match rewrite_path_step(step, self.ctx) {
                    Ok(s) => *step = s,
                    Err(e) => {
                        self.err = Some(e);
                        return;
                    }
                }
                self.visit_expr_mut(base);
            }
            Expr::Update { step, base, value } => {
                match rewrite_path_step(step, self.ctx) {
                    Ok(s) => *step = s,
                    Err(e) => {
                        self.err = Some(e);
                        return;
                    }
                }
                self.visit_expr_mut(base);
                if self.err.is_some() {
                    return;
                }
                self.visit_expr_mut(value);
            }
            Expr::WriteBack {
                node, child, world, ..
            } => {
                match rewrite_borrow_node(node, self.ctx) {
                    Ok(n) => *node = n,
                    Err(e) => {
                        self.err = Some(e);
                        return;
                    }
                }
                match self.rename(child) {
                    Some(n) => *child = n,
                    None => return,
                }
                if let Some(w) = world {
                    if let Some(n) = self.rename(w) {
                        *w = n;
                    }
                }
            }
            Expr::IsParent { node, child, .. } => {
                match rewrite_borrow_node(node, self.ctx) {
                    Ok(n) => *node = n,
                    Err(e) => {
                        self.err = Some(e);
                        return;
                    }
                }
                if let Some(n) = self.rename(child) {
                    *child = n;
                }
            }

            // ---- Sub-expression branching: alpha-rename only, no phi.
            // Phi happens at statement level (see `rewrite_stmt`). Each
            // arm is walked with a saved/restored scope clone so
            // arm-local bindings don't leak.
            Expr::If {
                cond,
                then_branch,
                else_branch,
            } => {
                self.visit_expr_mut(cond);
                if self.err.is_some() {
                    return;
                }
                let saved = self.ctx.scope.clone();
                match rewrite_block(then_branch, self.ctx) {
                    Ok(b) => **then_branch = b,
                    Err(e) => {
                        self.err = Some(e);
                        return;
                    }
                }
                self.ctx.scope = saved.clone();
                match rewrite_block(else_branch, self.ctx) {
                    Ok(b) => **else_branch = b,
                    Err(e) => {
                        self.err = Some(e);
                        return;
                    }
                }
                self.ctx.scope = saved;
            }
            Expr::Match {
                selector, cases, ..
            } => {
                self.visit_expr_mut(selector);
                if self.err.is_some() {
                    return;
                }
                let saved = self.ctx.scope.clone();
                for arm in cases.iter_mut() {
                    self.ctx.scope = saved.clone();
                    let mut new_bindings = Vec::with_capacity(arm.bindings.len());
                    for b in &arm.bindings {
                        let fresh = self.ctx.fresh(b);
                        self.ctx.bind(b.clone(), fresh.clone());
                        new_bindings.push(fresh);
                    }
                    arm.bindings = new_bindings;
                    match rewrite_block(&arm.body, self.ctx) {
                        Ok(b) => *arm.body = b,
                        Err(e) => {
                            self.err = Some(e);
                            return;
                        }
                    }
                }
                self.ctx.scope = saved;
            }

            // ---- Loops -- never reached in the forward flow. Stage 2
            // lifts every loop to statement level, where `rewrite_block`
            // intercepts it for `loop_state` synthesis; a `While` in a
            // value (sub-expression) position is unexpected IR (verified
            // 0/96 client packages). Surface it rather than silently
            // mis-handle a loop with no visible post-loop continuation
            // -- per-function isolation in `rewrite_program` skips just
            // this function.
            Expr::While { .. } => {
                self.err = Some(Stage5Error::WhileInValuePosition {
                    function: self.ctx.function,
                });
            }

            // ---- Quantifiers ----
            Expr::Quantifier {
                binder,
                domain,
                body,
                ..
            } => {
                match domain {
                    crate::ir::QuantDomain::Unbounded => {}
                    crate::ir::QuantDomain::Range { start, end } => {
                        self.visit_expr_mut(start);
                        if self.err.is_some() {
                            return;
                        }
                        self.visit_expr_mut(end);
                        if self.err.is_some() {
                            return;
                        }
                    }
                    crate::ir::QuantDomain::Collection(c) => {
                        self.visit_expr_mut(c);
                        if self.err.is_some() {
                            return;
                        }
                    }
                    crate::ir::QuantDomain::VecRange { vec, start, end } => {
                        self.visit_expr_mut(vec);
                        if self.err.is_some() {
                            return;
                        }
                        self.visit_expr_mut(start);
                        if self.err.is_some() {
                            return;
                        }
                        self.visit_expr_mut(end);
                        if self.err.is_some() {
                            return;
                        }
                    }
                }
                let saved = self.ctx.scope.clone();
                let fresh_binder = self.ctx.fresh(binder);
                self.ctx.bind(binder.clone(), fresh_binder.clone());
                *binder = fresh_binder;
                match rewrite_block(body, self.ctx) {
                    Ok(b) => **body = b,
                    Err(e) => {
                        self.ctx.scope = saved;
                        self.err = Some(e);
                        return;
                    }
                }
                self.ctx.scope = saved;
            }
            Expr::LabeledBlock { body, .. } => match rewrite_block(body, self.ctx) {
                Ok(b) => **body = b,
                Err(e) => {
                    self.err = Some(e);
                }
            },

            // ---- Mechanical recursion (BinOp, UnOp, BitOp, Call, Tuple,
            // Pack, Unpack, Field, ReadRef, WriteRef, ToProp, ToBool,
            // Const, Unit): rename children via the default walk.
            _ => walk_expr_mut_default(self, e),
        }
    }
}

fn rewrite_borrow_node(node: &BorrowNode, ctx: &Ctx) -> Result<BorrowNode, Stage5Error> {
    match node {
        BorrowNode::LocalRoot(v) => Ok(BorrowNode::LocalRoot(ctx.lookup(v)?)),
        BorrowNode::Reference(v) => Ok(BorrowNode::Reference(ctx.lookup(v)?)),
        BorrowNode::GlobalRoot(_) => Ok(node.clone()),
        BorrowNode::SpecGlobalRoot { .. } => Ok(node.clone()),
    }
}

// ---------------------------------------------------------------------------
// Phi rewriting at statement level (Phases 3 + 4)
// ---------------------------------------------------------------------------

/// Result of walking one arm of an `If` / `Match` for phi computation.
struct ArmWalk {
    block: Block,
    /// Source-name vars bound inside the arm.
    defined: BTreeSet<VarId>,
    /// Per-arm scope after the walk; used to resolve each phi var's
    /// fresh SSA name from this arm's perspective.
    scope_after: BTreeMap<VarId, VarId>,
    /// What kind of tail the arm has. Used to decide phi
    /// participation and tail rewriting.
    tail_kind: TailKind,
    /// For Match arms: the alpha-renamed variant bindings, in the
    /// order the input arm declared them. Captured at the moment of
    /// allocation -- NOT recovered from `scope_after`, which would
    /// be wrong if the arm body rebinds a binding via a `Stmt::Let`.
    /// For If arms, this is always empty.
    renamed_bindings: Vec<VarId>,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum TailKind {
    Value,
    Terminator,
}

fn tail_kind_of(tail: &BlockTail) -> TailKind {
    match tail {
        BlockTail::Value(_) => TailKind::Value,
        _ => TailKind::Terminator,
    }
}

/// Walk an arm with `ctx.scope` set to `outer_scope`. Returns the
/// rewritten block, the per-arm scope-after-walk, the defined set
/// (source names introduced inside the arm), the tail kind, and the
/// alpha-renamed variant bindings (for `Match` arms; empty for `If`).
///
/// `ctx.scope` is set to `outer_scope` on entry and left in the
/// arm's post-walk state on exit. Callers reset before the next
/// arm.
fn walk_arm_for_phi(
    arm_body: &Block,
    outer_scope: &BTreeMap<VarId, VarId>,
    arm_local_bindings: &[VarId],
    ctx: &mut Ctx,
) -> Result<ArmWalk, Stage5Error> {
    ctx.scope = outer_scope.clone();
    // For Match arms, the variant bindings are arm-local:
    // alpha-rename them inside the arm scope before walking the body.
    // Capture the fresh names eagerly -- recovering them from
    // `scope_after` later would silently pick up any rebind the arm
    // body does on the same source name.
    let mut renamed_bindings: Vec<VarId> = Vec::with_capacity(arm_local_bindings.len());
    for b in arm_local_bindings {
        let fresh = ctx.fresh(b);
        ctx.bind(b.clone(), fresh.clone());
        renamed_bindings.push(fresh);
    }
    let new_body = rewrite_block(arm_body, ctx)?;
    let scope_after = ctx.scope.clone();
    let arm_local_set: BTreeSet<&VarId> = arm_local_bindings.iter().collect();
    // `defined` = source names whose SSA binding differs from the outer
    // scope after the arm walk -- i.e. newly bound (`None != Some(v)`) OR
    // rebound/shadowed (`Some(old) != Some(v)`). Arm-local variant
    // bindings are excluded (they don't escape arms for phi purposes).
    let mut defined: BTreeSet<VarId> = BTreeSet::new();
    for (k, v) in &scope_after {
        if arm_local_set.contains(k) {
            continue;
        }
        if outer_scope.get(k) != Some(v) {
            defined.insert(k.clone());
        }
    }
    Ok(ArmWalk {
        block: new_body,
        defined,
        scope_after,
        tail_kind: tail_kind_of(&arm_body.tail),
        renamed_bindings,
    })
}

/// Compute the phi var set: vars defined in **all** Value-tailed arms,
/// plus vars defined in some Value-tailed arm AND already present in
/// outer scope (half-phi). Excludes terminator arms.
///
/// Returns a sorted `Vec<VarId>` for deterministic output ordering.
fn compute_phi_vars(arms: &[ArmWalk], outer_scope: &BTreeMap<VarId, VarId>) -> Vec<VarId> {
    let value_arms: Vec<&ArmWalk> = arms
        .iter()
        .filter(|a| a.tail_kind == TailKind::Value)
        .collect();
    if value_arms.is_empty() {
        return Vec::new();
    }
    // Intersection of defined sets across Value arms.
    let mut intersection: BTreeSet<VarId> = value_arms[0].defined.clone();
    for arm in &value_arms[1..] {
        intersection.retain(|v| arm.defined.contains(v));
    }
    // Half-phi: union of defined sets, restricted to outer-scope vars.
    let mut half_phi: BTreeSet<VarId> = BTreeSet::new();
    for arm in &value_arms {
        for v in &arm.defined {
            if outer_scope.contains_key(v) {
                half_phi.insert(v.clone());
            }
        }
    }
    let mut combined: BTreeSet<VarId> = intersection;
    combined.extend(half_phi);
    combined.into_iter().collect()
}

/// Build the new tail for a Value-tailed arm: `Tuple([orig...,
/// phi_in_arm...])`. `pattern_arity` is the number of slots in the
/// surrounding `Stmt::Let` pattern (0 if `Stmt::Eval`).
fn build_phi_arm_tail(
    arm: &ArmWalk,
    phi_vars: &[VarId],
    pattern_arity: usize,
) -> Result<BlockTail, Stage5Error> {
    let BlockTail::Value(orig_value) = &arm.block.tail else {
        // Caller should only call this for Value-tailed arms.
        unreachable!("build_phi_arm_tail called on non-Value tail");
    };
    let mut components: Vec<Expr> = Vec::with_capacity(pattern_arity + phi_vars.len());
    // Original tail components.
    if pattern_arity > 1 {
        // A multi-slot let pattern requires the arm's tail to already
        // be a Tuple of matching arity (guaranteed by construction --
        // 0/96 client packages hit a mismatch). Splat its elements.
        // Consistent with the `unreachable!` / `expect` guards above:
        // a mismatch is a structural-invariant violation, not a case
        // to paper over.
        let Expr::Tuple(elems) = orig_value else {
            unreachable!("phi arm tail for a {pattern_arity}-slot let pattern must be a Tuple");
        };
        assert_eq!(
            elems.len(),
            pattern_arity,
            "phi arm tail Tuple arity must match the surrounding let pattern",
        );
        components.extend(elems.clone());
    } else if pattern_arity == 1 {
        components.push(orig_value.clone());
    }
    // Phi var components in arm scope.
    for v in phi_vars {
        let resolved = arm
            .scope_after
            .get(v)
            .cloned()
            .expect("phi var should be in arm scope");
        components.push(Expr::Var(resolved));
    }
    Ok(BlockTail::Value(tuple_or_single(components)))
}

/// Phi-rewrite a `Stmt::Eval(If)` or `Stmt::Let { value: If, .. }`.
/// `pattern` is `Some(pat)` for the Let case, `None` for Eval.
fn phi_rewrite_if(
    pattern: Option<&Vec<Option<VarId>>>,
    cond: &Expr,
    then_branch: &Block,
    else_branch: &Block,
    ctx: &mut Ctx,
) -> Result<Stmt, Stage5Error> {
    let new_cond = rewrite_expr(cond, ctx)?;
    let outer_scope = ctx.scope.clone();
    let then_walk = walk_arm_for_phi(then_branch, &outer_scope, &[], ctx)?;
    let else_walk = walk_arm_for_phi(else_branch, &outer_scope, &[], ctx)?;
    ctx.scope = outer_scope.clone();
    let arms = vec![then_walk, else_walk];
    finish_phi_branching(
        pattern,
        &arms,
        &outer_scope,
        |new_arms| Expr::If {
            cond: Box::new(new_cond.clone()),
            then_branch: Box::new(new_arms[0].clone()),
            else_branch: Box::new(new_arms[1].clone()),
        },
        ctx,
    )
}

fn phi_rewrite_match(
    pattern: Option<&Vec<Option<VarId>>>,
    struct_id: crate::ir::StructId,
    selector: &Expr,
    cases: &[MatchArm],
    ctx: &mut Ctx,
) -> Result<Stmt, Stage5Error> {
    let new_selector = rewrite_expr(selector, ctx)?;
    let outer_scope = ctx.scope.clone();
    let mut arms = Vec::with_capacity(cases.len());
    let mut bindings_per_arm: Vec<Vec<VarId>> = Vec::with_capacity(cases.len());
    for arm in cases {
        let walk = walk_arm_for_phi(&arm.body, &outer_scope, &arm.bindings, ctx)?;
        // Read renamed bindings from `walk.renamed_bindings` (set at
        // allocation time). Using `scope_after` would be wrong if the
        // arm body rebinds a variant-binding source name with a
        // later `Stmt::Let`.
        bindings_per_arm.push(walk.renamed_bindings.clone());
        arms.push(walk);
    }
    ctx.scope = outer_scope.clone();
    let variants: Vec<usize> = cases.iter().map(|c| c.variant).collect();
    finish_phi_branching(
        pattern,
        &arms,
        &outer_scope,
        |new_arms| {
            let cases: Vec<MatchArm> = new_arms
                .iter()
                .zip(variants.iter())
                .zip(bindings_per_arm.iter())
                .map(|((blk, variant), bindings)| MatchArm {
                    variant: *variant,
                    bindings: bindings.clone(),
                    body: Box::new(blk.clone()),
                })
                .collect();
            Expr::Match {
                struct_id,
                selector: Box::new(new_selector.clone()),
                cases,
            }
        },
        ctx,
    )
}

/// Common tail of `phi_rewrite_if` / `phi_rewrite_match`. `build` is
/// a closure that builds the surrounding `Expr::If` / `Match` given
/// the rewritten arm blocks.
fn finish_phi_branching<F>(
    pattern: Option<&Vec<Option<VarId>>>,
    arms: &[ArmWalk],
    outer_scope: &BTreeMap<VarId, VarId>,
    build: F,
    ctx: &mut Ctx,
) -> Result<Stmt, Stage5Error>
where
    F: Fn(&[Block]) -> Expr,
{
    let phi_vars = compute_phi_vars(arms, outer_scope);

    // Note: a var defined in some Value arm but not all AND not in
    // outer scope is arm-local. It naturally doesn't escape the
    // merge: `compute_phi_vars` excludes it from `phi_vars`, and the
    // outer scope isn't updated to map it. If post-merge code
    // references the var, the base validator catches it via
    // `UnboundVariable`. We don't emit a defensive reject here --
    // an earlier version did, but it false-positived on perfectly
    // legal arm-internal bindings.

    // Determine the existing pattern's arity (slots in the let, or 0
    // for Eval).
    let pattern_arity = pattern.map(|p| p.len()).unwrap_or(0);

    // For each arm, rewrite the tail if needed.
    let new_blocks: Vec<Block> = arms
        .iter()
        .map(|arm| {
            if arm.tail_kind == TailKind::Value && (pattern_arity > 0 || !phi_vars.is_empty()) {
                let new_tail = build_phi_arm_tail(arm, &phi_vars, pattern_arity)?;
                Ok::<_, Stage5Error>(Block {
                    stmts: arm.block.stmts.clone(),
                    tail: new_tail,
                })
            } else {
                Ok(arm.block.clone())
            }
        })
        .collect::<Result<Vec<_>, _>>()?;

    let new_branching = build(&new_blocks);

    // Allocate fresh names for the existing pattern (if any) AND for
    // phi vars. Update outer scope so downstream code resolves
    // correctly.
    let mut new_pattern: Vec<Option<VarId>> = Vec::new();
    if let Some(pat) = pattern {
        for slot in pat {
            match slot {
                Some(v) => {
                    let fresh = ctx.fresh(v);
                    ctx.bind(v.clone(), fresh.clone());
                    new_pattern.push(Some(fresh));
                }
                None => new_pattern.push(None),
            }
        }
    }
    for v in &phi_vars {
        let fresh = ctx.fresh(v);
        ctx.bind(v.clone(), fresh.clone());
        new_pattern.push(Some(fresh));
    }

    if new_pattern.is_empty() {
        // Stmt::Eval(If/Match), no phi vars introduced.
        Ok(Stmt::Eval(new_branching))
    } else {
        Ok(Stmt::Let {
            pattern: new_pattern,
            value: new_branching,
        })
    }
}

// ---------------------------------------------------------------------------
// Free-var / bound-var collection (Phase 5 pre-pass support)
// ---------------------------------------------------------------------------

/// Collects every `VarId` *referenced* in a sub-tree (all mentions, not
/// scope-aware -- this is "all uses", not free vars). Structural-var
/// carriers (`BorrowLoc`, `WriteBack`, `IsParent`, `MapKey::df_value`)
/// are recorded explicitly since `walk_expr_default` treats them as
/// leaves. `While::iter_locals` are intentionally NOT descended (they
/// are empty in the single-pass flow; skipping preserves loop_state
/// computation on re-entry over already-stage-5 IR).
struct RefCollector<'a> {
    out: &'a mut BTreeSet<VarId>,
}

impl Visitor for RefCollector<'_> {
    fn visit_expr(&mut self, e: &Expr) {
        match e {
            Expr::Var(v) | Expr::BorrowLoc(v) => {
                self.out.insert(v.clone());
            }
            Expr::WriteBack {
                node, child, world, ..
            } => {
                self.out.insert(child.clone());
                if let BorrowNode::LocalRoot(v) | BorrowNode::Reference(v) = node {
                    self.out.insert(v.clone());
                }
                if let Some(v) = world {
                    self.out.insert(v.clone());
                }
            }
            Expr::IsParent { node, child, .. } => {
                self.out.insert(child.clone());
                if let BorrowNode::LocalRoot(v) | BorrowNode::Reference(v) = node {
                    self.out.insert(v.clone());
                }
            }
            Expr::Borrow { step, .. } | Expr::Update { step, .. } => {
                if let crate::ir::path::PathStep::MapKey {
                    df_value: Some(v), ..
                } = step
                {
                    self.out.insert(v.clone());
                }
                walk_expr_default(self, e);
            }
            Expr::While {
                header, cond, body, ..
            } => {
                self.visit_block(header);
                self.visit_expr(cond);
                self.visit_block(body);
            }
            _ => walk_expr_default(self, e),
        }
    }
}

fn collect_refs_block(block: &Block, out: &mut BTreeSet<VarId>) {
    RefCollector { out }.visit_block(block);
}

fn collect_refs_expr(expr: &Expr, out: &mut BTreeSet<VarId>) {
    RefCollector { out }.visit_expr(expr);
}

fn collect_refs_stmt(stmt: &Stmt, out: &mut BTreeSet<VarId>) {
    RefCollector { out }.visit_stmt(stmt);
}

fn collect_refs_tail(tail: &BlockTail, out: &mut BTreeSet<VarId>) {
    RefCollector { out }.visit_tail(tail);
}

/// Collects every `VarId` bound by a `Stmt::Let` pattern anywhere in a
/// sub-tree (used to detect loop-carried vars). Match-arm bindings,
/// quantifier binders, and `While::iter_locals` binders are NOT counted
/// (arm/loop/quant-local; they don't escape). `BitOp` operands and
/// `While::iter_locals` inits are not descended -- they never carry
/// `Let` bindings -- matching the pre-refactor collector exactly.
struct BindCollector<'a> {
    out: &'a mut BTreeSet<VarId>,
}

impl Visitor for BindCollector<'_> {
    fn visit_stmt(&mut self, s: &Stmt) {
        if let Stmt::Let { pattern, .. } = s {
            for slot in pattern.iter().flatten() {
                self.out.insert(slot.clone());
            }
        }
        walk_stmt_default(self, s);
    }

    fn visit_bitop(&mut self, _op: &crate::ir::BitOp) {}

    fn visit_expr(&mut self, e: &Expr) {
        if let Expr::While {
            header, cond, body, ..
        } = e
        {
            self.visit_block(header);
            self.visit_expr(cond);
            self.visit_block(body);
        } else {
            walk_expr_default(self, e);
        }
    }
}

fn collect_binds_block(block: &Block, out: &mut BTreeSet<VarId>) {
    BindCollector { out }.visit_block(block);
}

fn rewrite_path_step(
    step: &crate::ir::path::PathStep,
    ctx: &mut Ctx,
) -> Result<crate::ir::path::PathStep, Stage5Error> {
    use crate::ir::path::PathStep;
    Ok(match step {
        PathStep::Field { .. } | PathStep::VariantField { .. } => step.clone(),
        PathStep::VecIndex(i) => PathStep::VecIndex(Box::new(rewrite_expr(i, ctx)?)),
        PathStep::MapKey {
            key,
            key_type,
            value_type,
            df_value,
        } => PathStep::MapKey {
            key: Box::new(rewrite_expr(key, ctx)?),
            key_type: key_type.clone(),
            value_type: value_type.clone(),
            df_value: df_value.as_ref().map(|v| ctx.lookup(v)).transpose()?,
        },
    })
}

// ---------------------------------------------------------------------------
// While at statement level (Phase 5)
// ---------------------------------------------------------------------------

/// Compute `loop_state` for a While at stmt position. `post_stmts`
/// is the surrounding block's `stmts[i+1..]`; `post_tail` is the
/// surrounding block's `tail`; `outer_scope` is the SSA scope at
/// loop entry, used to detect WriteBack-on-capture chains (an
/// outer-scope source-name re-bound somewhere inside the body --
/// the IR signature of mutation propagation through the loop).
/// Returns a deterministic sorted list of source-name vars.
fn compute_loop_state(
    header: &Block,
    cond: &Expr,
    body: &Block,
    post_stmts: &[Stmt],
    post_tail: &BlockTail,
    outer_scope: &BTreeMap<VarId, VarId>,
) -> Vec<VarId> {
    let mut header_refs: BTreeSet<VarId> = BTreeSet::new();
    collect_refs_block(header, &mut header_refs);
    let mut cond_refs: BTreeSet<VarId> = BTreeSet::new();
    collect_refs_expr(cond, &mut cond_refs);
    let mut body_refs: BTreeSet<VarId> = BTreeSet::new();
    collect_refs_block(body, &mut body_refs);
    let mut post_refs: BTreeSet<VarId> = BTreeSet::new();
    for s in post_stmts {
        collect_refs_stmt(s, &mut post_refs);
    }
    collect_refs_tail(post_tail, &mut post_refs);
    let mut outer_refs = header_refs;
    outer_refs.extend(post_refs.iter().cloned());
    outer_refs.extend(cond_refs.iter().cloned());

    let mut header_binds: BTreeSet<VarId> = BTreeSet::new();
    collect_binds_block(header, &mut header_binds);
    // The header runs before the condition and before the body on EVERY
    // iteration, so most of what it binds is answered within the same
    // iteration and carries nothing across the back edge. Only a read the
    // header has not already answered can observe the previous iteration's
    // value; `upward_exposed` is that analysis.
    let (header_exposed, header_must_bind) = upward_exposed(header);
    let mut body_binds: BTreeSet<VarId> = BTreeSet::new();
    collect_binds_block(body, &mut body_binds);

    // A var is loop-carried iff it is rebound inside the body (`binds`)
    // AND it is either:
    //   - referenced by the immediate surrounding block (header / cond /
    //     post-loop continuation) -- a "local" loop variable; or
    //   - already in outer scope -- a mutation propagated in by stage-3
    //     mut-to-let (a WriteRef / WriteBack on `&mut <outer>`, or an
    //     augmented-return Call rebinding the same source-name). Move's
    //     bytecode gives plain shadow `let`s distinct `VarId`s, so only
    //     true mutations re-enter an outer source-name here.
    //
    // The mutation must thread through `iter_locals` so each iteration
    // sees the latest value; without lifting, the recursive call
    // re-passes the pre-loop value and per-iteration mutations are
    // silently dropped. The loop's exit-value is bound to a fresh
    // post-loop SSA name that the enclosing scope picks up via the
    // normal phi / post-loop rebind machinery.
    //
    // Equivalently `binds ∩ (refs ∪ outer_scope)`; iterating the
    // `BTreeSet` keeps the result deterministically sorted.
    let mut state: BTreeSet<VarId> = body_binds
        .into_iter()
        .filter(|v| outer_refs.contains(v) || outer_scope.contains_key(v))
        .collect();
    // A header bind is loop-carried only when a read can observe a value
    // from the PREVIOUS iteration:
    //
    //   - the header reads it before binding it (`tick := tick + 1`, the
    //     Sui `test_scenario::next_with_context` World token);
    //   - the header binds it on only some paths, and the condition or the
    //     body reads it -- the unbound path falls through to the older value;
    //   - it is an outer-scope name the header rebinds and post-loop code
    //     reads: the restored outer scope would hand back the pre-loop value.
    //
    // Everything else the header binds is answered inside the iteration that
    // wrote it. Threading those anyway put dead parameters on every generated
    // loop function, `_step` and `.after`, and dead fields in the `Step.cont`
    // payload -- an ABI change with nothing behind it. A header bind that only
    // post-loop code reads is already threaded as a `live_out` (below), which
    // captures it at the cond-false exit without widening the carried state.
    state.extend(header_binds.into_iter().filter(|v| {
        header_exposed.contains(v)
            || (!header_must_bind.contains(v) && (cond_refs.contains(v) || body_refs.contains(v)))
            || (outer_scope.contains_key(v) && post_refs.contains(v))
    }));
    state.into_iter().collect()
}

/// `(upward_exposed, must_bind)` for `block`.
///
/// `upward_exposed` is every var the block may READ before it WRITES it --
/// a use that reaches back past the block's own bindings. `must_bind` is
/// every var the block binds on EVERY path through it; a read after such a
/// bind can never see an older value.
fn upward_exposed(block: &Block) -> (BTreeSet<VarId>, BTreeSet<VarId>) {
    let mut walk = UpwardExposed {
        bound: BTreeSet::new(),
        exposed: BTreeSet::new(),
    };
    walk.visit_block(block);
    (walk.exposed, walk.bound)
}

struct UpwardExposed {
    bound: BTreeSet<VarId>,
    exposed: BTreeSet<VarId>,
}

impl Visitor for UpwardExposed {
    /// `walk_*_default` calls this on every var slot it reaches. Binders are
    /// intercepted by the overrides below, so everything that arrives here
    /// is a read.
    fn visit_var(&mut self, v: &VarId) {
        if !self.bound.contains(v) {
            self.exposed.insert(v.clone());
        }
    }

    fn visit_stmt(&mut self, s: &Stmt) {
        match s {
            Stmt::Let { pattern, value } => {
                self.visit_expr(value);
                for p in pattern.iter().flatten() {
                    self.bound.insert(p.clone());
                }
            }
            Stmt::Eval(e) => self.visit_expr(e),
        }
    }

    fn visit_expr(&mut self, e: &Expr) {
        match e {
            Expr::If {
                cond,
                then_branch,
                else_branch,
            } => {
                self.visit_expr(cond);
                let entry = self.bound.clone();
                self.visit_block(then_branch);
                let after_then = std::mem::replace(&mut self.bound, entry);
                self.visit_block(else_branch);
                self.bound = self.bound.intersection(&after_then).cloned().collect();
            }
            Expr::Match {
                selector, cases, ..
            } => {
                self.visit_expr(selector);
                let entry = std::mem::take(&mut self.bound);
                let mut merged: Option<BTreeSet<VarId>> = None;
                for arm in cases {
                    self.bound = entry.clone();
                    for b in &arm.bindings {
                        self.bound.insert(b.clone());
                    }
                    self.visit_block(&arm.body);
                    merged = Some(match merged {
                        None => std::mem::take(&mut self.bound),
                        Some(m) => m.intersection(&self.bound).cloned().collect(),
                    });
                }
                self.bound = merged.unwrap_or(entry);
            }
            Expr::While {
                header, cond, body, ..
            } => {
                // A nested loop's header runs once on entry, so its binds
                // hold afterwards; its body may run zero times. `iter_locals`
                // are empty in the single-pass flow and are not descended.
                self.visit_block(header);
                self.visit_expr(cond);
                let entry = self.bound.clone();
                self.visit_block(body);
                self.bound = entry;
            }
            Expr::LabeledBlock { body, .. } => {
                // A `ReturnFromBlock` can skip the rest of the block, so
                // nothing it binds is guaranteed.
                let entry = self.bound.clone();
                self.visit_block(body);
                self.bound = entry;
            }
            Expr::Quantifier { binder, .. } => {
                let entry = self.bound.clone();
                self.bound.insert(binder.clone());
                walk_expr_default(self, e);
                self.bound = entry;
            }
            _ => walk_expr_default(self, e),
        }
    }
}

/// Normalize the body's outermost tail to the implicit-continue
/// shape `BlockTail::Value(V)`. Two input shapes converge:
///
/// - `BlockTail::Continue { level: 0, value: V }`: `rewrite_tail`
///   already installed the loop_state Tuple in `value` (via
///   `rewrite_loop_jump_value`). We collapse to `BlockTail::Value(V)`.
///
/// - `BlockTail::Value(Expr::Unit)`: stage 2's `lift_region` uniform
///   fall-through. `rewrite_tail` left Unit untouched; we install the
///   loop_state Tuple here, mirroring what `rewrite_loop_jump_value`
///   would have done.
///
/// Inner `Continue`s (inside `If` / `Match` arms inside the body)
/// stay explicit -- they're not at the body's outermost tail.
fn normalize_body_tail(body: Block, iter_local_names: &[VarId]) -> Block {
    let tail = match body.tail {
        BlockTail::Continue { level: 0, value } => BlockTail::Value(*value),
        BlockTail::Value(Expr::Unit) if !iter_local_names.is_empty() => {
            let elems: Vec<Expr> = iter_local_names
                .iter()
                .map(|v| Expr::Var(v.clone()))
                .collect();
            BlockTail::Value(tuple_or_single(elems))
        }
        other => other,
    };
    Block {
        stmts: body.stmts,
        tail,
    }
}

/// Rewrite a `While` appearing at the top of a statement's value
/// position. Handles loop_state synthesis, iteration-local SSA
/// allocation, post-loop name allocation, and the surrounding stmt
/// shape.
fn rewrite_while_at_stmt(
    surrounding_pattern: Option<&Vec<Option<VarId>>>,
    header: &Block,
    cond: &Expr,
    body: &Block,
    post_stmts: &[Stmt],
    post_tail: &BlockTail,
    ctx: &mut Ctx,
) -> Result<Stmt, Stage5Error> {
    let loop_state = compute_loop_state(header, cond, body, post_stmts, post_tail, &ctx.scope);

    // Defensive: every `loop_state` var must already be bound in
    // outer scope. The init expression for each iter_local is
    // `Var(outer_scope[v])`, so an unbound `v` would produce an
    // ill-formed init expression. Reject regardless of whether `v`
    // is referenced post-loop -- the failure mode is the same.
    let uninit_vars: Vec<VarId> = loop_state
        .iter()
        .filter(|v| !ctx.scope.contains_key(*v))
        .cloned()
        .collect();
    // A loop_state var with no pre-loop value is bound late in the body
    // and referenced across the back-edge (header writeback) or as a
    // post-loop value -- e.g. a World dynamic-field store key/value
    // borrowed inside the loop in cetus MoveSTL `skip_list::insert`.
    // Thread it with a typed `default` init (see the iter_locals loop
    // below) instead of rejecting.
    //
    // Soundness: in VALID Move a body-bound var can only be read after
    // the loop (or carried across the back-edge for the next iteration's
    // writeback) if the loop runs at least once on that path -- Move's
    // definite-initialization check forbids observing it otherwise. So
    // the iteration-0 default is overwritten before it can be observed.
    // We keep the defensive reject ONLY when the var's type can't be
    // recovered (the `Const::Default` init would otherwise be
    // ill-formed); that also preserves the reject for genuinely
    // malformed hand-built IR whose late binding isn't typeable.
    if !uninit_vars.is_empty() {
        let untyped: Vec<VarId> = uninit_vars
            .iter()
            .filter(|v| !ctx.var_types.contains_key(*v))
            .cloned()
            .collect();
        if !untyped.is_empty() {
            return Err(Stage5Error::UninitFromZeroIterLoop {
                function: ctx.function,
                vars: untyped,
            });
        }
    }

    let saved_outer = ctx.scope.clone();

    // For each loop_state var: capture its pre-loop SSA name (from
    // outer scope) as the init expression, then allocate a fresh
    // iteration-local name and bind it for header / cond / body.
    // The iteration-local is "this iteration's view" of the
    // loop_state -- in scope throughout header re-eval, cond
    // evaluation, and body. Stage 7 will turn each (iter_local,
    // init) pair into a recursive `LoopBody` helper param plus the
    // initial Call argument.
    let mut iter_locals_emitted: Vec<(VarId, Expr)> = Vec::with_capacity(loop_state.len());
    for v in &loop_state {
        // Init value the first iteration's iter_local takes. A normal
        // loop_state var uses its pre-loop SSA name. A loop-carried var
        // with no pre-loop value (filtered to be type-known above) uses
        // a typed `default` -- only ever reached on a guarded iter-0
        // header path, so never observed.
        let init = match ctx.scope.get(v).cloned() {
            Some(pre_loop) => Expr::Var(pre_loop),
            None => {
                let ty = ctx
                    .var_types
                    .get(v)
                    .cloned()
                    .expect("uninit loop_state var must be type-known (checked above)");
                Expr::Const(Const::Default(ty))
            }
        };
        let iter_local = ctx.fresh(v);
        ctx.bind(v.clone(), iter_local.clone());
        iter_locals_emitted.push((iter_local, init));
    }

    // Push the loop frame BEFORE walking the header. A structured
    // loop header can itself carry `Continue { level: 0 }` (e.g.
    // `if cond { ...; continue }` skip-to-next-iteration in
    // `binary_search`); `rewrite_loop_jump_value` needs `loop_at(0)`
    // to resolve to THIS loop so the carried value is rewritten to
    // the loop_state tuple. Walking the header without the frame left
    // header continues carrying `Unit`, which stage 7 then could not
    // lower (rendered `sorry`).
    ctx.push_loop(LoopFrame {
        loop_state: loop_state.clone(),
    });
    // Walk header with iter_local visible. Header may bind further
    // vars (its own bindings are iteration-scoped, not loop_state).
    let new_header = rewrite_block(header, ctx)?;
    // Walk cond with header bindings + iter_local visible.
    let new_cond = rewrite_expr(cond, ctx)?;

    // The cond-false edge exits after the header has executed. Preserve the
    // newest SSA name for every carried slot at exactly that point. Stage 7
    // must pass these values to LoopAfter; using the iter-local parameter
    // names would discard mutations performed by the header (notably the
    // Scenario and World updates in test_scenario::next_with_context).
    let header_exit_locals: Vec<VarId> = loop_state
        .iter()
        .map(|v| ctx.lookup(v))
        .collect::<Result<Vec<_>, _>>()?;

    // ---- Live-out capture (exit-point scope = post-header) --------
    // Vars referenced AFTER the loop that are bound inside the loop
    // (header) but are NOT loop-carried (`loop_state`) and NOT from
    // the pre-loop outer scope. Their final-iteration value escapes.
    // We capture each one's current in-loop SSA name HERE: at the
    // cond-false exit, header bindings are live and the body has not
    // run. Stage 7 threads these into the `.after` helper under a
    // fresh post-loop name (allocated below). Without this, post-loop
    // references to header-internal names made stage 5 bail (the
    // `binary_search` mid_obs/next_obs bug).
    let loop_state_set: BTreeSet<VarId> = loop_state.iter().cloned().collect();
    let mut post_refs: BTreeSet<VarId> = BTreeSet::new();
    for s in post_stmts {
        collect_refs_stmt(s, &mut post_refs);
    }
    collect_refs_tail(post_tail, &mut post_refs);
    let mut live_out_srcs: Vec<VarId> = Vec::new();
    let mut live_out_in_loop: Vec<VarId> = Vec::new();
    for v in &post_refs {
        if loop_state_set.contains(v) || saved_outer.contains_key(v) {
            continue;
        }
        if let Some(in_loop_name) = ctx.scope.get(v) {
            live_out_srcs.push(v.clone());
            live_out_in_loop.push(in_loop_name.clone());
        }
    }

    let mut new_body = rewrite_block(body, ctx)?;

    // While iter_locals are still in scope, look up the CURRENT SSA
    // name for each loop_state source-name. These names reflect any
    // assignments inside the body (e.g. `t_4_1 := t_4_1 << 1` updates
    // the SSA name for source-name `t_4`); using the iter_local
    // binders directly would carry the pre-assignment names, which is
    // wrong. `rewrite_loop_jump_value` does the same lookup for
    // explicit `Continue { level: 0 }` tails; we do it here for the
    // implicit-continue case where the body's outermost tail is
    // `Value(Unit)` (stage 2's uniform fall-through).
    let body_tail_state: Vec<VarId> = loop_state
        .iter()
        .map(|v| ctx.lookup(v))
        .collect::<Result<Vec<_>, _>>()?;

    ctx.pop_loop();

    // Restore outer scope before the While. Header-local /
    // iter-local / body-local bindings are gone.
    ctx.scope = saved_outer;

    new_body = normalize_body_tail(new_body, &body_tail_state);

    // Allocate a fresh post-loop name for each live-out var and bind
    // src -> post in the (restored) outer scope so the caller's
    // post-loop walk of `post_stmts` / `post_tail` resolves to a
    // properly-bound name (validator is strictly scoped: header
    // names cannot escape). Pair each post name with the in-loop
    // name captured at the exit point; `live_out` carries
    // (in_loop_name, post_name) for stage 7 to thread into `.after`.
    let mut live_out_emitted: Vec<(VarId, VarId)> = Vec::with_capacity(live_out_srcs.len());
    let mut live_out_posts: Vec<VarId> = Vec::with_capacity(live_out_srcs.len());
    for (src, in_loop_name) in live_out_srcs.iter().zip(live_out_in_loop.iter()) {
        let post = ctx.fresh(src);
        ctx.bind(src.clone(), post.clone());
        live_out_emitted.push((in_loop_name.clone(), post.clone()));
        live_out_posts.push(post);
    }

    let new_while = Expr::While {
        header: Box::new(new_header),
        cond: Box::new(new_cond),
        body: Box::new(new_body),
        iter_locals: iter_locals_emitted,
        header_exit_locals,
        live_out: live_out_emitted,
    };

    // Build the surrounding Stmt. Pattern = (existing pattern slots) +
    // (post-loop fresh names for loop_state).
    let mut new_pattern: Vec<Option<VarId>> = Vec::new();
    if let Some(pat) = surrounding_pattern {
        for slot in pat {
            match slot {
                Some(v) => {
                    let fresh = ctx.fresh(v);
                    ctx.bind(v.clone(), fresh.clone());
                    new_pattern.push(Some(fresh));
                }
                None => new_pattern.push(None),
            }
        }
    }
    for v in &loop_state {
        let post_fresh = ctx.fresh(v);
        ctx.bind(v.clone(), post_fresh.clone());
        new_pattern.push(Some(post_fresh));
    }
    // Live-out post-loop names follow the loop_state post-names.
    // Stage 7 relies on this ordering: the trailing pattern slots
    // beyond `iter_locals.len()` are the live-out `.after` params.
    for post in &live_out_posts {
        new_pattern.push(Some(post.clone()));
    }

    if new_pattern.is_empty() {
        Ok(Stmt::Eval(new_while))
    } else {
        Ok(Stmt::Let {
            pattern: new_pattern,
            value: new_while,
        })
    }
}
