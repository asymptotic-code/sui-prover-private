//! Per-function use-count walker.
//!
//! Counts `Expr::Var(_)` references within a `Block`, with two
//! shadowing rules baked in:
//!
//! - `Expr::Quantifier::binder` shadows outer-scope vars of the same
//!   name for the lifetime of `Quantifier::body`. References in the
//!   `Quantifier::domain` are NOT shadowed (the bound variable is
//!   not in scope there).
//! - `MatchArm::bindings` shadow outer-scope vars of the same name
//!   for the lifetime of the arm body.
//!
//! `Stmt::Let::pattern` positions are NOT counted -- they are defs,
//! not uses. The walker visits every right-hand-side `value` and
//! every `Block::tail` payload (including the `value` of
//! `BlockTail::Break / Continue / Return / Abort`).
//!
//! See `plans/lean-pipeline/stage-06-let-inline.md` decision-log
//! §12 for the use-count contract.

use std::collections::{BTreeMap, BTreeSet};

use crate::ir::{
    quant::QuantDomain,
    visit::{walk_block_default, walk_expr_default, walk_stmt_default, walk_tail_default, Visitor},
    Block, Expr, MatchArm, VarId,
};

/// Per-function use counts.
///
/// Tracks two kinds of references separately:
///
/// - `counts` -- references at substitutable positions, i.e. every
///   `Expr::Var(v)` that the walker encounters. `get(v)` returns
///   this count.
/// - `borrow_uses` -- references at non-substitutable positions:
///   `Expr::BorrowLoc(v)` and `Expr::WriteBack { child: v, .. }`.
///   These carry a `VarId` slot that takes a name, not an
///   expression -- the stage-6 substituter cannot rewrite them when
///   the replacement is non-Var. `has_borrow_use(v)` returns whether
///   any exist.
///
/// Sub-passes that drop a Let must check BOTH: only inline (or
/// wildcard-collapse the pattern) when `get(v) == 1` (or 0) AND
/// `!has_borrow_use(v)`. Otherwise the Let drops with the
/// `BorrowLoc(v)` / `WriteBack { child: v }` dangling -- the base
/// validator would reject the resulting program, but the failure
/// would surface as a base-validator `UnboundVariable` rather than
/// a clean stage-6 invariant violation.
///
/// In well-formed stage-6 input (post-stage-4), BorrowLoc and
/// WriteBack only appear in pattern-4b function tails; this
/// defensive split exists so a future stage-4 regression doesn't
/// produce silent corruption.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct UseCount {
    counts: BTreeMap<VarId, u32>,
    borrow_uses: std::collections::BTreeSet<VarId>,
}

impl UseCount {
    /// Substitutable-use count: number of `Expr::Var(v)` references
    /// in the walked body. Returns `0` if `v` has no such reference.
    pub fn get(&self, v: &VarId) -> u32 {
        self.counts.get(v).copied().unwrap_or(0)
    }

    /// Whether `v` appears in any non-substitutable position
    /// (`Expr::BorrowLoc(v)` or `Expr::WriteBack { child: v, .. }`).
    /// Sub-passes refuse to inline / drop Lets where this returns
    /// `true`.
    pub fn has_borrow_use(&self, v: &VarId) -> bool {
        self.borrow_uses.contains(v)
    }

    /// Total number of distinct vars with at least one substitutable
    /// reference. Sanity-check helper for tests.
    pub fn distinct_referenced(&self) -> usize {
        self.counts.len()
    }

    /// Borrow the substitutable-use map.
    pub fn as_map(&self) -> &BTreeMap<VarId, u32> {
        &self.counts
    }
}

/// Build a `UseCount` over `body`. Top-level entry point used by every
/// stage-6 sub-pass.
pub fn count_uses(body: &Block) -> UseCount {
    let mut walker = UseCountWalker::default();
    walker.visit_block(body);
    walker.into_use_count()
}

/// Internal walker; carries the shadowing stack alongside the counts.
#[derive(Default)]
struct UseCountWalker {
    counts: BTreeMap<VarId, u32>,
    borrow_uses: BTreeSet<VarId>,
    /// Stack of shadowing scopes. Each entry is the set of names
    /// bound by an enclosing `Quantifier::binder`,
    /// `MatchArm::bindings`, or `Expr::While::iter_locals`.
    /// References to a shadowed name do not count toward the outer
    /// var of the same name.
    shadowed: Vec<BTreeSet<VarId>>,
}

impl UseCountWalker {
    fn into_use_count(self) -> UseCount {
        UseCount {
            counts: self.counts,
            borrow_uses: self.borrow_uses,
        }
    }

    fn is_shadowed(&self, v: &VarId) -> bool {
        self.shadowed.iter().any(|scope| scope.contains(v))
    }

    fn bump(&mut self, v: &VarId) {
        if self.is_shadowed(v) {
            return;
        }
        *self.counts.entry(v.clone()).or_insert(0) += 1;
    }

    fn mark_borrow_use(&mut self, v: &VarId) {
        if self.is_shadowed(v) {
            return;
        }
        self.borrow_uses.insert(v.clone());
    }

    /// Mark the `VarId` carried by `BorrowNode::LocalRoot(v)` or
    /// `BorrowNode::Reference(v)` as a borrow-use. `SpecGlobalRoot`
    /// carries no VarId.
    fn mark_borrow_node_use(&mut self, node: &crate::ir::BorrowNode) {
        match node {
            crate::ir::BorrowNode::LocalRoot(v) | crate::ir::BorrowNode::Reference(v) => {
                self.mark_borrow_use(v);
            }
            crate::ir::BorrowNode::GlobalRoot(_) | crate::ir::BorrowNode::SpecGlobalRoot { .. } => {}
        }
    }

    fn with_scope<F>(&mut self, binders: BTreeSet<VarId>, f: F)
    where
        F: FnOnce(&mut Self),
    {
        self.shadowed.push(binders);
        f(self);
        self.shadowed.pop();
    }
}

impl Visitor for UseCountWalker {
    fn visit_block(&mut self, b: &Block) {
        walk_block_default(self, b);
    }

    fn visit_stmt(&mut self, s: &crate::ir::Stmt) {
        // `Stmt::Let::pattern` positions are defs, not uses; the
        // default walker only visits the `value`. `Stmt::Eval`'s
        // expression is fully visited.
        walk_stmt_default(self, s);
    }

    fn visit_tail(&mut self, t: &crate::ir::BlockTail) {
        // Default visits the wrapped expression for every variant.
        walk_tail_default(self, t);
    }

    fn visit_expr(&mut self, e: &Expr) {
        match e {
            Expr::Var(v) => self.bump(v),
            // BorrowLoc(v) and WriteBack { child: v, .. } carry a
            // `v: VarId` slot that names a variable but does not
            // accept a substitution (the slot is a name, not an
            // expression). The walker records these as
            // non-substitutable "borrow uses" so sub-passes refuse
            // to inline / wildcard-drop the var.
            Expr::BorrowLoc(v) => self.mark_borrow_use(v),
            // WriteBack and IsParent carry a VarId in BOTH `child` and
            // (when `node` is `LocalRoot(v)` or `Reference(v)`) inside
            // `node`. Both are non-substitutable name positions -- sub-
            // passes that drop the binding would leave a dangling
            // reference in the rendered output. Mark both as borrow
            // uses so sub-passes refuse to inline / wildcard-collapse
            // either var.
            // The WriteRef bridge (stage-4 writeback lowering) names
            // its rebound parent in `reference`; treat a Var there as
            // a borrow-use so sub-passes keep the same inlining
            // constraints the WriteBack node imposed before lowering
            // (inlining a Mutation-returning call into the reference
            // slot breaks the renderer's .val/ofLocal decisions).
            Expr::WriteRef { reference, value } => {
                if let Expr::Var(r) = reference.as_ref() {
                    self.mark_borrow_use(r);
                } else {
                    self.visit_expr(reference);
                }
                self.visit_expr(value);
            }
            Expr::WriteBack {
                node, child, world, ..
            } => {
                self.mark_borrow_use(child);
                self.mark_borrow_node_use(node);
                // DF writeback world input: a non-substitutable name slot.
                if let Some(v) = world {
                    self.mark_borrow_use(v);
                }
            }
            Expr::IsParent { node, child, .. } => {
                self.mark_borrow_use(child);
                self.mark_borrow_node_use(node);
            }
            // `df_value` is a non-substitutable name slot (the renderer
            // emits `fun _ _ => df_value`; inlining a world-threaded read
            // into that closure would re-execute it). Count base/key as
            // usual and mark df_value as a borrow use so DCE keeps its
            // binding.
            // Same name-slot rule for the unified `Borrow` form: a
            // MapKey step's `df_value` is non-substitutable (the
            // renderer emits `fun _ _ => df_value`), so mark it a
            // borrow use; base and the step operands count as usual.
            Expr::Borrow { step, base } => {
                self.visit_expr(base);
                for op in step.exprs() {
                    self.visit_expr(op);
                }
                if let crate::ir::path::PathStep::MapKey {
                    df_value: Some(v), ..
                } = step
                {
                    self.mark_borrow_use(v);
                }
            }
            Expr::Quantifier {
                binder,
                domain,
                body,
                ..
            } => {
                // The domain is evaluated in outer scope -- the
                // binder is NOT in scope there.
                match domain {
                    QuantDomain::Unbounded => {}
                    QuantDomain::Range { start, end } => {
                        self.visit_expr(start);
                        self.visit_expr(end);
                    }
                    QuantDomain::Collection(c) => self.visit_expr(c),
                    QuantDomain::VecRange { vec, start, end } => {
                        self.visit_expr(vec);
                        self.visit_expr(start);
                        self.visit_expr(end);
                    }
                }
                // The binder shadows for the body only.
                let mut scope = BTreeSet::new();
                scope.insert(binder.clone());
                self.with_scope(scope, |w| w.visit_block(body));
            }
            Expr::While {
                header,
                cond,
                body,
                iter_locals,
                header_exit_locals: _,
                live_out: _,
            } => {
                // `iter_locals` are `(binder, init)` pairs. The
                // `init` expressions evaluate ONCE in the outer
                // scope at loop entry (before the binder is bound) --
                // walk them with no shadowing.
                for (_, init) in iter_locals {
                    self.visit_expr(init);
                }
                // The binders shadow outer-scope vars for the
                // entirety of `header`, `cond`, and `body`.
                let scope: BTreeSet<VarId> = iter_locals.iter().map(|(b, _)| b.clone()).collect();
                self.with_scope(scope, |w| {
                    w.visit_block(header);
                    w.visit_expr(cond);
                    w.visit_block(body);
                });
            }
            _ => walk_expr_default(self, e),
        }
    }

    fn visit_match_arm(&mut self, arm: &MatchArm) {
        // Arm-local bindings shadow outer-scope vars of the same
        // name for the lifetime of the arm body.
        let scope: BTreeSet<VarId> = arm.bindings.iter().cloned().collect();
        self.with_scope(scope, |w| w.visit_block(&arm.body));
    }
}
