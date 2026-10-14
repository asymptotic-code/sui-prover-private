//! Sub-pass 2a -- trivial-copy elimination.
//!
//! For every `Stmt::Let { pattern: [Some(v)], value: Var(y) | Const(c) }`:
//! - Substitute `v -> Var(y) | Const(c)` at every downstream use site.
//! - Drop the `Stmt::Let`.
//!
//! Multi-use is OK -- duplicating a `Var` or `Const` is zero-cost.
//! Mutation is safe in a single pass because the substitution
//! happens only at `v`'s use sites, and `y` / the const literal
//! doesn't change semantics if duplicated.
//!
//! Sub-pass 2a runs as part of the stage-6 fixpoint; one call
//! processes the whole body in pre-order, collapsing every trivial
//! copy reachable at the current shape. A long copy chain `let a =
//! x; let b = a; let c = b; use c` collapses one level per fixpoint
//! iteration -- the design doc accepts this; the fixpoint converges
//! quickly.

use crate::ir::visit::{walk_block_mut_default, MutVisitor};
use crate::ir::{Block, Expr, Stmt, VarId};

use super::substitute;
use super::use_count::{count_uses, UseCount};

/// Apply trivial-copy elimination over `body` once. Returns `true`
/// when any `Stmt::Let { value: Var | Const }` was inlined and
/// dropped.
pub fn copy_inline_once(body: &mut Block) -> bool {
    let counts = count_uses(body);
    let mut pass = CopyInline {
        counts: &counts,
        changed: false,
    };
    pass.visit_block_mut(body);
    pass.changed
}

struct CopyInline<'a> {
    counts: &'a UseCount,
    changed: bool,
}

impl MutVisitor for CopyInline<'_> {
    fn visit_block_mut(&mut self, b: &mut Block) {
        // Phase 1: process this block's stmts top-down. Each trivial-copy
        // Let substitutes `v -> repl` into the rest of the block (the
        // substituter descends into nested blocks too).
        let mut i = 0;
        while i < b.stmts.len() {
            if let Some((v, repl)) = inline_candidate(&b.stmts[i], self.counts) {
                for j in (i + 1)..b.stmts.len() {
                    substitute::substitute_var_in_stmt(&mut b.stmts[j], &v, &repl);
                }
                substitute::substitute_var_in_tail(&mut b.tail, &v, &repl);
                b.stmts.remove(i);
                self.changed = true;
                // i stays the same; next stmt slid into position.
            } else {
                i += 1;
            }
        }
        // Phase 2: recurse into nested blocks (If/Match/While/Quantifier/
        // LabeledBlock) via the framework walk.
        walk_block_mut_default(self, b);
    }
}

fn inline_candidate(s: &Stmt, counts: &UseCount) -> Option<(VarId, Expr)> {
    let (pattern, value) = match s {
        Stmt::Let { pattern, value } if pattern.len() == 1 => (pattern, value),
        _ => return None,
    };
    let v = pattern[0].as_ref()?.clone();
    match value {
        Expr::Var(w) if *w == v => {
            // Identity Let `let v = Var(v)` -- shouldn't occur: stage 7's
            // cont_inline drops these self-rebinds at the source. Skip;
            // the postcondition reports any that slip through.
            None
        }
        // A `Var` replacement names a location, so the substituter can
        // rename `v`'s borrow positions (`BorrowLoc(v)` /
        // `WriteBack { child: v, .. }` / ...) var->var. Borrow uses do
        // NOT block a copy.
        Expr::Var(_) => Some((v, value.clone())),
        // A `Const` has no location and can't fill a borrow slot: if `v`
        // appears in a borrow position, dropping the Let would leave it
        // dangling, so refuse.
        Expr::Const(_) => {
            if counts.has_borrow_use(&v) {
                None
            } else {
                Some((v, value.clone()))
            }
        }
        _ => None,
    }
}
