//! Sub-pass 2b -- single-use pure-and-total inlining.
//!
//! For every `Stmt::Let { pattern: [Some(v)], value: e }` where:
//! - `is_pure_total(e, program)` (no side effects, cannot abort), AND
//! - `use_count(v) == 1` (`v` is referenced exactly once),
//!
//! ...substitute `v -> e` at the unique use site and drop the Let.
//!
//! ## Count stability across inlines
//!
//! Inlining a single-use pure-and-total Let does NOT change the use
//! count of any other var. Proof sketch: before the inline, every
//! `Var(w)` reference in `e` contributes to `count(w)` (because `e`
//! is the value of `let v = e`, which the walker counts). After
//! substitution, `e` lives at `v`'s old use site -- the same
//! `Var(w)` references exist, contributing the same amount. Dropping
//! the Let removes `e` from its old position (no net effect; the
//! references moved, not duplicated). So `count(w)` is invariant.
//!
//! This means one `count_uses()` snapshot is valid for an entire
//! pass; we don't need to recompute between inlines.

use crate::ir::visit::{walk_block_mut_default, MutVisitor};
use crate::ir::{Block, Expr, Program, Stmt, VarId};

use super::effects_predicate::is_pure_total;
use super::substitute;
use super::use_count::{count_uses, UseCount};

/// Apply single-use pure-and-total inlining over `body` once.
/// Returns `true` when any `Stmt::Let` was inlined and dropped.
pub fn single_use_inline_once(body: &mut Block, program: &Program) -> bool {
    let counts = count_uses(body);
    let mut pass = SingleUse {
        counts: &counts,
        program,
        changed: false,
    };
    pass.visit_block_mut(body);
    pass.changed
}

struct SingleUse<'a> {
    counts: &'a UseCount,
    program: &'a Program,
    changed: bool,
}

impl MutVisitor for SingleUse<'_> {
    fn visit_block_mut(&mut self, b: &mut Block) {
        // Phase 1: top-level inlines in this block. The substituter
        // descends into nested blocks, so the unique use site is
        // rewritten wherever it lives.
        let mut i = 0;
        while i < b.stmts.len() {
            if let Some((v, repl)) = inline_candidate(&b.stmts[i], self.counts, self.program) {
                for j in (i + 1)..b.stmts.len() {
                    substitute::substitute_var_in_stmt(&mut b.stmts[j], &v, &repl);
                }
                substitute::substitute_var_in_tail(&mut b.tail, &v, &repl);
                b.stmts.remove(i);
                self.changed = true;
                // i stays; next stmt slid into position.
            } else {
                i += 1;
            }
        }
        // Phase 2: recurse into nested blocks via the framework walk.
        walk_block_mut_default(self, b);
    }
}

fn inline_candidate(s: &Stmt, counts: &UseCount, program: &Program) -> Option<(VarId, Expr)> {
    let (pattern, value) = match s {
        Stmt::Let { pattern, value } if pattern.len() == 1 => (pattern, value),
        _ => return None,
    };
    let v = pattern[0].as_ref()?.clone();
    if counts.get(&v) != 1 {
        return None;
    }
    // Refuse to inline if `v` is referenced in a non-substitutable
    // position (`BorrowLoc(v)` / `WriteBack { child: v, .. }`):
    // the substituter can't rewrite those slots, so dropping the
    // Let would leave the reference dangling. Stage 6's input
    // shouldn't contain these outside pattern-4b tails; this guards
    // a future stage-4 regression.
    if counts.has_borrow_use(&v) {
        return None;
    }
    if !is_pure_total(value, program) {
        return None;
    }
    // Defensive: skip Var/Const values -- those are sub-pass 2a's
    // job and may have multi-use. Single_use is for the cases 2a
    // doesn't cover (Field, Pack, pure-total Calls, ...).
    if matches!(value, Expr::Var(_) | Expr::Const(_)) {
        return None;
    }
    Some((v, value.clone()))
}
