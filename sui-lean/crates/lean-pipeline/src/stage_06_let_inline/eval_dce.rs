//! Sub-pass 2d -- dead-code elimination on `Stmt::Eval`.
//!
//! For every `Stmt::Eval(e)` where `is_pure_total(e, program)`:
//! drop the statement. Pure-and-total expressions have no
//! observable behaviour and produce no value (Eval discards the
//! value anyway), so removing them preserves semantics.
//!
//! `Stmt::Eval(impure_or_partial_e)` is retained -- the evaluation
//! still produces a side effect or abort, even though the value
//! is discarded.

use crate::ir::visit::{walk_block_mut_default, MutVisitor};
use crate::ir::{Block, Program, Stmt};

use super::effects_predicate::is_eval_dce_droppable;

/// Apply Eval-DCE over `body` once. Returns `true` when any
/// `Stmt::Eval` was dropped.
pub fn eval_dce_once(body: &mut Block, program: &Program) -> bool {
    let mut pass = EvalDce {
        program,
        changed: false,
    };
    pass.visit_block_mut(body);
    pass.changed
}

struct EvalDce<'a> {
    program: &'a Program,
    changed: bool,
}

impl MutVisitor for EvalDce<'_> {
    fn visit_block_mut(&mut self, b: &mut Block) {
        // Phase 1: filter out droppable Eval stmts. `is_eval_dce_droppable`
        // is broader than `is_pure_total` -- it sees through Calls to
        // pure-total natives, which `is_pure_total` conservatively
        // rejects to avoid surprising `single_use_inline`.
        let old = std::mem::take(&mut b.stmts);
        let mut new: Vec<Stmt> = Vec::with_capacity(old.len());
        for s in old {
            match &s {
                Stmt::Eval(e) if is_eval_dce_droppable(e, self.program) => {
                    self.changed = true;
                }
                _ => new.push(s),
            }
        }
        b.stmts = new;
        // Phase 2: recurse into nested blocks via the framework walk.
        walk_block_mut_default(self, b);
    }
}
