//! Pre-pass: literal-tuple destructure splitting.
//!
//! For every `Stmt::Let { pattern: [p0, p1, ...], value: Expr::Tuple([e0, e1, ...]) }`
//! where `pattern.len() == elems.len()` AND every `e_i` is
//! pure-and-total, split the single multi-binding Let into one Let
//! per position. Wildcard pattern positions (`None`) drop their
//! element entirely (since `e_i` is pure-total).
//!
//! This exposes each `e_i` to sub-passes 2a and 2b individually,
//! which otherwise would be unable to inline `e_i` (the wrapping
//! Tuple-Let blocks per-position substitution).
//!
//! Runs ONCE before the fixpoint per the design-doc decision-log §10
//! (splitting inside the fixpoint risks oscillation with 2c's
//! wildcard collapse).

use crate::ir::visit::{walk_block_mut_default, MutVisitor};
use crate::ir::{Block, Expr, Program, Stmt};

use super::effects_predicate::is_pure_total;

/// Apply tuple-literal splitting over `body`. Returns `true` when
/// any `Stmt::Let` was split. The caller typically runs this once
/// before the stage-6 fixpoint.
pub fn split_tuple_literals(body: &mut Block, program: &Program) -> bool {
    let mut pass = TupleSplit {
        program,
        changed: false,
    };
    pass.visit_block_mut(body);
    pass.changed
}

struct TupleSplit<'a> {
    program: &'a Program,
    changed: bool,
}

impl MutVisitor for TupleSplit<'_> {
    fn visit_block_mut(&mut self, b: &mut Block) {
        // Phase 1: split qualifying multi-binding tuple-literal Lets.
        let old = std::mem::take(&mut b.stmts);
        let mut new: Vec<Stmt> = Vec::with_capacity(old.len());
        for s in old {
            match try_split(&s, self.program) {
                Some(split) => {
                    new.extend(split);
                    self.changed = true;
                }
                None => new.push(s),
            }
        }
        b.stmts = new;
        // Phase 2: recurse into nested blocks via the framework walk.
        walk_block_mut_default(self, b);
    }
}

fn try_split(s: &Stmt, program: &Program) -> Option<Vec<Stmt>> {
    let (pattern, value) = match s {
        Stmt::Let { pattern, value } => (pattern, value),
        _ => return None,
    };
    if pattern.len() < 2 {
        return None;
    }
    let elems = match value {
        Expr::Tuple(elems) => elems,
        _ => return None,
    };
    if pattern.len() != elems.len() {
        return None;
    }
    // Every element must be pure-and-total -- splitting reorders
    // evaluation (each element binds independently); preserving
    // semantics requires the elements be side-effect-free and
    // non-aborting.
    if !elems.iter().all(|e| is_pure_total(e, program)) {
        return None;
    }

    let mut result = Vec::with_capacity(pattern.len());
    for (pat, e) in pattern.iter().zip(elems.iter()) {
        match pat {
            Some(v) => {
                result.push(Stmt::Let {
                    pattern: vec![Some(v.clone())],
                    value: e.clone(),
                });
            }
            None => {
                // Wildcard position with a pure-total element: drop
                // entirely (DCE). A per-position `let _ = e_i` would
                // be a fully-wildcard single-position Let, which the
                // IR validator rejects; dropping preserves observable
                // behaviour because `e_i` is pure-total.
            }
        }
    }
    Some(result)
}
