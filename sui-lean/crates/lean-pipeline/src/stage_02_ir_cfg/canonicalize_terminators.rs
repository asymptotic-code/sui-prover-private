//! Post-lift canonicalization: hoist terminating-arm `If` / `Match`
//! expressions into the surrounding `Block`'s tail position.
//!
//! `lift_region` emits `If` / `Match` / `While` uniformly as
//! `Block { stmts: [Stmt::Eval(expr)], tail: Value(Unit) }` --
//! whether or not the arms terminate. That's the correct, minimal
//! lift contract: per-region translation without analyzing arm
//! termination. The canonicalization step here recognizes when a
//! `Stmt::Eval(if_expr)` is itself a terminator (every arm's lifted
//! `Block` has a non-`Value(Unit)` tail) and rewrites the enclosing
//! block:
//!
//! ```text
//! Block {
//!     stmts: [..., Stmt::Eval(if_expr), ...dead-stmts...],
//!     tail: ...dead-tail...,
//! }
//! ```
//!
//! becomes:
//!
//! ```text
//! Block {
//!     stmts: [...],          // everything before the Stmt::Eval
//!     tail: Value(if_expr),
//! }
//! ```
//!
//! The discarded trailing stmts + tail are dead because every arm of
//! the lifted If/Match transfers control before reaching them.
//!
//! The pass is recursive (walks every nested `Block` -- If arms,
//! Match arms, While headers/bodies) and reaches a fixed point in a
//! single forward sweep because each rewrite turns the enclosing
//! block's tail into a `Value(Expr::If|Match)`, which then propagates
//! the "terminator" status outward on the next ancestor's check.
//!
//! Without this pass:
//! - `rand_level`'s outer `if (level > list.level)` whose arms each
//!   `break`/`continue` would render as `let _ := if ... else ...;
//!   while_0(...)` -- the breaks become discarded side-effect calls
//!   and the synthetic `Continue{0}` (stamped by `lift_while`) forces
//!   an unconditional re-iter on every loop pass.
//! - `swap_or_fill.aborts` and friends would carry render-time
//!   `binop-operand-types-agree` violations from the trailing dead
//!   tail surviving past stage 7.

use crate::ir::visit::{walk_block_mut_default, MutVisitor};
use crate::ir::{Block, BlockTail, Expr, Stmt};

/// Returns `true` iff `block.tail` is anything but `Value(Unit)`.
/// `Value(Unit)` is the canonical "this block falls off the end"
/// marker; anything else is a terminator (explicit `Break`/
/// `Continue`/`Return`/`Abort`, or a `Value(non-Unit)` carrying a
/// nested terminator-If).
fn terminates(block: &Block) -> bool {
    !matches!(&block.tail, BlockTail::Value(Expr::Unit))
}

/// Returns `true` iff every arm of the given `Expr::If` /
/// `Expr::Match` has a terminating tail. Returns `false` for any
/// other `Expr` variant (defensive -- callers should only pass
/// `Stmt::Eval(If|Match)` payloads).
fn expr_terminates_via_arms(e: &Expr) -> bool {
    match e {
        Expr::If {
            then_branch,
            else_branch,
            ..
        } => terminates(then_branch) && terminates(else_branch),
        Expr::Match { cases, .. } => !cases.is_empty() && cases.iter().all(|c| terminates(&c.body)),
        _ => false,
    }
}

/// Canonicalize `block` in place. Walks every nested Block first
/// (post-order, so children are canonical before we make decisions
/// about the parent), then scans the parent's `stmts` for the
/// earliest `Stmt::Eval(if|match)` whose arms all terminate. If one
/// is found, truncate `stmts` to before that index and replace
/// `block.tail` with `Value(if|match)`.
pub fn canonicalize(block: &mut Block) {
    Canonicalizer.visit_block_mut(block);
}

struct Canonicalizer;

impl MutVisitor for Canonicalizer {
    fn visit_block_mut(&mut self, b: &mut Block) {
        // 1) Recurse into every nested Block first (post-order: children
        //    are canonical before we scan the parent). The default walk
        //    descends into If/Match/While/Quantifier/LabeledBlock bodies,
        //    invoking this same override on each.
        walk_block_mut_default(self, b);

        // 2) Scan this block's stmts for the earliest terminating
        //    Stmt::Eval(if|match); if found, truncate to before it and
        //    hoist it into the tail (discarding the dead trailing stmts
        //    + old tail).
        let cut = b.stmts.iter().position(|s| match s {
            Stmt::Eval(e) => expr_terminates_via_arms(e),
            _ => false,
        });
        if let Some(idx) = cut {
            let mut tail_stmt = b.stmts.split_off(idx);
            // `tail_stmt[0]` is the Stmt::Eval(if|match); rest are dead.
            let Stmt::Eval(e) = tail_stmt.remove(0) else {
                // Unreachable by the `position` predicate.
                return;
            };
            b.tail = BlockTail::Value(e);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::MatchArm;

    fn unit_block() -> Block {
        Block {
            stmts: Vec::new(),
            tail: BlockTail::Value(Expr::Unit),
        }
    }

    fn break_block(level: u32) -> Block {
        Block {
            stmts: Vec::new(),
            tail: BlockTail::Break {
                level,
                value: Box::new(Expr::Unit),
            },
        }
    }

    fn continue_block(level: u32) -> Block {
        Block {
            stmts: Vec::new(),
            tail: BlockTail::Continue {
                level,
                value: Box::new(Expr::Unit),
            },
        }
    }

    fn if_expr(then_blk: Block, else_blk: Block) -> Expr {
        Expr::If {
            cond: Box::new(Expr::Var("c".into())),
            then_branch: Box::new(then_blk),
            else_branch: Box::new(else_blk),
        }
    }

    #[test]
    fn terminates_false_for_value_unit() {
        assert!(!terminates(&unit_block()));
    }

    #[test]
    fn terminates_true_for_break() {
        assert!(terminates(&break_block(0)));
    }

    #[test]
    fn expr_terminates_via_arms_true_for_break_continue() {
        let e = if_expr(break_block(0), continue_block(0));
        assert!(expr_terminates_via_arms(&e));
    }

    #[test]
    fn expr_terminates_via_arms_false_if_one_arm_falls_through() {
        let e = if_expr(unit_block(), break_block(0));
        assert!(!expr_terminates_via_arms(&e));
    }

    #[test]
    fn canonicalize_hoists_terminating_if_to_tail() {
        // Block { stmts: [Stmt::Eval(if{break, continue})], tail: Value(Unit) }
        // ->
        // Block { stmts: [], tail: Value(if{break, continue}) }
        let mut b = Block {
            stmts: vec![Stmt::Eval(if_expr(break_block(0), continue_block(0)))],
            tail: BlockTail::Value(Expr::Unit),
        };
        canonicalize(&mut b);
        assert!(b.stmts.is_empty());
        match b.tail {
            BlockTail::Value(Expr::If { .. }) => {}
            other => panic!("expected Value(If), got {other:?}"),
        }
    }

    #[test]
    fn canonicalize_drops_dead_trailing_continue_tail() {
        // Simulates lift_while's stamped Continue{0} after the
        // terminating-arm If: that Continue is dead.
        let mut b = Block {
            stmts: vec![Stmt::Eval(if_expr(break_block(0), continue_block(0)))],
            tail: BlockTail::Continue {
                level: 0,
                value: Box::new(Expr::Unit),
            },
        };
        canonicalize(&mut b);
        // The dead Continue{0} tail is overwritten by Value(If).
        match b.tail {
            BlockTail::Value(Expr::If { .. }) => {}
            other => panic!("expected Value(If), got {other:?}"),
        }
    }

    #[test]
    fn canonicalize_preserves_non_terminating_if() {
        // Block { stmts: [Stmt::Eval(if{unit, unit})], tail: Value(Unit) }
        // should NOT be touched -- the If's arms both fall through.
        let mut b = Block {
            stmts: vec![Stmt::Eval(if_expr(unit_block(), unit_block()))],
            tail: BlockTail::Value(Expr::Unit),
        };
        let snapshot = b.clone();
        canonicalize(&mut b);
        assert_eq!(b, snapshot);
    }

    #[test]
    fn canonicalize_recurses_into_nested_if_arms() {
        // Outer If's then-arm contains a Stmt::Eval(InnerIf{break, break})
        // followed by a Value(Unit) tail. Inner arms terminate, so
        // the InnerIf should hoist to the then-arm's tail. After that,
        // the OUTER If's then-arm.tail = Value(InnerIf) -- non-Value(Unit) --
        // and combined with else-arm.tail = Continue{0}, the OUTER If
        // also terminates and should hoist into the surrounding tail.
        let inner = if_expr(break_block(0), break_block(0));
        let outer_then = Block {
            stmts: vec![Stmt::Eval(inner)],
            tail: BlockTail::Value(Expr::Unit),
        };
        let outer_else = continue_block(0);
        let outer = if_expr(outer_then, outer_else);

        let mut b = Block {
            stmts: vec![Stmt::Eval(outer)],
            tail: BlockTail::Continue {
                level: 0,
                value: Box::new(Expr::Unit),
            },
        };
        canonicalize(&mut b);

        // Top-level: outer If hoisted to tail.
        let outer_e = match &b.tail {
            BlockTail::Value(e @ Expr::If { .. }) => e,
            other => panic!("expected Value(If) at top, got {other:?}"),
        };
        // Inner If hoisted inside the outer's then-arm.
        let Expr::If { then_branch, .. } = outer_e else {
            unreachable!();
        };
        assert!(
            then_branch.stmts.is_empty(),
            "inner hoist should empty stmts"
        );
        match &then_branch.tail {
            BlockTail::Value(Expr::If { .. }) => {}
            other => panic!("expected inner Value(If), got {other:?}"),
        }
    }

    #[test]
    fn canonicalize_match_with_all_arms_break() {
        let cases = vec![
            MatchArm {
                variant: 0,
                bindings: Vec::new(),
                body: Box::new(break_block(0)),
            },
            MatchArm {
                variant: 1,
                bindings: Vec::new(),
                body: Box::new(break_block(0)),
            },
        ];
        let m = Expr::Match {
            struct_id: 0,
            selector: Box::new(Expr::Unit),
            cases,
        };
        let mut b = Block {
            stmts: vec![Stmt::Eval(m)],
            tail: BlockTail::Value(Expr::Unit),
        };
        canonicalize(&mut b);
        match b.tail {
            BlockTail::Value(Expr::Match { .. }) => {}
            other => panic!("expected Value(Match), got {other:?}"),
        }
    }

    #[test]
    fn canonicalize_skips_empty_match() {
        // Empty cases vector -- defensively NOT a terminator.
        let m = Expr::Match {
            struct_id: 0,
            selector: Box::new(Expr::Unit),
            cases: Vec::new(),
        };
        let mut b = Block {
            stmts: vec![Stmt::Eval(m)],
            tail: BlockTail::Value(Expr::Unit),
        };
        let snapshot = b.clone();
        canonicalize(&mut b);
        assert_eq!(b, snapshot);
    }
}
