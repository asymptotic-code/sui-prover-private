//! Free-variable analysis on `Block` / `Expr`.
//!
//! Returns the set of `VarId`s referenced inside a sub-tree that are
//! NOT bound by some enclosing binder within that sub-tree. Function
//! parameters live outside the walked sub-tree, so they always count
//! as free; the caller filters those out.
//!
//! Used by `crate::ir::analysis::extract` to size captured-vars
//! lists, and by stage 7 (loops + continuations extraction).
//!
//! ## Binding sites
//!
//! - `Stmt::Let { pattern, value }` -- pattern names bind from the
//!   stmt onward in the same `Block` (value is evaluated in the
//!   pre-binding scope). `None` positions in the pattern bind no
//!   name.
//! - `MatchArm::bindings` -- bind for the arm `body` only.
//! - `Quantifier::binder` -- binds for the quantifier `body` only;
//!   `domain` evaluated in outer scope.
//! - `Expr::While::iter_locals` -- each `(VarId, init)`: `init`
//!   evaluated in the OUTER scope (binder not yet in scope); the
//!   `VarId` is bound for `header`, `cond`, and `body`.
//!
//! ## Use sites
//!
//! Most uses come through `Expr::Var(v)`. Three other expression
//! variants reference vars structurally (not via `Expr::Var`) and
//! must be counted as uses:
//!
//! - `Expr::BorrowLoc(v)` -- the borrowed local.
//! - `Expr::WriteBack { node, child, .. }` -- `child` is a use; if
//!   `node` is `BorrowNode::LocalRoot(v)` or `BorrowNode::Reference(v)`,
//!   `v` is also a use.

use std::collections::BTreeSet;

use crate::ir::analysis::scope::{self, ScopeObserver};
use crate::ir::expr::{Block, Expr};
use crate::ir::VarId;

/// Return the free vars of `b`: vars referenced inside `b` whose
/// binder is not inside `b`. Order is deterministic (`BTreeSet`).
pub fn free_vars(b: &Block) -> BTreeSet<VarId> {
    let mut fv = FreeVars::default();
    scope::walk_block(&mut fv, b);
    fv.free
}

/// Free vars of an expression, treated as a 1-statement block. Useful
/// for analysing single tail expressions or call arguments.
pub fn free_vars_of_expr(e: &Expr) -> BTreeSet<VarId> {
    let mut fv = FreeVars::default();
    scope::walk_expr(&mut fv, e);
    fv.free
}

/// `ScopeObserver` that records every use whose binder is not inside
/// the walked sub-tree. The binding discipline + var-carrier walk
/// live in [`crate::ir::analysis::scope`].
#[derive(Default)]
struct FreeVars {
    free: BTreeSet<VarId>,
}

impl ScopeObserver for FreeVars {
    fn on_use(&mut self, v: &VarId, in_scope: bool) {
        if !in_scope {
            self.free.insert(v.clone());
        }
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::borrow::{BorrowEdge, BorrowNode};
    use crate::ir::builder::{
        block, eval, just, let_stmt, lit_bool, lit_u64, tail_break, tail_continue, tail_return,
        tail_value, unit, var,
    };
    use crate::ir::expr::{Block, BlockTail, Expr, MatchArm, Stmt};
    use crate::ir::ops::BinOp;
    use crate::ir::quant::{QuantDomain, QuantifierKind};
    use crate::ir::ty::Type;

    fn vid(s: &str) -> VarId {
        s.into()
    }

    fn set_of(names: &[&str]) -> BTreeSet<VarId> {
        names.iter().map(|s| (*s).into()).collect()
    }

    #[test]
    fn empty_block_has_no_free_vars() {
        let b = just(unit());
        assert_eq!(free_vars(&b), BTreeSet::new());
    }

    #[test]
    fn var_in_value_tail_is_free() {
        let b = just(var("x"));
        assert_eq!(free_vars(&b), set_of(&["x"]));
    }

    #[test]
    fn let_binding_shadows_outer_use() {
        // let x = 1; x  -- x is bound, not free.
        let b = block(vec![let_stmt(&["x"], lit_u64(1))], tail_value(var("x")));
        assert_eq!(free_vars(&b), BTreeSet::new());
    }

    #[test]
    fn let_value_evaluated_in_outer_scope() {
        // let x = x + 1; x -- the rhs `x` refers to outer.
        let b = block(
            vec![let_stmt(
                &["x"],
                Expr::BinOp {
                    op: BinOp::Add,
                    lhs: Box::new(var("x")),
                    rhs: Box::new(lit_u64(1)),
                },
            )],
            tail_value(var("x")),
        );
        assert_eq!(free_vars(&b), set_of(&["x"]));
    }

    #[test]
    fn use_in_break_continue_return_abort_tails_counts() {
        let cases: Vec<BlockTail> = vec![
            tail_break(0, var("a")),
            tail_continue(0, var("b")),
            tail_return(var("c")),
            BlockTail::Abort {
                code: Box::new(var("d")),
            },
        ];
        for (tail, name) in cases.into_iter().zip(["a", "b", "c", "d"]) {
            let b = Block {
                stmts: vec![],
                tail,
            };
            assert_eq!(free_vars(&b), set_of(&[name]), "tail var {name} not free");
        }
    }

    #[test]
    fn borrow_loc_counts_as_use() {
        let b = just(Expr::BorrowLoc(vid("x")));
        assert_eq!(free_vars(&b), set_of(&["x"]));
    }

    #[test]
    fn borrow_global_has_no_local_free_variable() {
        let b = just(Expr::BorrowGlobal(7));
        assert!(free_vars(&b).is_empty());
    }

    #[test]
    fn write_back_child_and_node_count_as_uses() {
        // WriteBack { node: LocalRoot(parent), edge: Direct, child }
        let b = just(Expr::WriteBack {
            node: BorrowNode::LocalRoot(vid("parent")),
            edge: BorrowEdge::Direct,
            child: vid("child"),
            world: None,
        });
        assert_eq!(free_vars(&b), set_of(&["child", "parent"]));
    }

    #[test]
    fn write_back_reference_node_var_counts() {
        let b = just(Expr::WriteBack {
            node: BorrowNode::Reference(vid("p")),
            edge: BorrowEdge::Direct,
            child: vid("c"),
            world: None,
        });
        assert_eq!(free_vars(&b), set_of(&["c", "p"]));
    }

    #[test]
    fn write_back_spec_global_root_has_no_var() {
        // SpecGlobalRoot carries only type arguments -- no variable
        // reference -- so free_vars sees only the child.
        let b = just(Expr::WriteBack {
            node: BorrowNode::SpecGlobalRoot { type_args: vec![] },
            edge: BorrowEdge::Direct,
            child: vid("c"),
            world: None,
        });
        assert_eq!(free_vars(&b), set_of(&["c"]));
    }

    #[test]
    fn is_parent_node_and_child_count_as_uses() {
        // IsParent { node: LocalRoot(parent), edge: Direct, child } --
        // both the node's var and the child are reads (the conditional
        // borrow-dispatch predicate references both).
        let b = just(Expr::IsParent {
            node: BorrowNode::LocalRoot(vid("parent")),
            edge: BorrowEdge::Direct,
            child: vid("child"),
        });
        assert_eq!(free_vars(&b), set_of(&["child", "parent"]));
    }

    #[test]
    fn if_arms_are_independently_scoped() {
        // if c { let x = 1; x } else { x }
        // then-arm binds x; else-arm uses outer x. Both `c` and `x`
        // (from the else arm) are free.
        let then_b = block(vec![let_stmt(&["x"], lit_u64(1))], tail_value(var("x")));
        let else_b = just(var("x"));
        let if_e = Expr::If {
            cond: Box::new(var("c")),
            then_branch: Box::new(then_b),
            else_branch: Box::new(else_b),
        };
        let b = just(if_e);
        assert_eq!(free_vars(&b), set_of(&["c", "x"]));
    }

    #[test]
    fn match_arm_bindings_dont_leak() {
        // match e { 0 (x) => x | 1 (y) => x }
        // arm 0 binds x locally; arm 1's `x` is free.
        let arm0 = MatchArm {
            variant: 0,
            bindings: vec![vid("x")],
            body: Box::new(just(var("x"))),
        };
        let arm1 = MatchArm {
            variant: 1,
            bindings: vec![vid("y")],
            body: Box::new(just(var("x"))),
        };
        let b = just(Expr::Match {
            struct_id: 0,
            selector: Box::new(var("e")),
            cases: vec![arm0, arm1],
        });
        assert_eq!(free_vars(&b), set_of(&["e", "x"]));
    }

    #[test]
    fn quantifier_binder_scoped_to_body_domain_evaluates_outer() {
        // forall i in start..end, p(i, k)
        // start, end, k are free. i is bound only inside body.
        let body = just(Expr::Call {
            fun: 0,
            type_args: vec![],
            args: vec![var("i"), var("k")],
        });
        let q = Expr::Quantifier {
            kind: QuantifierKind::Forall,
            binder: vid("i"),
            binder_type: Type::UInt(64),
            domain: QuantDomain::Range {
                start: Box::new(var("start")),
                end: Box::new(var("end")),
            },
            body: Box::new(body),
        };
        let b = just(q);
        assert_eq!(free_vars(&b), set_of(&["end", "k", "start"]));
    }

    #[test]
    fn quantifier_unbounded_no_domain_use() {
        // forall x : T, x > 0   -- x bound, no other vars used.
        let body = just(Expr::BinOp {
            op: BinOp::Gt,
            lhs: Box::new(var("x")),
            rhs: Box::new(lit_u64(0)),
        });
        let q = Expr::Quantifier {
            kind: QuantifierKind::Forall,
            binder: vid("x"),
            binder_type: Type::UInt(64),
            domain: QuantDomain::Unbounded,
            body: Box::new(body),
        };
        assert_eq!(free_vars(&just(q)), BTreeSet::new());
    }

    #[test]
    fn while_iter_locals_init_evaluates_outer_binder_scoped_inner() {
        // While { iter_locals: [(i, start)], header: empty, cond: i < n,
        //         body: { Continue { 0, i + 1 } } }
        // `start` and `n` are free; `i` is bound by iter_locals.
        let header = just(unit());
        let cond = Expr::BinOp {
            op: BinOp::Lt,
            lhs: Box::new(var("i")),
            rhs: Box::new(var("n")),
        };
        let body_block = block(
            vec![],
            tail_continue(
                0,
                Expr::BinOp {
                    op: BinOp::Add,
                    lhs: Box::new(var("i")),
                    rhs: Box::new(lit_u64(1)),
                },
            ),
        );
        let while_e = Expr::While {
            header: Box::new(header),
            cond: Box::new(cond),
            body: Box::new(body_block),
            iter_locals: vec![(vid("i"), var("start"))],
            header_exit_locals: vec![vid("i")],
            live_out: vec![],
        };
        let b = just(while_e);
        assert_eq!(free_vars(&b), set_of(&["n", "start"]));
    }

    #[test]
    fn while_header_local_is_bound_in_body() {
        // While { iter_locals: [(i, start)], header: { let h = n }, cond: true,
        //         body: { continue 0 (h) } }
        // `h` is defined in the header and read in the body; the header
        // runs each iteration before the body, so `h` is in scope there
        // and is NOT free. `n` (header rhs) and `start` (iter-local init)
        // are free; `i` and `h` are bound.
        let header = block(vec![let_stmt(&["h"], var("n"))], tail_value(unit()));
        let body_block = block(vec![], tail_continue(0, var("h")));
        let while_e = Expr::While {
            header: Box::new(header),
            cond: Box::new(lit_bool(true)),
            body: Box::new(body_block),
            iter_locals: vec![(vid("i"), var("start"))],
            header_exit_locals: vec![vid("i")],
            live_out: vec![],
        };
        let b = just(while_e);
        assert_eq!(free_vars(&b), set_of(&["n", "start"]));
    }

    #[test]
    fn nested_block_let_doesnt_leak_to_outer() {
        // { let x = 1; if (true) { let y = 2; y + x } else { 0 }; x }
        // After the if, x is still bound (let above the if), y is not.
        // y has no use outside the then-arm. No free vars.
        let then_b = block(
            vec![let_stmt(&["y"], lit_u64(2))],
            tail_value(Expr::BinOp {
                op: BinOp::Add,
                lhs: Box::new(var("y")),
                rhs: Box::new(var("x")),
            }),
        );
        let else_b = just(lit_u64(0));
        let if_stmt = eval(Expr::If {
            cond: Box::new(lit_bool(true)),
            then_branch: Box::new(then_b),
            else_branch: Box::new(else_b),
        });
        let b = block(
            vec![let_stmt(&["x"], lit_u64(1)), if_stmt],
            tail_value(var("x")),
        );
        assert_eq!(free_vars(&b), BTreeSet::new());
    }

    #[test]
    fn multi_pattern_let_binds_all_named_positions() {
        // let (a, _, c) = (x, y, z); a + c
        // Pattern binds a and c (the wildcard binds nothing). All of
        // x, y, z are free; a and c are not.
        let value = Expr::Tuple(vec![var("x"), var("y"), var("z")]);
        let pat = Stmt::Let {
            pattern: vec![Some(vid("a")), None, Some(vid("c"))],
            value,
        };
        let tail = tail_value(Expr::BinOp {
            op: BinOp::Add,
            lhs: Box::new(var("a")),
            rhs: Box::new(var("c")),
        });
        let b = block(vec![pat], tail);
        assert_eq!(free_vars(&b), set_of(&["x", "y", "z"]));
    }

    #[test]
    fn free_vars_of_expr_helper() {
        let e = Expr::BinOp {
            op: BinOp::Add,
            lhs: Box::new(var("a")),
            rhs: Box::new(var("b")),
        };
        assert_eq!(free_vars_of_expr(&e), set_of(&["a", "b"]));
    }
}
