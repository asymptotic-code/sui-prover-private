//! Defensive tests for `UseCount::has_borrow_use` and the sub-pass
//! candidate skips that depend on it.
//!
//! Stage 6's well-formed input is post-stage-4, where `Expr::BorrowLoc`
//! / `Expr::WriteBack` only survive in pattern-4b function tails.
//! These tests verify that if a regression lets such ops leak into a
//! regular body, the sub-passes refuse to inline / wildcard-collapse
//! the affected variable -- the base validator then catches the
//! pre-existing inconsistency rather than stage 6 producing broken IR.

use super::fixtures::*;
use crate::ir::{BorrowEdge, BorrowNode, Effects, Expr, Stmt, Type};
use crate::stage_06_let_inline::copy_inline::copy_inline_once;
use crate::stage_06_let_inline::single_use::single_use_inline_once;
use crate::stage_06_let_inline::tuple_simplify::tuple_simplify_once;
use crate::stage_06_let_inline::use_count::count_uses;

#[test]
fn borrowloc_counted_as_borrow_use() {
    // body: `let v = x; BorrowLoc(v); v`
    let body = block_value(
        vec![
            let_stmt("v", var("x")),
            Stmt::Eval(Expr::BorrowLoc(vid("v"))),
        ],
        var("v"),
    );
    let counts = count_uses(&body);
    assert!(counts.has_borrow_use(&vid("v")));
    // The `Var(v)` in the tail counts toward substitutable uses; the
    // BorrowLoc(v) inside the Eval does NOT bump `get(v)`.
    assert_eq!(counts.get(&vid("v")), 1);
}

#[test]
fn writeback_child_and_node_var_counted_as_borrow_use() {
    // `WriteBack { node: LocalRoot(parent), child }` carries TWO
    // bare-name VarId references: the `child` field directly, and
    // the `parent` inside `node`. Both are non-substitutable name
    // positions -- the renderer reads them by name, and sub-passes
    // (copy-inline / wildcard-collapse) must refuse to drop either.
    // See `UseCountWalker::mark_borrow_node_use`.
    let body = block_value(
        vec![Stmt::Eval(Expr::WriteBack {
            node: BorrowNode::LocalRoot(vid("parent")),
            edge: BorrowEdge::Direct,
            child: vid("child"),
            world: None,
        })],
        Expr::Unit,
    );
    let counts = count_uses(&body);
    assert!(counts.has_borrow_use(&vid("child")));
    assert!(counts.has_borrow_use(&vid("parent")));
}

#[test]
fn copy_inline_renames_borrow_use_for_var_repl() {
    // body: `let v = Var(x); BorrowLoc(v); 0`
    //
    // A `Var` replacement names a location, so copy_inline inlines it and
    // RENAMES the borrow position `BorrowLoc(v) -> BorrowLoc(x)`, then
    // drops the Let. (A borrow can be renamed var -> var.)
    let mut body = block_value(
        vec![
            let_stmt("v", var("x")),
            Stmt::Eval(Expr::BorrowLoc(vid("v"))),
        ],
        u64_const(0),
    );
    let changed = copy_inline_once(&mut body);
    assert!(changed);
    assert_eq!(body.stmts.len(), 1);
    match &body.stmts[0] {
        Stmt::Eval(Expr::BorrowLoc(w)) => assert_eq!(w.as_ref(), "x"),
        other => panic!("expected Eval(BorrowLoc(x)), got {other:?}"),
    }
}

#[test]
fn copy_inline_refuses_borrow_use_for_const_repl() {
    // body: `let v = 5; BorrowLoc(v); 0`
    //
    // A `Const` has no location -- it can't fill a borrow slot. So the
    // borrow use of `v` blocks the copy; the Let stays and BorrowLoc(v)
    // is not left dangling.
    let mut body = block_value(
        vec![
            let_stmt("v", u64_const(5)),
            Stmt::Eval(Expr::BorrowLoc(vid("v"))),
        ],
        u64_const(0),
    );
    let changed = copy_inline_once(&mut body);
    assert!(!changed);
    assert_eq!(body.stmts.len(), 2);
}

#[test]
fn copy_inline_renames_writeback_child_for_var_repl() {
    // body: `let v = Var(x); WriteBack { node: LocalRoot(p), child: v }; 0`
    //
    // Writeback renames are safe var -> var: the child slot `v` becomes
    // `x`. The `node` LocalRoot(p) is untouched (names a different var).
    let mut body = block_value(
        vec![
            let_stmt("v", var("x")),
            Stmt::Eval(Expr::WriteBack {
                node: BorrowNode::LocalRoot(vid("p")),
                edge: BorrowEdge::Direct,
                child: vid("v"),
                world: None,
            }),
        ],
        u64_const(0),
    );
    let changed = copy_inline_once(&mut body);
    assert!(changed);
    assert_eq!(body.stmts.len(), 1);
    match &body.stmts[0] {
        Stmt::Eval(Expr::WriteBack { child, node, .. }) => {
            assert_eq!(child.as_ref(), "x");
            assert!(matches!(node, BorrowNode::LocalRoot(p) if p.as_ref() == "p"));
        }
        other => panic!("expected Eval(WriteBack child=x), got {other:?}"),
    }
}

#[test]
fn single_use_refuses_when_borrow_use_present() {
    // body: `let v = s.f0; BorrowLoc(v); v`
    //
    // count(v) = 1, value is pure-total (Field). Without the skip,
    // single_use would inline v -> s.f0 at the Var(v) tail and drop
    // the Let, leaving BorrowLoc(v) dangling.
    let mut body = block_value(
        vec![
            Stmt::Let {
                pattern: vec![Some(vid("v"))],
                value: Expr::Field {
                    struct_id: 7,
                    field_index: 0,
                    base: Box::new(var("s")),
                },
            },
            Stmt::Eval(Expr::BorrowLoc(vid("v"))),
        ],
        var("v"),
    );
    let p = empty_program();
    let changed = single_use_inline_once(&mut body, &p);
    assert!(!changed);
    assert_eq!(body.stmts.len(), 2);
}

#[test]
fn tuple_simplify_refuses_wildcard_when_borrow_use_present() {
    // body: `let v = call(); BorrowLoc(v); 0`
    //
    // count(v) = 0, but BorrowLoc(v) keeps it alive. tuple_simplify
    // would otherwise wildcard-collapse `Some(v) -> None`, making it
    // an all-wildcard Let and dropping / converting it. The skip
    // refuses.
    let callee = stub_callee("imp", Effects::CONSERVATIVE, Type::Unit);
    let p = program_with(vec![(7, callee)]);
    let mut body = block_value(
        vec![
            Stmt::Let {
                pattern: vec![Some(vid("v"))],
                value: call(7, vec![]),
            },
            Stmt::Eval(Expr::BorrowLoc(vid("v"))),
        ],
        u64_const(0),
    );
    let changed = tuple_simplify_once(&mut body, &p);
    assert!(!changed);
    assert_eq!(body.stmts.len(), 2);
    if let Stmt::Let { pattern, .. } = &body.stmts[0] {
        assert!(matches!(&pattern[0], Some(n) if n.as_ref() == "v"));
    } else {
        panic!("expected Let");
    }
}
