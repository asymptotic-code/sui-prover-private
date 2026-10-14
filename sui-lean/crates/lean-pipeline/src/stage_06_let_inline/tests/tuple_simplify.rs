//! Tests for sub-pass 2c (`tuple_simplify`).

use super::fixtures::*;
use crate::ir::{BlockTail, Effects, Expr, Stmt, Type};
use crate::stage_06_let_inline::tuple_simplify::tuple_simplify_once;

#[test]
fn single_position_unused_pure_let_is_dropped() {
    // `let a = x; 0`  -- a unused, value is Var (pure-total).
    let mut body = block_value(
        vec![Stmt::Let {
            pattern: vec![Some(vid("a"))],
            value: var("x"),
        }],
        u64_const(0),
    );
    let p = empty_program();
    let changed = tuple_simplify_once(&mut body, &p);
    assert!(changed);
    assert_eq!(body.stmts.len(), 0);
}

#[test]
fn single_position_unused_impure_let_becomes_eval() {
    // `let a = side_effecting_call(); 0`  -- a unused, value impure.
    let callee = stub_callee("imp", Effects::CONSERVATIVE, Type::UInt(64));
    let p = program_with(vec![(7, callee)]);
    let mut body = block_value(
        vec![Stmt::Let {
            pattern: vec![Some(vid("a"))],
            value: call(7, vec![]),
        }],
        u64_const(0),
    );
    let changed = tuple_simplify_once(&mut body, &p);
    assert!(changed);
    assert_eq!(body.stmts.len(), 1);
    assert!(matches!(&body.stmts[0], Stmt::Eval(_)));
}

#[test]
fn unused_position_replaced_with_wildcard() {
    // `let (a, b) = pair_call(); a`  -- b unused. Pair_call is Impure
    // so the Let isn't dropped; only b's pattern slot becomes None.
    let callee = stub_callee("pair", Effects::CONSERVATIVE, Type::Unit);
    let p = program_with(vec![(7, callee)]);
    let mut body = block_value(
        vec![Stmt::Let {
            pattern: vec![Some(vid("a")), Some(vid("b"))],
            value: call(7, vec![]),
        }],
        var("a"),
    );
    let changed = tuple_simplify_once(&mut body, &p);
    assert!(changed);
    assert_eq!(body.stmts.len(), 1);
    if let Stmt::Let { pattern, .. } = &body.stmts[0] {
        assert!(matches!(&pattern[0], Some(v) if v.as_ref() == "a"));
        assert!(pattern[1].is_none());
    } else {
        panic!("expected Let with wildcard");
    }
}

#[test]
fn all_positions_unused_pure_total_value_dropped() {
    // `let (a, b) = pure_call(); 0`  -- a/b unused, value pure-total.
    let callee = stub_callee("pure", Effects::PURE, Type::Unit);
    let p = program_with(vec![(7, callee)]);
    let mut body = block_value(
        vec![Stmt::Let {
            pattern: vec![Some(vid("a")), Some(vid("b"))],
            value: call(7, vec![]),
        }],
        u64_const(0),
    );
    let changed = tuple_simplify_once(&mut body, &p);
    assert!(changed);
    assert_eq!(body.stmts.len(), 0);
}

#[test]
fn all_positions_unused_impure_value_becomes_eval() {
    // `let (a, b) = imp_call(); 0`  -- a/b unused, value impure.
    let callee = stub_callee("imp", Effects::CONSERVATIVE, Type::Unit);
    let p = program_with(vec![(7, callee)]);
    let mut body = block_value(
        vec![Stmt::Let {
            pattern: vec![Some(vid("a")), Some(vid("b"))],
            value: call(7, vec![]),
        }],
        u64_const(0),
    );
    let changed = tuple_simplify_once(&mut body, &p);
    assert!(changed);
    assert_eq!(body.stmts.len(), 1);
    assert!(matches!(&body.stmts[0], Stmt::Eval(_)));
}

#[test]
fn used_let_is_untouched() {
    // `let a = x; a`  -- a is used; nothing to simplify.
    let mut body = block_value(vec![let_stmt("a", var("x"))], var("a"));
    let p = empty_program();
    let changed = tuple_simplify_once(&mut body, &p);
    assert!(!changed);
}

#[test]
fn descends_into_if_arm() {
    // body: if c { let a = x; 0 } else { 0 } -- the inner let is dead.
    let then_b = block_value(vec![let_stmt("a", var("x"))], u64_const(0));
    let else_b = block_value(vec![], u64_const(0));
    let mut body = block_value(vec![], if_expr(var("c"), then_b, else_b));
    let p = empty_program();
    let changed = tuple_simplify_once(&mut body, &p);
    assert!(changed);
    if let BlockTail::Value(Expr::If { then_branch, .. }) = &body.tail {
        assert_eq!(then_branch.stmts.len(), 0);
    } else {
        panic!("expected If tail");
    }
}
