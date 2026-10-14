//! Tests for the tuple-literal splitting pre-pass.

use super::fixtures::*;
use crate::ir::{BlockTail, Effects, Expr, Stmt, Type};
use crate::stage_06_let_inline::tuple_split::split_tuple_literals;

#[test]
fn splits_simple_tuple_literal_with_pure_total_elems() {
    // `let (a, b) = (x, y); (a, b)`
    // -> `let a = x; let b = y; (a, b)`
    let mut body = block_value(
        vec![Stmt::Let {
            pattern: vec![Some(vid("a")), Some(vid("b"))],
            value: tuple(vec![var("x"), var("y")]),
        }],
        tuple(vec![var("a"), var("b")]),
    );
    let p = empty_program();
    let changed = split_tuple_literals(&mut body, &p);
    assert!(changed);
    assert_eq!(body.stmts.len(), 2);
    if let Stmt::Let { pattern, value } = &body.stmts[0] {
        assert_eq!(pattern.len(), 1);
        assert!(matches!(&pattern[0], Some(v) if v.as_ref() == "a"));
        assert!(matches!(value, Expr::Var(v) if v.as_ref() == "x"));
    } else {
        panic!("expected let a = x");
    }
    if let Stmt::Let { pattern, value } = &body.stmts[1] {
        assert!(matches!(&pattern[0], Some(v) if v.as_ref() == "b"));
        assert!(matches!(value, Expr::Var(v) if v.as_ref() == "y"));
    } else {
        panic!("expected let b = y");
    }
}

#[test]
fn does_not_split_when_any_element_is_partial() {
    // `let (a, b) = (x, c + 1); (a, b)`
    // The second element is partial (BinOp::Add on UInt).
    let mut body = block_value(
        vec![Stmt::Let {
            pattern: vec![Some(vid("a")), Some(vid("b"))],
            value: tuple(vec![var("x"), add(var("c"), u64_const(1))]),
        }],
        tuple(vec![var("a"), var("b")]),
    );
    let p = empty_program();
    let changed = split_tuple_literals(&mut body, &p);
    assert!(!changed);
    assert_eq!(body.stmts.len(), 1);
}

#[test]
fn does_not_split_when_value_is_not_tuple_literal() {
    // `let (a, b) = f(); (a, b)` -- not a tuple literal.
    let callee = stub_callee("f", Effects::PURE, Type::Unit);
    let p = program_with(vec![(7, callee)]);
    let mut body = block_value(
        vec![Stmt::Let {
            pattern: vec![Some(vid("a")), Some(vid("b"))],
            value: call(7, vec![]),
        }],
        tuple(vec![var("a"), var("b")]),
    );
    let changed = split_tuple_literals(&mut body, &p);
    assert!(!changed);
    assert_eq!(body.stmts.len(), 1);
}

#[test]
fn does_not_split_when_arity_mismatches() {
    // `let (a, b) = (x, y, z); ...` -- arity 2 vs 3.
    let mut body = block_value(
        vec![Stmt::Let {
            pattern: vec![Some(vid("a")), Some(vid("b"))],
            value: tuple(vec![var("x"), var("y"), var("z")]),
        }],
        u64_const(0),
    );
    let p = empty_program();
    let changed = split_tuple_literals(&mut body, &p);
    assert!(!changed);
}

#[test]
fn drops_wildcard_positions() {
    // `let (a, _) = (x, y); a`
    // -> `let a = x; a` (the wildcard position with pure-total `y`
    //    drops entirely).
    let mut body = block_value(
        vec![Stmt::Let {
            pattern: vec![Some(vid("a")), None],
            value: tuple(vec![var("x"), var("y")]),
        }],
        var("a"),
    );
    let p = empty_program();
    let changed = split_tuple_literals(&mut body, &p);
    assert!(changed);
    assert_eq!(body.stmts.len(), 1);
    if let Stmt::Let { pattern, value } = &body.stmts[0] {
        assert_eq!(pattern.len(), 1);
        assert!(matches!(&pattern[0], Some(v) if v.as_ref() == "a"));
        assert!(matches!(value, Expr::Var(v) if v.as_ref() == "x"));
    } else {
        panic!("expected let a = x");
    }
}

#[test]
fn descends_into_if_arm() {
    // body: if c { let (a, b) = (x, y); use a } else { 0 }
    let then_b = block_value(
        vec![Stmt::Let {
            pattern: vec![Some(vid("a")), Some(vid("b"))],
            value: tuple(vec![var("x"), var("y")]),
        }],
        var("a"),
    );
    let else_b = block_value(vec![], u64_const(0));
    let mut body = block_value(vec![], if_expr(var("c"), then_b, else_b));
    let p = empty_program();
    let changed = split_tuple_literals(&mut body, &p);
    assert!(changed);
    if let BlockTail::Value(Expr::If { then_branch, .. }) = &body.tail {
        assert_eq!(then_branch.stmts.len(), 2);
    } else {
        panic!("expected If tail");
    }
}

#[test]
fn three_position_tuple_splits_correctly() {
    // `let (a, b, c) = (x, y, z); ...`
    let mut body = block_value(
        vec![Stmt::Let {
            pattern: vec![Some(vid("a")), Some(vid("b")), Some(vid("c"))],
            value: tuple(vec![var("x"), var("y"), var("z")]),
        }],
        u64_const(0),
    );
    let p = empty_program();
    let changed = split_tuple_literals(&mut body, &p);
    assert!(changed);
    assert_eq!(body.stmts.len(), 3);
}

#[test]
fn single_position_let_is_skipped() {
    // `let a = (x); a` -- single-pattern Let isn't a tuple
    // destructure, regardless of value shape.
    let mut body = block_value(
        vec![Stmt::Let {
            pattern: vec![Some(vid("a"))],
            value: tuple(vec![var("x")]),
        }],
        var("a"),
    );
    let p = empty_program();
    let changed = split_tuple_literals(&mut body, &p);
    assert!(!changed);
    assert_eq!(body.stmts.len(), 1);
}
