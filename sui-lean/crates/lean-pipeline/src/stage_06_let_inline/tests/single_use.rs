//! Tests for sub-pass 2b (`single_use_inline`).

use super::fixtures::*;
use crate::ir::{AbortBit, BlockTail, DetBit, Effects, Expr, MutLevel, Stmt, Type};
use crate::stage_06_let_inline::single_use::single_use_inline_once;

#[test]
fn field_projection_single_use_inlines() {
    // `let a = s.f0; a`  ->  `s.f0`
    let mut body = block_value(
        vec![Stmt::Let {
            pattern: vec![Some(vid("a"))],
            value: Expr::Field {
                struct_id: 7,
                field_index: 0,
                base: Box::new(var("s")),
            },
        }],
        var("a"),
    );
    let p = empty_program();
    let changed = single_use_inline_once(&mut body, &p);
    assert!(changed);
    assert_eq!(body.stmts.len(), 0);
    assert!(matches!(&body.tail, BlockTail::Value(Expr::Field { .. })));
}

#[test]
fn pure_total_pack_single_use_inlines() {
    // `let a = Pack S { x, y }; a`  ->  `Pack S { x, y }`
    let pack = Expr::Pack {
        struct_id: 7,
        type_args: Vec::new(),
        variant: None,
        fields: vec![var("x"), var("y")],
    };
    let mut body = block_value(
        vec![Stmt::Let {
            pattern: vec![Some(vid("a"))],
            value: pack,
        }],
        var("a"),
    );
    let p = empty_program();
    let changed = single_use_inline_once(&mut body, &p);
    assert!(changed);
    assert_eq!(body.stmts.len(), 0);
}

#[test]
fn multi_use_pack_is_not_inlined() {
    // `let a = Pack S { x, y }; (a, a)`  -- NOT inlined (would
    // duplicate work).
    let pack = Expr::Pack {
        struct_id: 7,
        type_args: Vec::new(),
        variant: None,
        fields: vec![var("x"), var("y")],
    };
    let mut body = block_value(
        vec![Stmt::Let {
            pattern: vec![Some(vid("a"))],
            value: pack,
        }],
        tuple(vec![var("a"), var("a")]),
    );
    let p = empty_program();
    let changed = single_use_inline_once(&mut body, &p);
    assert!(!changed);
    assert_eq!(body.stmts.len(), 1);
}

#[test]
fn pure_total_call_inlines() {
    // `let a = f(); a` where f is PureTotal.
    let callee = stub_callee("f", Effects::PURE, Type::UInt(64));
    let p = program_with(vec![(7, callee)]);

    let mut body = block_value(
        vec![Stmt::Let {
            pattern: vec![Some(vid("a"))],
            value: call(7, vec![]),
        }],
        var("a"),
    );
    let changed = single_use_inline_once(&mut body, &p);
    assert!(changed);
    assert_eq!(body.stmts.len(), 0);
    assert!(matches!(&body.tail, BlockTail::Value(Expr::Call { .. })));
}

#[test]
fn pure_partial_call_is_not_inlined() {
    // `let a = f(); a` where f is PurePartial (e.g., aborts).
    let callee = stub_callee(
        "f",
        Effects {
            aborts: AbortBit::Partial,
            det: DetBit::Det,
            mutation: MutLevel::NoMut,
            world_writes: false,
        },
        Type::UInt(64),
    );
    let p = program_with(vec![(7, callee)]);

    let mut body = block_value(
        vec![Stmt::Let {
            pattern: vec![Some(vid("a"))],
            value: call(7, vec![]),
        }],
        var("a"),
    );
    let changed = single_use_inline_once(&mut body, &p);
    assert!(!changed);
    assert_eq!(body.stmts.len(), 1);
}

#[test]
fn impure_call_is_not_inlined() {
    // `let a = f(); a` where f is Impure (e.g., transfer).
    let callee = stub_callee("f", Effects::CONSERVATIVE, Type::UInt(64));
    let p = program_with(vec![(7, callee)]);

    let mut body = block_value(
        vec![Stmt::Let {
            pattern: vec![Some(vid("a"))],
            value: call(7, vec![]),
        }],
        var("a"),
    );
    let changed = single_use_inline_once(&mut body, &p);
    assert!(!changed);
}

#[test]
fn arithmetic_let_is_not_inlined() {
    // `let a = b + c; a`  -- BinOp::Add on UInt is partial.
    let mut body = block_value(vec![let_stmt("a", add(var("b"), var("c")))], var("a"));
    let p = empty_program();
    let changed = single_use_inline_once(&mut body, &p);
    assert!(!changed);
    assert_eq!(body.stmts.len(), 1);
}

#[test]
fn var_copy_let_is_skipped() {
    // `let a = b; a`  -- Var copy is 2a's job, not 2b's.
    let mut body = block_value(vec![let_stmt("a", var("b"))], var("a"));
    let p = empty_program();
    let changed = single_use_inline_once(&mut body, &p);
    assert!(!changed);
}

#[test]
fn const_let_is_skipped() {
    // `let a = 7; a`  -- Const is 2a's job, not 2b's.
    let mut body = block_value(vec![let_stmt("a", u64_const(7))], var("a"));
    let p = empty_program();
    let changed = single_use_inline_once(&mut body, &p);
    assert!(!changed);
}

#[test]
fn does_not_inline_if_use_count_is_zero() {
    // `let a = s.f0; 0`  -- a is unused; 2c's job, not 2b's.
    let mut body = block_value(
        vec![Stmt::Let {
            pattern: vec![Some(vid("a"))],
            value: Expr::Field {
                struct_id: 7,
                field_index: 0,
                base: Box::new(var("s")),
            },
        }],
        u64_const(0),
    );
    let p = empty_program();
    let changed = single_use_inline_once(&mut body, &p);
    assert!(!changed);
}

#[test]
fn cascading_inlines_in_one_pass() {
    // `let a = pure_call(); let b = (a, 1); b`
    //
    // count(a) = 1, count(b) = 1, both pure-total.
    //
    // After one pass: both a and b should be inlined (count stability
    // proof in the doc comment of `single_use.rs`).
    let callee = stub_callee("pure_call", Effects::PURE, Type::UInt(64));
    let p = program_with(vec![(7, callee)]);

    let mut body = block_value(
        vec![
            Stmt::Let {
                pattern: vec![Some(vid("a"))],
                value: call(7, vec![]),
            },
            Stmt::Let {
                pattern: vec![Some(vid("b"))],
                value: tuple(vec![var("a"), u64_const(1)]),
            },
        ],
        var("b"),
    );
    let changed = single_use_inline_once(&mut body, &p);
    assert!(changed);
    assert_eq!(body.stmts.len(), 0);
    // Tail should be Tuple([Call(7, []), Const(1)])
    if let BlockTail::Value(Expr::Tuple(elems)) = &body.tail {
        assert_eq!(elems.len(), 2);
        assert!(matches!(&elems[0], Expr::Call { fun: 7, .. }));
        assert!(matches!(&elems[1], Expr::Const(_)));
    } else {
        panic!("expected Tuple tail, got {:?}", body.tail);
    }
}

#[test]
fn descends_into_if_arm() {
    // body: if c { let a = s.f0; a } else { 0 }
    let then_b = block_value(
        vec![Stmt::Let {
            pattern: vec![Some(vid("a"))],
            value: Expr::Field {
                struct_id: 7,
                field_index: 0,
                base: Box::new(var("s")),
            },
        }],
        var("a"),
    );
    let else_b = block_value(vec![], u64_const(0));
    let mut body = block_value(vec![], if_expr(var("c"), then_b, else_b));
    let p = empty_program();
    let changed = single_use_inline_once(&mut body, &p);
    assert!(changed);
    if let BlockTail::Value(Expr::If { then_branch, .. }) = &body.tail {
        assert_eq!(then_branch.stmts.len(), 0);
        assert!(matches!(
            &then_branch.tail,
            BlockTail::Value(Expr::Field { .. })
        ));
    } else {
        panic!("expected If tail");
    }
}

#[test]
fn pattern_4b_call_result_is_not_inlined() {
    // Pattern-4b consumers have `let r = mutref_call(...)` body-locals
    // that survive into stage 6 with `Type::MutableRef` slots. The
    // call's return is `Type::MutableRef`, but our pure-and-total check only
    // depends on the callee's `Effects`. For typical pattern-4b
    // functions, effects carry `aborts: Partial` (they take `&mut`
    // args, which makes them at-most-partial). So the let isn't
    // inlined.
    //
    // This test exercises the wiring: a callee with non-PURE
    // effects isn't inlined.
    let callee = stub_callee(
        "borrow_field",
        Effects {
            aborts: AbortBit::Partial,
            det: DetBit::Det,
            mutation: MutLevel::NoMut,
            world_writes: false,
        },
        Type::Unit,
    );
    let p = program_with(vec![(7, callee)]);

    let mut body = block_value(
        vec![Stmt::Let {
            pattern: vec![Some(vid("r"))],
            value: call(7, vec![var("s")]),
        }],
        var("r"),
    );
    let changed = single_use_inline_once(&mut body, &p);
    assert!(!changed);
}
