//! Tests for sub-pass 2d (`eval_dce`).

use super::fixtures::*;
use crate::ir::{AbortBit, DetBit, Effects, Expr, MutLevel, Stmt, Type};
use crate::stage_06_let_inline::eval_dce::eval_dce_once;

#[test]
fn eval_const_dropped() {
    let mut body = block_value(vec![Stmt::Eval(u64_const(5))], u64_const(0));
    let p = empty_program();
    let changed = eval_dce_once(&mut body, &p);
    assert!(changed);
    assert_eq!(body.stmts.len(), 0);
}

#[test]
fn eval_pure_total_call_dropped() {
    let callee = stub_callee("pure", Effects::PURE, Type::Unit);
    let p = program_with(vec![(7, callee)]);
    let mut body = block_value(vec![Stmt::Eval(call(7, vec![]))], u64_const(0));
    let changed = eval_dce_once(&mut body, &p);
    assert!(changed);
    assert_eq!(body.stmts.len(), 0);
}

#[test]
fn eval_pure_partial_call_kept() {
    let callee = stub_callee(
        "partial",
        Effects {
            aborts: AbortBit::Partial,
            det: DetBit::Det,
            mutation: MutLevel::NoMut,
            world_writes: false,
        },
        Type::Unit,
    );
    let p = program_with(vec![(7, callee)]);
    let mut body = block_value(vec![Stmt::Eval(call(7, vec![]))], u64_const(0));
    let changed = eval_dce_once(&mut body, &p);
    assert!(!changed);
    assert_eq!(body.stmts.len(), 1);
}

#[test]
fn eval_impure_call_kept() {
    let callee = stub_callee("imp", Effects::CONSERVATIVE, Type::Unit);
    let p = program_with(vec![(7, callee)]);
    let mut body = block_value(vec![Stmt::Eval(call(7, vec![]))], u64_const(0));
    let changed = eval_dce_once(&mut body, &p);
    assert!(!changed);
    assert_eq!(body.stmts.len(), 1);
}

#[test]
fn eval_arithmetic_kept() {
    // BinOp::Add on UInt is partial -- the Eval is retained.
    let mut body = block_value(
        vec![Stmt::Eval(add(u64_const(1), u64_const(2)))],
        u64_const(0),
    );
    let p = empty_program();
    let changed = eval_dce_once(&mut body, &p);
    assert!(!changed);
    assert_eq!(body.stmts.len(), 1);
}

#[test]
fn multiple_pure_evals_all_dropped() {
    let mut body = block_value(
        vec![
            Stmt::Eval(u64_const(1)),
            Stmt::Eval(var("x")),
            Stmt::Eval(Expr::Unit),
        ],
        u64_const(0),
    );
    let p = empty_program();
    let changed = eval_dce_once(&mut body, &p);
    assert!(changed);
    assert_eq!(body.stmts.len(), 0);
}

#[test]
fn descends_into_if_arm() {
    let then_b = block_value(vec![Stmt::Eval(u64_const(1))], u64_const(0));
    let else_b = block_value(vec![], u64_const(0));
    let mut body = block_value(vec![], if_expr(var("c"), then_b, else_b));
    let p = empty_program();
    let changed = eval_dce_once(&mut body, &p);
    assert!(changed);
}
