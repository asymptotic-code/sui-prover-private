//! Stage-5 run-level invariant tests:
//! - **Re-run idempotency** (alpha-equivalent up to fresh counter):
//!   running stage 5 a second time over its own output produces a
//!   program that still passes the postcondition. (Strict
//!   byte-identical idempotency does NOT hold -- a second alpha-rename
//!   pass introduces new counter suffixes -- but the structural
//!   result is well-formed SSA either way.)
//! - **Determinism**: same input twice -> byte-identical output.
//! - **Stage-6 handoff** (stub): for now, stage 5 hands off to
//!   stage 6 by guaranteeing its own postcondition. When stage 6's
//!   `preconditions::check` lands, this test gets upgraded.

use crate::ir::{BlockTail, Expr, Stmt, Type};
use crate::stage_05_ssa::postcondition::check;
use crate::stage_05_ssa::run;

use super::fixtures::*;

fn build_fixture() -> crate::ir::Program {
    let stmts = vec![
        Stmt::Let {
            pattern: vec![Some("x".into())],
            value: lit_u64(1),
        },
        Stmt::Let {
            pattern: vec![Some("x".into())],
            value: lit_u64(2),
        },
        Stmt::Eval(Expr::If {
            cond: Box::new(Expr::Var("c".into())),
            then_branch: Box::new(Block {
                stmts: vec![Stmt::Let {
                    pattern: vec![Some("x".into())],
                    value: lit_u64(3),
                }],
                tail: BlockTail::Value(Expr::Unit),
            }),
            else_branch: Box::new(Block {
                stmts: vec![Stmt::Let {
                    pattern: vec![Some("x".into())],
                    value: lit_u64(4),
                }],
                tail: BlockTail::Value(Expr::Unit),
            }),
        }),
    ];
    one_fn_program(
        stmts,
        Expr::Var("x".into()),
        vec![param("c", Type::Bool), param("x", Type::UInt(64))],
        Type::UInt(64),
    )
}

#[test]
fn rerun_postcondition_holds() {
    let mut p = build_fixture();
    run(&mut p).unwrap();
    check(&p).unwrap();
    // Re-run on already-renamed output. The counter advances; new
    // names are still unique. Postcondition still holds.
    run(&mut p).unwrap();
    check(&p).unwrap();
}

#[test]
fn deterministic_byte_identical_output() {
    let mut p1 = build_fixture();
    let mut p2 = build_fixture();
    run(&mut p1).unwrap();
    run(&mut p2).unwrap();
    assert_eq!(p1, p2);
}

#[test]
fn postcondition_holds_after_run() {
    let mut p = build_fixture();
    run(&mut p).unwrap();
    check(&p).expect("stage-5 postcondition should hold immediately after run");
}

use crate::ir::expr::Block;
