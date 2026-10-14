//! Stage 4 idempotency + determinism tests.

use crate::ir::{Expr, Stmt, Type};
use crate::stage_04_effects::run;

use super::fixtures::*;

#[test]
fn idempotent_run_twice_is_noop() {
    let emit = native_impure("event::emit", vec![param("e", Type::UInt(64))], Type::Unit);
    let caller = func(
        "f",
        sig(Vec::new(), Type::Unit),
        body(
            vec![Stmt::Eval(Expr::Call {
                fun: 0,
                type_args: Vec::new(),
                args: vec![lit_u64(7)],
            })],
            Expr::Unit,
        ),
        FuncOpts::default(),
    );
    let mut program = program_with_natives(vec![(1, caller)], vec![(0, emit)]);
    run(&mut program).unwrap();
    let snapshot = program.clone();
    run(&mut program).unwrap();
    assert_eq!(program, snapshot);
}

#[test]
fn deterministic_byte_identical_output() {
    fn build() -> crate::ir::Program {
        let emit = native_impure("event::emit", vec![param("e", Type::UInt(64))], Type::Unit);
        let caller = func(
            "f",
            sig(Vec::new(), Type::UInt(64)),
            body(
                vec![Stmt::Eval(Expr::Call {
                    fun: 0,
                    type_args: Vec::new(),
                    args: vec![lit_u64(7)],
                })],
                lit_u64(42),
            ),
            FuncOpts::default(),
        );
        program_with_natives(vec![(1, caller)], vec![(0, emit)])
    }

    let mut p1 = build();
    let mut p2 = build();
    run(&mut p1).unwrap();
    run(&mut p2).unwrap();
    assert_eq!(p1, p2);
}

#[test]
fn idempotent_on_empty_program() {
    let mut p1 = program_with(Vec::new());
    let mut p2 = program_with(Vec::new());
    run(&mut p1).unwrap();
    run(&mut p2).unwrap();
    run(&mut p2).unwrap();
    assert_eq!(p1, p2);
}
