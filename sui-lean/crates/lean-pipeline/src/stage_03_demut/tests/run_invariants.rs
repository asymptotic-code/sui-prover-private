//! Idempotency + determinism tests for `stage_03_demut::run`.

use crate::ir::builder::{lit_u64, var};
use crate::ir::{Block, BlockTail, Expr, Stmt, Type, VarId};
use crate::stage_03_demut::run;

use super::fixtures::{func, mut_ref, param, program_with, sig, FuncOpts};

fn t() -> Type {
    Type::UInt(64)
}

fn vid(name: &str) -> VarId {
    VarId::from(name)
}

fn build_prog() -> crate::ir::Program {
    // g(x: &mut T): R { *x = 42; 7 }
    let g_body = Block {
        stmts: vec![
            Stmt::Let {
                pattern: vec![Some(vid("r0"))],
                value: Expr::BorrowLoc(vid("x")),
            },
            Stmt::Eval(Expr::WriteRef {
                reference: Box::new(var("r0")),
                value: Box::new(lit_u64(42)),
            }),
        ],
        tail: BlockTail::Value(lit_u64(7)),
    };
    let g = func(
        "g",
        sig(vec![param("x", mut_ref(t(), t()))], t()),
        g_body,
        FuncOpts::default(),
    );

    // caller(arg: &mut T) { let r = g(&mut arg); }
    let caller_body = Block {
        stmts: vec![
            Stmt::Let {
                pattern: vec![Some(vid("r0"))],
                value: Expr::BorrowLoc(vid("arg")),
            },
            Stmt::Let {
                pattern: vec![Some(vid("r"))],
                value: Expr::Call {
                    fun: 0,
                    type_args: Vec::new(),
                    args: vec![var("r0")],
                },
            },
        ],
        tail: BlockTail::Value(Expr::Unit),
    };
    let caller = func(
        "caller",
        sig(vec![param("arg", mut_ref(t(), t()))], Type::Unit),
        caller_body,
        FuncOpts::default(),
    );

    program_with(vec![(0, g), (1, caller)])
}

#[test]
fn idempotent_run_twice_is_noop_on_second_call() {
    let mut prog = build_prog();
    run(&mut prog).expect("first run ok");
    let after_first = prog.clone();
    run(&mut prog).expect("second run ok");
    assert_eq!(
        prog, after_first,
        "stage 3 should be idempotent on a stage-3-clean program"
    );
}

#[test]
fn deterministic_byte_identical_output() {
    let mut prog_a = build_prog();
    let mut prog_b = build_prog();
    run(&mut prog_a).expect("run a ok");
    run(&mut prog_b).expect("run b ok");
    assert_eq!(prog_a, prog_b, "same input -> byte-identical output");
}
