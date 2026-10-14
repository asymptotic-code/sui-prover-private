//! Phase 5 unit tests for the stage-3 postcondition validator.

use crate::ir::builder::{lit_u64, var};
use crate::ir::{Block, BlockTail, BorrowEdge, BorrowNode, Expr, Stmt, Type, VarId};
use crate::stage_03_demut::postcondition::{check, PostconditionError};
use crate::stage_03_demut::run;

use super::fixtures::{body_returning, func, mut_ref, param, program_with, sig, FuncOpts};

fn t() -> Type {
    Type::UInt(64)
}

fn vid(name: &str) -> VarId {
    VarId::from(name)
}

#[test]
fn well_formed_stage_3_output_passes() {
    // Run the full pipeline, then check.
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
        tail: BlockTail::Value(Expr::Unit),
    };
    let g = func(
        "g",
        sig(vec![param("x", mut_ref(t(), t()))], Type::Unit),
        g_body,
        FuncOpts::default(),
    );
    let mut prog = program_with(vec![(0, g)]);
    run(&mut prog).expect("run ok");
    check(&prog).expect("postcondition should pass after run");
}

#[test]
fn lingering_write_ref_rejects() {
    // Bind a genuine MutableRef so the base validator accepts the WriteRef;
    // the stage-specific lingering-operation check must be what rejects it.
    let body = Block {
        stmts: vec![
            Stmt::Let {
                pattern: vec![Some(vid("r"))],
                value: Expr::BorrowLoc(vid("local")),
            },
            Stmt::Eval(Expr::WriteRef {
                reference: Box::new(var("r")),
                value: Box::new(lit_u64(1)),
            }),
        ],
        tail: BlockTail::Value(Expr::Unit),
    };
    let f = func(
        "f",
        sig(vec![param("local", t())], Type::Unit),
        body,
        FuncOpts::default(),
    );
    let prog = program_with(vec![(0, f)]);
    let err = check(&prog).unwrap_err();
    assert_eq!(err, PostconditionError::WriteRefSurvived { function: 0 });
}

#[test]
fn lingering_write_back_rejects() {
    // Bind `r` to make the body otherwise well-formed (base validator
    // checks variable scope before stage-3-specific rules fire).
    let body = Block {
        stmts: vec![
            Stmt::Let {
                pattern: vec![Some(vid("r"))],
                value: Expr::BorrowLoc(vid("local")),
            },
            Stmt::Eval(Expr::WriteBack {
                node: BorrowNode::LocalRoot(vid("local")),
                edge: BorrowEdge::Direct,
                child: vid("r"),
                world: None,
            }),
        ],
        tail: BlockTail::Value(Expr::Unit),
    };
    let f = func(
        "f",
        sig(vec![param("local", t())], Type::Unit),
        body,
        FuncOpts::default(),
    );
    let prog = program_with(vec![(0, f)]);
    let err = check(&prog).unwrap_err();
    assert_eq!(err, PostconditionError::WriteBackSurvived { function: 0 });
}

#[test]
fn mut_ref_in_param_rejects() {
    let f = func(
        "f",
        sig(vec![param("x", mut_ref(t(), t()))], Type::Unit),
        body_returning(Expr::Unit),
        FuncOpts::default(),
    );
    let prog = program_with(vec![(0, f)]);
    let err = check(&prog).unwrap_err();
    assert_eq!(
        err,
        PostconditionError::MutRefInParam {
            function: 0,
            param_index: 0,
        }
    );
}

#[test]
fn empty_program_passes() {
    let prog = program_with(Vec::new());
    check(&prog).expect("empty program should pass");
}

#[test]
fn native_function_with_mut_param_is_exempt() {
    // Obsolete: natives now live in program.natives.decls, not
    // program.functions; stages walk only functions, so this
    // behavior is structurally guaranteed.
}
