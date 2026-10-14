//! Tests for Transform 1: WriteRef position-shift.

use crate::ir::{Expr, Stmt, Type, VarId};
use crate::stage_03_mut_to_let::{rewrite_write_refs, Stage3Error};

use super::fixtures::*;

const STRUCT_S: usize = 7;

#[test]
fn write_ref_on_borrow_loc_temp_becomes_let_rebind() {
    // let r = &x; *r = 5;
    let stmts = vec![let_borrow_loc("r", "x"), eval_write_ref("r", lit_u64(5))];
    let mut program = one_fn_program(
        stmts,
        Expr::Unit,
        vec![param("x", Type::UInt(64))],
        Type::Unit,
    );
    rewrite_write_refs(&mut program).unwrap();

    let stmts = &body_of(&program).stmts;
    assert_eq!(stmts.len(), 2);

    // First stmt: the BorrowLoc -- untouched.
    match &stmts[0] {
        Stmt::Let { pattern, value } => {
            assert_eq!(pattern, &vec![Some(VarId::from("r"))]);
            assert_eq!(value, &Expr::BorrowLoc(VarId::from("x")));
        }
        other => panic!("expected Stmt::Let, got {:?}", other),
    }

    // Second stmt: Stmt::Eval(WriteRef) became Stmt::Let { value: WriteRef }
    match &stmts[1] {
        Stmt::Let { pattern, value } => {
            assert_eq!(pattern, &vec![Some(VarId::from("r"))]);
            match value {
                Expr::WriteRef {
                    reference,
                    value: v,
                } => {
                    assert_eq!(**reference, Expr::Var(VarId::from("r")));
                    assert_eq!(**v, lit_u64(5));
                }
                other => panic!("expected Expr::WriteRef value, got {:?}", other),
            }
        }
        other => panic!("expected Stmt::Let, got {:?}", other),
    }
}

#[test]
fn write_ref_on_borrow_field_temp_becomes_let_rebind() {
    let stmts = vec![
        let_borrow_loc("r0", "x"),
        let_borrow_field("r1", STRUCT_S, 0, Expr::Var(VarId::from("r0"))),
        eval_write_ref("r1", lit_u64(7)),
    ];
    let mut program = one_fn_program(
        stmts,
        Expr::Unit,
        vec![param("x", Type::UInt(64))],
        Type::Unit,
    );
    rewrite_write_refs(&mut program).unwrap();

    let stmts = &body_of(&program).stmts;
    assert_eq!(stmts.len(), 3);
    match &stmts[2] {
        Stmt::Let { pattern, value: _ } => {
            assert_eq!(pattern, &vec![Some(VarId::from("r1"))]);
        }
        other => panic!("expected Stmt::Let rebind of r1, got {:?}", other),
    }
}

#[test]
fn non_var_reference_rejects() {
    // WriteRef with a non-Var reference (e.g. inline BorrowLoc).
    let stmts = vec![Stmt::Eval(Expr::WriteRef {
        reference: Box::new(Expr::BorrowLoc(VarId::from("x"))),
        value: Box::new(lit_u64(5)),
    })];
    let mut program = one_fn_program(
        stmts,
        Expr::Unit,
        vec![param("x", Type::UInt(64))],
        Type::Unit,
    );
    let err = rewrite_write_refs(&mut program).unwrap_err();
    assert_eq!(err, Stage3Error::WriteRefNonVar { function: 0 });
}

#[test]
fn native_function_left_untouched() {
    // Obsolete: natives now live in program.natives.decls, not
    // program.functions; stages walk only functions, so this
    // behavior is structurally guaranteed.
}

#[test]
fn no_op_when_no_write_ref_present() {
    let stmts = vec![let_borrow_loc("r", "x")];
    let mut program = one_fn_program(
        stmts.clone(),
        Expr::Unit,
        vec![param("x", Type::UInt(64))],
        Type::Unit,
    );
    let before = program.clone();
    rewrite_write_refs(&mut program).unwrap();
    assert_eq!(program, before);
}

#[test]
fn idempotent_run_twice() {
    let stmts = vec![let_borrow_loc("r", "x"), eval_write_ref("r", lit_u64(5))];
    let mut program = one_fn_program(
        stmts,
        Expr::Unit,
        vec![param("x", Type::UInt(64))],
        Type::Unit,
    );
    rewrite_write_refs(&mut program).unwrap();
    let after_once = program.clone();
    rewrite_write_refs(&mut program).unwrap();
    assert_eq!(program, after_once);
}
