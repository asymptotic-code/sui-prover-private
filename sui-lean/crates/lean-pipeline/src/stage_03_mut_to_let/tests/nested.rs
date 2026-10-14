//! Tests that rewriting descends into If / Match / While arms.

use crate::ir::builder::{block, just, tail_value};
use crate::ir::{BorrowEdge, BorrowNode, Expr, MatchArm, Stmt, Type, VarId};
use crate::stage_03_mut_to_let::{rewrite_write_backs, rewrite_write_refs};

use super::fixtures::*;

const STRUCT_S: usize = 7;

#[test]
fn write_ref_inside_if_then_arm_is_rewritten() {
    let then_branch = block(
        vec![let_borrow_loc("r", "x"), eval_write_ref("r", lit_u64(5))],
        tail_value(Expr::Unit),
    );
    let else_branch = just(Expr::Unit);
    let if_expr = Expr::If {
        cond: Box::new(Expr::Const(crate::ir::Const::Bool(true))),
        then_branch: Box::new(then_branch),
        else_branch: Box::new(else_branch),
    };
    let mut program = one_fn_program(
        vec![Stmt::Eval(if_expr)],
        Expr::Unit,
        vec![param("x", Type::UInt(64))],
        Type::Unit,
    );
    rewrite_write_refs(&mut program).unwrap();

    if let Stmt::Eval(Expr::If { then_branch, .. }) = &body_of(&program).stmts[0] {
        assert_eq!(then_branch.stmts.len(), 2);
        match &then_branch.stmts[1] {
            Stmt::Let { pattern, value } => {
                assert_eq!(pattern, &vec![Some(VarId::from("r"))]);
                assert!(matches!(value, Expr::WriteRef { .. }));
            }
            other => panic!("expected Stmt::Let inside if then-arm, got {:?}", other),
        }
    } else {
        panic!("expected If expr in body stmts");
    }
}

#[test]
fn write_back_inside_match_arm_is_rewritten() {
    let arm_body = block(
        vec![
            let_borrow_loc("r", "x"),
            eval_write_back(
                BorrowNode::LocalRoot(VarId::from("x")),
                BorrowEdge::Direct,
                "r",
            ),
        ],
        tail_value(Expr::Unit),
    );
    let match_expr = Expr::Match {
        struct_id: 0,
        selector: Box::new(Expr::Var(VarId::from("x"))),
        cases: vec![MatchArm {
            variant: 0,
            bindings: Vec::new(),
            body: Box::new(arm_body),
        }],
    };
    let mut program = one_fn_program(
        vec![Stmt::Eval(match_expr)],
        Expr::Unit,
        vec![param("x", Type::UInt(64))],
        Type::Unit,
    );
    rewrite_write_backs(&mut program).unwrap();

    if let Stmt::Eval(Expr::Match { cases, .. }) = &body_of(&program).stmts[0] {
        let arm = &cases[0];
        assert_eq!(arm.body.stmts.len(), 2);
        match &arm.body.stmts[1] {
            Stmt::Let { pattern, value } => {
                assert_eq!(pattern, &vec![Some(VarId::from("x"))]);
                assert!(matches!(value, Expr::WriteBack { .. }));
            }
            other => panic!("expected Stmt::Let rebind in match arm, got {:?}", other),
        }
    } else {
        panic!("expected Match expr in body stmts");
    }
}

#[test]
fn write_ref_inside_while_body_is_rewritten() {
    let loop_body = block(
        vec![let_borrow_loc("r", "x"), eval_write_ref("r", lit_u64(0))],
        crate::ir::BlockTail::Continue {
            level: 0,
            value: Box::new(Expr::Unit),
        },
    );
    let while_expr = Expr::While {
        header: Box::new(just(Expr::Unit)),
        cond: Box::new(Expr::Const(crate::ir::Const::Bool(false))),
        body: Box::new(loop_body),
        iter_locals: Vec::new(),
        header_exit_locals: Vec::new(),
        live_out: vec![],
    };
    let mut program = one_fn_program(
        vec![Stmt::Eval(while_expr)],
        Expr::Unit,
        vec![param("x", Type::UInt(64))],
        Type::Unit,
    );
    rewrite_write_refs(&mut program).unwrap();

    if let Stmt::Eval(Expr::While { body, .. }) = &body_of(&program).stmts[0] {
        assert_eq!(body.stmts.len(), 2);
        match &body.stmts[1] {
            Stmt::Let { pattern, .. } => {
                assert_eq!(pattern, &vec![Some(VarId::from("r"))]);
            }
            other => panic!("expected Stmt::Let inside while body, got {:?}", other),
        }
    } else {
        panic!("expected While expr in body stmts");
    }
}

#[test]
fn write_ref_at_block_tail_via_if_value_is_rewritten() {
    // tail = If(c) { r = &x; *r = 5; r } else { unit }
    let then_branch = block(
        vec![let_borrow_loc("r", "x"), eval_write_ref("r", lit_u64(5))],
        tail_value(Expr::Var(VarId::from("r"))),
    );
    let else_branch = block(vec![], tail_value(Expr::Unit));
    let if_expr = Expr::If {
        cond: Box::new(Expr::Const(crate::ir::Const::Bool(true))),
        then_branch: Box::new(then_branch),
        else_branch: Box::new(else_branch),
    };
    let mut program = one_fn_program(
        vec![],
        if_expr,
        vec![param("x", Type::UInt(64))],
        // Non-unit return for type-shape consistency; doesn't affect the test.
        mut_ref(Type::UInt(64), Type::UInt(64)),
    );
    rewrite_write_refs(&mut program).unwrap();

    let tail = &body_of(&program).tail;
    if let crate::ir::BlockTail::Value(Expr::If { then_branch, .. }) = tail {
        match &then_branch.stmts[1] {
            Stmt::Let { pattern, value } => {
                assert_eq!(pattern, &vec![Some(VarId::from("r"))]);
                assert!(matches!(value, Expr::WriteRef { .. }));
            }
            other => panic!("expected Stmt::Let in then-arm, got {:?}", other),
        }
    } else {
        panic!("expected If at tail");
    }
}
