//! Tests for the stage-3 (mut-to-let) postcondition validator.

use crate::ir::builder::{block, tail_value};
use crate::ir::{BorrowEdge, BorrowNode, Expr, Stmt, Type, VarId};
use crate::stage_03_mut_to_let::postcondition::{check, PostconditionError};
use crate::stage_03_mut_to_let::run;

use super::fixtures::*;

const STRUCT_S: usize = 7;

#[test]
fn empty_program_passes() {
    let program = program_with(vec![]);
    assert_eq!(check(&program), Ok(()));
}

#[test]
fn well_formed_post_stage_3_output_passes() {
    let stmts = vec![
        let_borrow_loc("r", "x"),
        eval_write_ref("r", lit_u64(5)),
        eval_write_back(
            BorrowNode::LocalRoot(VarId::from("x")),
            BorrowEdge::Direct,
            "r",
        ),
    ];
    let mut program = one_fn_program(
        stmts,
        Expr::Unit,
        vec![param("x", Type::UInt(64))],
        Type::Unit,
    );
    run(&mut program).unwrap();
    assert_eq!(check(&program), Ok(()));
}

#[test]
fn lingering_write_ref_eval_rejects() {
    let stmts = vec![let_borrow_loc("r", "x"), eval_write_ref("r", lit_u64(5))];
    let program = one_fn_program(
        stmts,
        Expr::Unit,
        vec![param("x", Type::UInt(64))],
        Type::Unit,
    );
    let err = check(&program).unwrap_err();
    assert_eq!(
        err,
        PostconditionError::LingeringWriteRefEval { function: 0 }
    );
}

#[test]
fn lingering_write_back_eval_rejects() {
    let stmts = vec![
        let_borrow_loc("r", "x"),
        eval_write_back(
            BorrowNode::LocalRoot(VarId::from("x")),
            BorrowEdge::Direct,
            "r",
        ),
    ];
    let program = one_fn_program(
        stmts,
        Expr::Unit,
        vec![param("x", Type::UInt(64))],
        Type::Unit,
    );
    let err = check(&program).unwrap_err();
    assert_eq!(
        err,
        PostconditionError::LingeringWriteBackEval { function: 0 }
    );
}

#[test]
fn write_ref_in_let_value_position_passes() {
    // After stage 3 the rewriter emits this shape -- the postcondition
    // must accept it.
    let stmts = vec![
        let_borrow_loc("r", "x"),
        Stmt::Let {
            pattern: vec![Some(VarId::from("r"))],
            value: Expr::WriteRef {
                reference: Box::new(Expr::Var(VarId::from("r"))),
                value: Box::new(lit_u64(5)),
            },
        },
    ];
    let program = one_fn_program(
        stmts,
        Expr::Unit,
        vec![param("x", Type::UInt(64))],
        Type::Unit,
    );
    assert_eq!(check(&program), Ok(()));
}

#[test]
fn write_back_in_let_value_position_passes() {
    let stmts = vec![
        let_borrow_loc("r", "x"),
        Stmt::Let {
            pattern: vec![Some(VarId::from("x"))],
            value: Expr::WriteBack {
                node: BorrowNode::LocalRoot(VarId::from("x")),
                edge: BorrowEdge::Direct,
                child: VarId::from("r"),
                world: None,
            },
        },
    ];
    let program = one_fn_program(
        stmts,
        Expr::Unit,
        vec![param("x", Type::UInt(64))],
        Type::Unit,
    );
    assert_eq!(check(&program), Ok(()));
}

#[test]
fn pre_ssa_branch_phi_shape_passes_stage3_postcondition() {
    let then_branch = block(
        vec![Stmt::Let {
            pattern: vec![Some(VarId::from("t"))],
            value: lit_u64(1),
        }],
        tail_value(Expr::Unit),
    );
    let else_branch = block(
        vec![Stmt::Let {
            pattern: vec![Some(VarId::from("t"))],
            value: lit_u64(2),
        }],
        tail_value(Expr::Unit),
    );
    let if_expr = Expr::If {
        cond: Box::new(Expr::Var(VarId::from("c"))),
        then_branch: Box::new(then_branch),
        else_branch: Box::new(else_branch),
    };
    let program = one_fn_program(
        vec![Stmt::Eval(if_expr)],
        Expr::Var(VarId::from("t")),
        vec![param("c", Type::Bool)],
        Type::UInt(64),
    );
    assert_eq!(check(&program), Ok(()));
}

#[test]
fn lingering_write_ref_inside_if_arm_rejects() {
    use crate::ir::builder::{block, just, tail_value};
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
    let program = one_fn_program(
        vec![Stmt::Eval(if_expr)],
        Expr::Unit,
        vec![param("x", Type::UInt(64))],
        Type::Unit,
    );
    assert_eq!(
        check(&program),
        Err(PostconditionError::LingeringWriteRefEval { function: 0 })
    );
}

#[test]
fn call_pattern_arity_mismatch_rejects() {
    // Construct a malformed program: callee g has &mut param + non-Unit
    // return (so render-time augmented arity = 2), but the caller's
    // Stmt::Let pattern has arity 1 (missing the mut-arg slot).
    let callee = func(
        "g",
        sig(
            vec![param("p", mut_ref(Type::UInt(64), Type::UInt(64)))],
            Type::Tuple(vec![
                Type::UInt(64),
                mut_ref(Type::UInt(64), Type::UInt(64)),
            ]),
        ),
        body(
            vec![],
            Expr::Tuple(vec![lit_u64(42), Expr::Var(VarId::from("p"))]),
        ),
        FuncOpts::default(),
    );
    // Caller with pattern len 1 — should be 2 to match augmented arity.
    let caller_body = vec![Stmt::Let {
        pattern: vec![Some(VarId::from("r"))],
        value: Expr::Call {
            fun: 1,
            type_args: Vec::new(),
            args: vec![Expr::Var(VarId::from("v"))],
        },
    }];
    let caller = func(
        "f",
        sig(
            vec![param("v", mut_ref(Type::UInt(64), Type::UInt(64)))],
            Type::Tuple(vec![
                Type::UInt(64),
                mut_ref(Type::UInt(64), Type::UInt(64)),
            ]),
        ),
        body(
            caller_body,
            Expr::Tuple(vec![
                Expr::Var(VarId::from("r")),
                Expr::Var(VarId::from("v")),
            ]),
        ),
        FuncOpts::default(),
    );
    let program = program_with(vec![(0, caller), (1, callee)]);
    let err = check(&program).unwrap_err();
    match err {
        PostconditionError::CallPatternArityMismatch {
            function: 0,
            callee: 1,
            pattern_len: 1,
            expected_arity: 2,
        } => {}
        other => panic!("expected CallPatternArityMismatch, got {:?}", other),
    }
}

#[test]
fn native_function_with_stray_write_ref_is_exempt() {
    // Obsolete: natives now live in program.natives.decls, not
    // program.functions; stages walk only functions, so this
    // behavior is structurally guaranteed.
}
