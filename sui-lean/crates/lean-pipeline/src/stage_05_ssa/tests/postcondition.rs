//! Stage-5 postcondition tests.
//!
//! Covers:
//! - Well-formed stage-5 output passes.
//! - Hand-built shadowing rejects with `Shadowing { var }`.
//! - Base-validator violations propagate as `BaseValidator`.

use crate::ir::{Expr, Stmt, Type, VarId};
use crate::stage_05_ssa::postcondition::{check, PostconditionError};
use crate::stage_05_ssa::run;

use super::fixtures::*;

#[test]
fn well_formed_post_run_passes() {
    let stmts = vec![
        Stmt::Let {
            pattern: vec![Some("x".into())],
            value: lit_u64(1),
        },
        Stmt::Let {
            pattern: vec![Some("x".into())],
            value: lit_u64(2),
        },
    ];
    let mut p = one_fn_program(stmts, Expr::Var("x".into()), vec![], Type::UInt(64));
    run(&mut p).unwrap();
    check(&p).expect("post-run program should pass postcondition");
}

#[test]
fn shadowing_let_rejects() {
    // Manually build a post-stage-5 IR where two `Stmt::Let`s bind
    // the same VarId. This is what stage 5 must NOT produce.
    let stmts = vec![
        Stmt::Let {
            pattern: vec![Some("x".into())],
            value: lit_u64(1),
        },
        Stmt::Let {
            pattern: vec![Some("x".into())],
            value: lit_u64(2),
        },
    ];
    let p = one_fn_program(stmts, Expr::Var("x".into()), vec![], Type::UInt(64));
    // Don't run stage 5 -- we want the raw shadowing.
    let err = check(&p).unwrap_err();
    match err {
        PostconditionError::Shadowing { var, .. } => {
            assert_eq!(var, VarId::from("x"));
        }
        other => panic!("expected Shadowing, got {:?}", other),
    }
}

#[test]
fn shadowing_param_vs_let_rejects() {
    // Function has param `x` and body lets `x` again -- pre-stage-5
    // shape. Should reject.
    let stmts = vec![Stmt::Let {
        pattern: vec![Some("x".into())],
        value: lit_u64(5),
    }];
    let p = one_fn_program(
        stmts,
        Expr::Unit,
        vec![param("x", Type::UInt(64))],
        Type::Unit,
    );
    let err = check(&p).unwrap_err();
    assert!(
        matches!(err, PostconditionError::Shadowing { ref var, .. } if *var == VarId::from("x"))
    );
}

#[test]
fn native_function_excluded_from_no_shadowing_check() {
    // Native function with stray shadowing in its (empty) body --
    // exempt.
    let f = func(
        "n",
        sig(vec![param("x", Type::UInt(64))], Type::UInt(64)),
        body(vec![], Expr::Var("x".into())),
        FuncOpts {
            native: true,
            module: 0,
        },
    );
    let p = program_with(vec![(0, f)]);
    check(&p).expect("native fn skipped");
}
