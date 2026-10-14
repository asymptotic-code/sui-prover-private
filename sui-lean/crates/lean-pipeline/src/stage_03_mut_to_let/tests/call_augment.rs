//! Tests for Transform 6: call-site destructure augmentation.

use crate::ir::{Expr, Stmt, Type, VarId};
use crate::stage_03_mut_to_let::{augment_call_sites, run, Stage3Error};

use super::fixtures::*;

/// Build a callee + caller pair. The callee takes one `&mut` param.
fn callee_with_one_mut(name: &str, ret: Type) -> crate::ir::Function {
    func(
        name,
        sig(
            vec![param("p", mut_ref(Type::UInt(64), Type::UInt(64)))],
            ret,
        ),
        body(vec![], Expr::Unit),
        FuncOpts::default(),
    )
}

#[test]
fn call_with_mut_arg_via_stmt_eval_becomes_let_with_mut_pattern() {
    let callee = callee_with_one_mut("g", Type::Unit);
    let caller_body = vec![Stmt::Eval(Expr::Call {
        fun: 1,
        type_args: Vec::new(),
        args: vec![Expr::Var(VarId::from("v"))],
    })];
    let caller = func(
        "f",
        sig(
            vec![param("v", mut_ref(Type::UInt(64), Type::UInt(64)))],
            Type::Unit,
        ),
        body(caller_body, Expr::Unit),
        FuncOpts::default(),
    );
    let mut program = program_with(vec![(0, caller), (1, callee)]);
    augment_call_sites(&mut program).unwrap();

    match &program.functions[&0].body.stmts[0] {
        Stmt::Let { pattern, value } => {
            assert_eq!(pattern, &vec![Some(VarId::from("v"))]);
            assert!(matches!(value, Expr::Call { fun: 1, .. }));
        }
        other => panic!("expected Stmt::Let after augmentation, got {:?}", other),
    }
}

#[test]
fn call_with_captured_return_pattern_extends() {
    let callee = callee_with_one_mut("g", Type::UInt(64));
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
            Type::UInt(64),
        ),
        body(caller_body, Expr::Var(VarId::from("r"))),
        FuncOpts::default(),
    );
    let mut program = program_with(vec![(0, caller), (1, callee)]);
    augment_call_sites(&mut program).unwrap();

    match &program.functions[&0].body.stmts[0] {
        Stmt::Let { pattern, .. } => {
            // pattern: [Some(r), Some(v)]
            assert_eq!(pattern.len(), 2);
            assert_eq!(pattern[0], Some(VarId::from("r")));
            assert_eq!(pattern[1], Some(VarId::from("v")));
        }
        other => panic!("expected augmented Stmt::Let, got {:?}", other),
    }
}

#[test]
fn call_with_no_mut_params_unchanged() {
    let callee = func(
        "g",
        sig(vec![param("p", Type::UInt(64))], Type::Unit),
        body(vec![], Expr::Unit),
        FuncOpts::default(),
    );
    let caller_body = vec![Stmt::Eval(Expr::Call {
        fun: 1,
        type_args: Vec::new(),
        args: vec![lit_u64(0)],
    })];
    let caller = func(
        "f",
        sig(vec![], Type::Unit),
        body(caller_body, Expr::Unit),
        FuncOpts::default(),
    );
    let mut program = program_with(vec![(0, caller), (1, callee)]);
    let before = program.clone();
    augment_call_sites(&mut program).unwrap();
    assert_eq!(program, before);
}

#[test]
fn multiple_mut_args_destructure_in_param_order() {
    let callee = func(
        "g",
        sig(
            vec![
                param("p", mut_ref(Type::UInt(64), Type::UInt(64))),
                param("q", Type::Bool),
                param("r", mut_ref(Type::Bool, Type::Bool)),
            ],
            Type::Unit,
        ),
        body(vec![], Expr::Unit),
        FuncOpts::default(),
    );
    let caller_body = vec![Stmt::Eval(Expr::Call {
        fun: 1,
        type_args: Vec::new(),
        args: vec![
            Expr::Var(VarId::from("v")),
            Expr::Const(crate::ir::Const::Bool(true)),
            Expr::Var(VarId::from("w")),
        ],
    })];
    let caller = func(
        "f",
        sig(
            vec![
                param("v", mut_ref(Type::UInt(64), Type::UInt(64))),
                param("w", mut_ref(Type::Bool, Type::Bool)),
            ],
            Type::Unit,
        ),
        body(caller_body, Expr::Unit),
        FuncOpts::default(),
    );
    let mut program = program_with(vec![(0, caller), (1, callee)]);
    augment_call_sites(&mut program).unwrap();

    match &program.functions[&0].body.stmts[0] {
        Stmt::Let { pattern, .. } => {
            // mut args at indices 0 and 2 -> pattern [Some(v), Some(w)]
            assert_eq!(pattern.len(), 2);
            assert_eq!(pattern[0], Some(VarId::from("v")));
            assert_eq!(pattern[1], Some(VarId::from("w")));
        }
        other => panic!("expected Stmt::Let, got {:?}", other),
    }
}

#[test]
fn non_var_at_mut_arg_position_rejects() {
    let callee = callee_with_one_mut("g", Type::Unit);
    let caller_body = vec![Stmt::Eval(Expr::Call {
        fun: 1,
        type_args: Vec::new(),
        args: vec![lit_u64(42)], // not a Var, but the param is &mut
    })];
    let caller = func(
        "f",
        sig(vec![], Type::Unit),
        body(caller_body, Expr::Unit),
        FuncOpts::default(),
    );
    let mut program = program_with(vec![(0, caller), (1, callee)]);
    let err = augment_call_sites(&mut program).unwrap_err();
    assert_eq!(err, Stage3Error::CallMutArgNonVar { function: 0 });
}

#[test]
fn idempotent_run_twice() {
    let callee = callee_with_one_mut("g", Type::Unit);
    let caller_body = vec![Stmt::Eval(Expr::Call {
        fun: 1,
        type_args: Vec::new(),
        args: vec![Expr::Var(VarId::from("v"))],
    })];
    let caller = func(
        "f",
        sig(
            vec![param("v", mut_ref(Type::UInt(64), Type::UInt(64)))],
            Type::Unit,
        ),
        body(caller_body, Expr::Unit),
        FuncOpts::default(),
    );
    let mut program = program_with(vec![(0, caller), (1, callee)]);
    augment_call_sites(&mut program).unwrap();
    let after_once = program.clone();
    augment_call_sites(&mut program).unwrap();
    assert_eq!(program, after_once);
}

#[test]
fn native_callee_with_mut_is_still_augmented() {
    // Native functions are skipped for body rewriting, but their
    // signatures still drive call-site augmentation at the caller.
    let callee = func(
        "n",
        sig(
            vec![param("p", mut_ref(Type::UInt(64), Type::UInt(64)))],
            Type::Unit,
        ),
        empty_body(),
        FuncOpts {
            native: true,
            module: 0,
        },
    );
    let caller_body = vec![Stmt::Eval(Expr::Call {
        fun: 1,
        type_args: Vec::new(),
        args: vec![Expr::Var(VarId::from("v"))],
    })];
    let caller = func(
        "f",
        sig(
            vec![param("v", mut_ref(Type::UInt(64), Type::UInt(64)))],
            Type::Unit,
        ),
        body(caller_body, Expr::Unit),
        FuncOpts::default(),
    );
    let mut program = program_with(vec![(0, caller), (1, callee)]);
    augment_call_sites(&mut program).unwrap();

    match &program.functions[&0].body.stmts[0] {
        Stmt::Let { pattern, .. } => {
            assert_eq!(pattern, &vec![Some(VarId::from("v"))]);
        }
        other => panic!("expected augmented Stmt::Let, got {:?}", other),
    }
}

#[test]
fn direct_tail_call_to_mut_callee_rejects() {
    // Stage 2 should always lift Calls to mut-taking callees into a
    // Stmt::Let. If a `tail: Value(Call(mut-taking))` slips through,
    // call_augment must reject -- otherwise body_tail (which runs
    // after) would wrap the Call in a Tuple, hiding it from any
    // subsequent caller-side augmentation. The order
    // `call_augment then body_tail` plus the
    // `CallInExpressionPosition` check guards against this.
    let callee = callee_with_one_mut("g", Type::Unit);
    let caller = func(
        "f",
        sig(
            vec![param("v", mut_ref(Type::UInt(64), Type::UInt(64)))],
            Type::Unit,
        ),
        body(
            vec![],
            // direct tail value: Call(g, [Var(v)]) -- mut callee not lifted
            Expr::Call {
                fun: 1,
                type_args: Vec::new(),
                args: vec![Expr::Var(VarId::from("v"))],
            },
        ),
        FuncOpts::default(),
    );
    let mut program = program_with(vec![(0, caller), (1, callee)]);
    let err = augment_call_sites(&mut program).unwrap_err();
    assert_eq!(err, Stage3Error::CallInExpressionPosition { function: 0 });
}

#[test]
fn stage3_rejects_tail_mutating_call_before_any_rewrite() {
    let callee = callee_with_one_mut("g", Type::Unit);
    let caller = func(
        "f",
        sig(
            vec![param("v", mut_ref(Type::UInt(64), Type::UInt(64)))],
            Type::Unit,
        ),
        body(
            vec![],
            Expr::Call {
                fun: 1,
                type_args: vec![],
                args: vec![Expr::Var("v".into())],
            },
        ),
        FuncOpts::default(),
    );
    let mut program = program_with(vec![(0, caller), (1, callee)]);
    let before = program.clone();

    assert_eq!(
        run(&mut program),
        Err(Stage3Error::CallInExpressionPosition { function: 0 })
    );
    assert_eq!(program, before, "shape rejection must precede all rewrites");
}

#[test]
fn stage3_rejects_mutating_call_nested_in_compound_expression() {
    let callee = callee_with_one_mut("g", Type::Unit);
    let caller = func(
        "f",
        sig(
            vec![param("v", mut_ref(Type::UInt(64), Type::UInt(64)))],
            Type::Unit,
        ),
        body(
            vec![],
            Expr::Tuple(vec![
                Expr::Call {
                    fun: 1,
                    type_args: vec![],
                    args: vec![Expr::Var("v".into())],
                },
                Expr::Unit,
            ]),
        ),
        FuncOpts::default(),
    );
    let mut program = program_with(vec![(0, caller), (1, callee)]);
    let before = program.clone();

    assert_eq!(
        run(&mut program),
        Err(Stage3Error::CallInExpressionPosition { function: 0 })
    );
    assert_eq!(program, before, "nested-call rejection must be atomic");
}

// Note: `Stage3Error::CallInExpressionPosition` is now reachable via
// the direct-tail-Call case (`tail: Value(Call(mut, ..))` without a
// surrounding Stmt::Let). The stage entry precheck walks all expression
// children, so a mut-taking Call inside Tuple, Pack, BinOp, call arguments,
// conditions, or any other compound position is rejected before mutation.
