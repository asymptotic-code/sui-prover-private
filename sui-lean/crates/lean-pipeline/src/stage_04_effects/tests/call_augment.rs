//! Stage 4 call-site augmentation tests.

use crate::ir::path::PathStep;
use crate::ir::{Block, BlockTail, Effects, Expr, QuantDomain, QuantifierKind, Stmt, Type, VarId};
use crate::stage_04_effects::common::WORLD_VAR;
use crate::stage_04_effects::{augment_call_sites, augment_signatures, ensure_world_struct};

use super::fixtures::*;

#[test]
fn eval_call_to_native_impure_becomes_let_with_world() {
    let native = native_impure("event::emit", vec![param("e", Type::UInt(64))], Type::Unit);
    let caller = func(
        "caller",
        sig(vec![param("e", Type::UInt(64))], Type::Unit),
        body(
            vec![Stmt::Eval(Expr::Call {
                fun: 0,
                type_args: Vec::new(),
                args: vec![Expr::Var(VarId::from("e"))],
            })],
            Expr::Unit,
        ),
        FuncOpts::default(),
    );
    let mut program = program_with_natives(vec![(1, caller)], vec![(0, native)]);
    let world_id = ensure_world_struct(&mut program);
    let needs_world = crate::stage_04_effects::common::compute_needs_world(&program);

    augment_signatures(&mut program, world_id, &needs_world).unwrap();
    let needs_world = crate::stage_04_effects::common::compute_needs_world(&program);

    augment_call_sites(&mut program, &needs_world).unwrap();

    let caller_body = body_of(&program, 1);
    assert_eq!(caller_body.stmts.len(), 1);
    match &caller_body.stmts[0] {
        Stmt::Let {
            pattern,
            value: Expr::Call { args, .. },
        } => {
            // Pattern: [Some(world)] (head_count = 0 since native
            // event::emit IR ret is Unit, augmented arity = 1).
            assert_eq!(pattern.len(), 1);
            assert!(matches!(&pattern[0], Some(v) if v.as_ref() == WORLD_VAR));
            // Args: [e, world].
            assert_eq!(args.len(), 2);
            assert!(matches!(args.last(), Some(Expr::Var(v)) if v.as_ref() == WORLD_VAR));
        }
        other => panic!("expected Stmt::Let with Call, got {:?}", other),
    }
}

#[test]
fn let_call_to_native_impure_with_return_augments_pattern() {
    let native = native_impure(
        "transfer::receive",
        vec![param("token", Type::UInt(64))],
        Type::UInt(64),
    );
    let caller = func(
        "caller",
        sig(vec![param("t", Type::UInt(64))], Type::UInt(64)),
        body(
            vec![Stmt::Let {
                pattern: vec![Some(VarId::from("v"))],
                value: Expr::Call {
                    fun: 0,
                    type_args: Vec::new(),
                    args: vec![Expr::Var(VarId::from("t"))],
                },
            }],
            Expr::Var(VarId::from("v")),
        ),
        FuncOpts::default(),
    );
    let mut program = program_with_natives(vec![(1, caller)], vec![(0, native)]);
    let world_id = ensure_world_struct(&mut program);
    let needs_world = crate::stage_04_effects::common::compute_needs_world(&program);

    augment_signatures(&mut program, world_id, &needs_world).unwrap();
    let needs_world = crate::stage_04_effects::common::compute_needs_world(&program);

    augment_call_sites(&mut program, &needs_world).unwrap();

    let caller_body = body_of(&program, 1);
    match &caller_body.stmts[0] {
        Stmt::Let {
            pattern,
            value: Expr::Call { args, .. },
        } => {
            // Native augmented arity = raw_arity(1) + 1 = 2.
            // Pattern: [Some(v), Some(world)].
            assert_eq!(pattern.len(), 2);
            assert!(matches!(&pattern[0], Some(v) if v.as_ref() == "v"));
            assert!(matches!(&pattern[1], Some(v) if v.as_ref() == WORLD_VAR));
            // Args: [t, world].
            assert_eq!(args.len(), 2);
            assert!(matches!(args.last(), Some(Expr::Var(v)) if v.as_ref() == WORLD_VAR));
        }
        other => panic!("expected Stmt::Let with Call, got {:?}", other),
    }
}

#[test]
fn eval_call_to_user_impure_becomes_let_with_world() {
    // Two user functions: callee is Impure (Unit return); caller is
    // Impure and calls callee.
    let callee = func(
        "g",
        sig(Vec::new(), Type::Unit),
        body(Vec::new(), Expr::Unit),
        FuncOpts::default(),
    );
    let caller = func(
        "f",
        sig(Vec::new(), Type::Unit),
        body(
            vec![Stmt::Eval(Expr::Call {
                fun: 0,
                type_args: Vec::new(),
                args: Vec::new(),
            })],
            Expr::Unit,
        ),
        FuncOpts::default(),
    );
    let mut program = program_with(vec![(0, callee), (1, caller)]);
    let world_id = ensure_world_struct(&mut program);
    let needs_world = crate::stage_04_effects::common::compute_needs_world(&program);

    augment_signatures(&mut program, world_id, &needs_world).unwrap();
    let needs_world = crate::stage_04_effects::common::compute_needs_world(&program);

    augment_call_sites(&mut program, &needs_world).unwrap();

    let caller_body = body_of(&program, 1);
    match &caller_body.stmts[0] {
        Stmt::Let {
            pattern,
            value: Expr::Call { args, .. },
        } => {
            // Non-native callee was augmented by Transform B:
            // return_type became Tuple([World]); arity = 1.
            // head_count = 0, so pattern = [Some(world)].
            assert_eq!(pattern.len(), 1);
            assert!(matches!(&pattern[0], Some(v) if v.as_ref() == WORLD_VAR));
            assert_eq!(args.len(), 1);
            assert!(matches!(args.last(), Some(Expr::Var(v)) if v.as_ref() == WORLD_VAR));
        }
        other => panic!("expected Stmt::Let with Call, got {:?}", other),
    }
}

#[test]
fn call_to_pure_callee_unchanged() {
    let callee = func(
        "g",
        sig(Vec::new(), Type::UInt(64)),
        body(Vec::new(), lit_u64(42)),
        FuncOpts {
            effects: Effects::PURE,
            ..Default::default()
        },
    );
    let caller = func(
        "f",
        sig(Vec::new(), Type::Unit),
        body(
            vec![Stmt::Let {
                pattern: vec![Some(VarId::from("v"))],
                value: Expr::Call {
                    fun: 0,
                    type_args: Vec::new(),
                    args: Vec::new(),
                },
            }],
            Expr::Unit,
        ),
        FuncOpts::default(),
    );
    let mut program = program_with(vec![(0, callee), (1, caller)]);
    let world_id = ensure_world_struct(&mut program);
    let needs_world = crate::stage_04_effects::common::compute_needs_world(&program);

    augment_signatures(&mut program, world_id, &needs_world).unwrap();
    let needs_world = crate::stage_04_effects::common::compute_needs_world(&program);

    augment_call_sites(&mut program, &needs_world).unwrap();

    let caller_body = body_of(&program, 1);
    match &caller_body.stmts[0] {
        Stmt::Let { pattern, .. } => {
            // Pattern unchanged: just [Some(v)].
            assert_eq!(pattern.len(), 1);
            assert!(matches!(&pattern[0], Some(v) if v.as_ref() == "v"));
        }
        other => panic!("expected Stmt::Let, got {:?}", other),
    }
}

#[test]
fn chain_of_native_calls_threads_world_through_each() {
    let emit = native_impure("event::emit", Vec::new(), Type::Unit);
    let transfer = native_impure("transfer::transfer", Vec::new(), Type::Unit);
    let caller = func(
        "f",
        sig(Vec::new(), Type::Unit),
        body(
            vec![
                Stmt::Eval(Expr::Call {
                    fun: 0,
                    type_args: Vec::new(),
                    args: Vec::new(),
                }),
                Stmt::Eval(Expr::Call {
                    fun: 1,
                    type_args: Vec::new(),
                    args: Vec::new(),
                }),
            ],
            Expr::Unit,
        ),
        FuncOpts::default(),
    );
    let mut program = program_with_natives(vec![(2, caller)], vec![(0, emit), (1, transfer)]);
    let world_id = ensure_world_struct(&mut program);
    let needs_world = crate::stage_04_effects::common::compute_needs_world(&program);

    augment_signatures(&mut program, world_id, &needs_world).unwrap();
    let needs_world = crate::stage_04_effects::common::compute_needs_world(&program);

    augment_call_sites(&mut program, &needs_world).unwrap();

    let caller_body = body_of(&program, 2);
    assert_eq!(caller_body.stmts.len(), 2);
    for stmt in &caller_body.stmts {
        match stmt {
            Stmt::Let {
                pattern,
                value: Expr::Call { args, .. },
            } => {
                assert!(matches!(&pattern[0], Some(v) if v.as_ref() == WORLD_VAR));
                assert!(matches!(args.last(), Some(Expr::Var(v)) if v.as_ref() == WORLD_VAR));
            }
            other => panic!("expected Stmt::Let with Call, got {:?}", other),
        }
    }
}

#[test]
fn call_in_expression_position_rejects() {
    let native = native_impure("event::emit", Vec::new(), Type::UInt(64));
    let caller = func(
        "f",
        sig(Vec::new(), Type::Unit),
        body(
            Vec::new(),
            // Tuple containing an Impure call -- not in Stmt::Eval / Stmt::Let::value
            // top-level position.
            Expr::Tuple(vec![Expr::Call {
                fun: 0,
                type_args: Vec::new(),
                args: Vec::new(),
            }]),
        ),
        FuncOpts::default(),
    );
    let mut program = program_with_natives(vec![(1, caller)], vec![(0, native)]);
    let world_id = ensure_world_struct(&mut program);
    let needs_world = crate::stage_04_effects::common::compute_needs_world(&program);

    augment_signatures(&mut program, world_id, &needs_world).unwrap();
    let result = augment_call_sites(&mut program, &needs_world);
    assert!(matches!(
        result,
        Err(crate::stage_04_effects::Stage4Error::CallInExpressionPosition { .. })
    ));
}

#[test]
fn idempotent_two_runs() {
    let native = native_impure("event::emit", Vec::new(), Type::Unit);
    let caller = func(
        "f",
        sig(Vec::new(), Type::Unit),
        body(
            vec![Stmt::Eval(Expr::Call {
                fun: 0,
                type_args: Vec::new(),
                args: Vec::new(),
            })],
            Expr::Unit,
        ),
        FuncOpts::default(),
    );
    let mut program = program_with_natives(vec![(1, caller)], vec![(0, native)]);
    let world_id = ensure_world_struct(&mut program);
    let needs_world = crate::stage_04_effects::common::compute_needs_world(&program);

    augment_signatures(&mut program, world_id, &needs_world).unwrap();
    let needs_world = crate::stage_04_effects::common::compute_needs_world(&program);

    augment_call_sites(&mut program, &needs_world).unwrap();
    let after_first = body_of(&program, 1).clone();
    let needs_world = crate::stage_04_effects::common::compute_needs_world(&program);

    augment_call_sites(&mut program, &needs_world).unwrap();
    assert_eq!(*body_of(&program, 1), after_first);
}

#[test]
fn quantifier_snapshot_hoists_world_read_from_path_operand() {
    let reader = native_with_effects("read_index", Vec::new(), Type::UInt(64), Effects::WORLD);
    let caller = func(
        "f",
        sig(Vec::new(), Type::Unit),
        body(
            Vec::new(),
            Expr::Quantifier {
                kind: QuantifierKind::Forall,
                binder: "x".into(),
                binder_type: Type::UInt(64),
                domain: QuantDomain::Unbounded,
                body: Box::new(Block::just(Expr::Borrow {
                    step: PathStep::VecIndex(Box::new(Expr::Call {
                        fun: 0,
                        type_args: Vec::new(),
                        args: Vec::new(),
                    })),
                    base: Box::new(Expr::Unit),
                })),
            },
        ),
        FuncOpts {
            effects: Effects::WORLD,
            ..Default::default()
        },
    );
    let mut program = program_with_natives(vec![(1, caller)], vec![(0, reader)]);
    let world_id = ensure_world_struct(&mut program);
    let needs_world = crate::stage_04_effects::common::compute_needs_world(&program);
    augment_signatures(&mut program, world_id, &needs_world).unwrap();
    let needs_world = crate::stage_04_effects::common::compute_needs_world(&program);
    augment_call_sites(&mut program, &needs_world).unwrap();

    let Expr::Quantifier { body, .. } = (match &program.functions[&1].body.tail {
        BlockTail::Value(expr) => expr,
        tail => panic!("expected value tail, got {tail:?}"),
    }) else {
        panic!("expected quantifier")
    };
    let [Stmt::Let {
        pattern,
        value: Expr::Call { args, .. },
    }] = body.stmts.as_slice()
    else {
        panic!("expected one snapshot let, got {:?}", body.stmts)
    };
    assert!(matches!(pattern.as_slice(), [Some(_), None]));
    assert!(matches!(args.last(), Some(Expr::Var(var)) if var.as_ref() == WORLD_VAR));
    assert!(matches!(
        &body.tail,
        BlockTail::Value(Expr::Borrow {
            step: PathStep::VecIndex(index),
            ..
        }) if matches!(index.as_ref(), Expr::Var(_))
    ));

    let after_first = program.functions[&1].body.clone();
    augment_call_sites(&mut program, &needs_world).unwrap();
    assert_eq!(program.functions[&1].body, after_first);
}

#[test]
fn world_read_in_quantifier_domain_is_not_skipped() {
    let reader = native_with_effects(
        "read_collection",
        Vec::new(),
        Type::Vector(Box::new(Type::UInt(64))),
        Effects::WORLD,
    );
    let caller = func(
        "f",
        sig(Vec::new(), Type::Unit),
        body(
            Vec::new(),
            Expr::Quantifier {
                kind: QuantifierKind::Forall,
                binder: "x".into(),
                binder_type: Type::UInt(64),
                domain: QuantDomain::Collection(Box::new(Expr::Call {
                    fun: 0,
                    type_args: Vec::new(),
                    args: Vec::new(),
                })),
                body: Box::new(Block::just(Expr::Const(crate::ir::Const::Bool(true)))),
            },
        ),
        FuncOpts {
            effects: Effects::WORLD,
            ..Default::default()
        },
    );
    let mut program = program_with_natives(vec![(1, caller)], vec![(0, reader)]);
    let world_id = ensure_world_struct(&mut program);
    let needs_world = crate::stage_04_effects::common::compute_needs_world(&program);
    augment_signatures(&mut program, world_id, &needs_world).unwrap();
    let needs_world = crate::stage_04_effects::common::compute_needs_world(&program);

    assert!(matches!(
        augment_call_sites(&mut program, &needs_world),
        Err(crate::stage_04_effects::Stage4Error::CallInExpressionPosition { function: 1 })
    ));
}

// Suppress unused-import warning when only one helper is used.
#[allow(unused_imports)]
use BlockTail as _;
