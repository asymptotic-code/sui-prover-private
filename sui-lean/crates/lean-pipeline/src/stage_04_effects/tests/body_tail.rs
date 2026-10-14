//! Stage 4 body-tail augmentation tests.

use crate::ir::{Block, BlockTail, Effects, Expr, MatchArm, Stmt, Type, VarId};
use crate::stage_04_effects::common::WORLD_VAR;
use crate::stage_04_effects::{
    augment_body_tails, augment_call_sites, augment_signatures, ensure_world_struct,
};

use super::fixtures::*;

#[test]
fn impure_unit_return_falls_off_becomes_singleton_tuple() {
    let f = func(
        "f",
        sig(Vec::new(), Type::Unit),
        body(Vec::new(), Expr::Unit),
        FuncOpts::default(),
    );
    let mut program = program_with(vec![(0, f)]);
    let world_id = ensure_world_struct(&mut program);
    let needs_world = crate::stage_04_effects::common::compute_needs_world(&program);

    augment_signatures(&mut program, world_id, &needs_world).unwrap();
    let needs_world = crate::stage_04_effects::common::compute_needs_world(&program);

    augment_body_tails(&mut program, world_id, &needs_world).unwrap();
    let f_body = body_of(&program, 0);
    match &f_body.tail {
        BlockTail::Value(Expr::Tuple(items)) => {
            assert_eq!(items.len(), 1);
            assert!(matches!(&items[0], Expr::Var(v) if v.as_ref() == WORLD_VAR));
        }
        other => panic!("expected Tuple([Var(world)]), got {:?}", other),
    }
}

#[test]
fn impure_int_return_appends_world_to_tail() {
    let f = func(
        "f",
        sig(Vec::new(), Type::UInt(64)),
        body(Vec::new(), lit_u64(42)),
        FuncOpts::default(),
    );
    let mut program = program_with(vec![(0, f)]);
    let world_id = ensure_world_struct(&mut program);
    let needs_world = crate::stage_04_effects::common::compute_needs_world(&program);

    augment_signatures(&mut program, world_id, &needs_world).unwrap();
    let needs_world = crate::stage_04_effects::common::compute_needs_world(&program);

    augment_body_tails(&mut program, world_id, &needs_world).unwrap();
    let f_body = body_of(&program, 0);
    match &f_body.tail {
        BlockTail::Value(Expr::Tuple(items)) => {
            assert_eq!(items.len(), 2);
            // First item is the original 42.
            assert!(matches!(
                &items[0],
                Expr::Const(crate::ir::Const::UInt { value, .. }) if *value == ethnum::U256::from(42u64)
            ));
            assert!(matches!(&items[1], Expr::Var(v) if v.as_ref() == WORLD_VAR));
        }
        other => panic!("expected Tuple([42, Var(world)]), got {:?}", other),
    }
}

#[test]
fn top_level_unit_if_preserves_effect_and_returns_selected_world() {
    let f = func(
        "f",
        sig(vec![param("c", Type::Bool)], Type::Unit),
        Block {
            stmts: Vec::new(),
            tail: BlockTail::Value(Expr::If {
                cond: Box::new(Expr::Var("c".into())),
                then_branch: Box::new(Block {
                    stmts: vec![Stmt::Eval(Expr::Call {
                        fun: 1,
                        type_args: Vec::new(),
                        args: Vec::new(),
                    })],
                    tail: BlockTail::Value(Expr::Unit),
                }),
                else_branch: Box::new(Block {
                    stmts: Vec::new(),
                    tail: BlockTail::Value(Expr::Unit),
                }),
            }),
        },
        FuncOpts::default(),
    );
    let mut program = program_with_natives(
        vec![(0, f)],
        vec![(1, native_impure("touch_world", Vec::new(), Type::Unit))],
    );
    let world_id = ensure_world_struct(&mut program);
    let needs_world = crate::stage_04_effects::common::compute_needs_world(&program);
    augment_signatures(&mut program, world_id, &needs_world).unwrap();
    let needs_world = crate::stage_04_effects::common::compute_needs_world(&program);
    augment_call_sites(&mut program, &needs_world).unwrap();
    augment_body_tails(&mut program, world_id, &needs_world).unwrap();

    let BlockTail::Value(Expr::If {
        then_branch,
        else_branch,
        ..
    }) = &program.functions[&0].body.tail
    else {
        panic!("Unit-valued If must remain the function-exit dispatcher")
    };
    assert!(matches!(
        &then_branch.tail,
        BlockTail::Value(Expr::Tuple(items))
            if matches!(&items[..], [Expr::Var(v)] if v.as_ref() == WORLD_VAR)
    ));
    assert!(matches!(
        &else_branch.tail,
        BlockTail::Value(Expr::Tuple(items))
            if matches!(&items[..], [Expr::Var(v)] if v.as_ref() == WORLD_VAR)
    ));
    crate::stage_04_effects::postcondition::check(&program, world_id)
        .expect("Stage 4 accepts the Unit-valued World exits");

    crate::stage_05_ssa::run(&mut program).expect("rename Unit-valued World exits");
    let function = &program.functions[&0];
    let incoming_world = function
        .signature
        .params
        .last()
        .expect("world parameter")
        .var
        .clone();
    let BlockTail::Value(Expr::If {
        then_branch,
        else_branch,
        ..
    }) = &function.body.tail
    else {
        panic!("SSA must preserve the function-exit If")
    };
    let Stmt::Let { pattern, .. } = &then_branch.stmts[0] else {
        panic!("world call must bind its returned state")
    };
    let selected_world = pattern
        .last()
        .and_then(Option::as_ref)
        .expect("world result binder");
    assert_ne!(selected_world, &incoming_world);
    assert!(matches!(
        &then_branch.tail,
        BlockTail::Value(Expr::Tuple(items))
            if items == &vec![Expr::Var(selected_world.clone())]
    ));
    assert!(matches!(
        &else_branch.tail,
        BlockTail::Value(Expr::Tuple(items))
            if items == &vec![Expr::Var(incoming_world)]
    ));
}

#[test]
fn top_level_if_returns_the_world_selected_by_its_arm() {
    let f = func(
        "f",
        sig(vec![param("c", Type::Bool)], Type::UInt(64)),
        Block {
            stmts: Vec::new(),
            tail: BlockTail::Value(Expr::If {
                cond: Box::new(Expr::Var("c".into())),
                then_branch: Box::new(Block {
                    stmts: vec![Stmt::Eval(Expr::Call {
                        fun: 1,
                        type_args: Vec::new(),
                        args: Vec::new(),
                    })],
                    tail: BlockTail::Value(lit_u64(7)),
                }),
                else_branch: Box::new(Block {
                    stmts: Vec::new(),
                    tail: BlockTail::Value(lit_u64(8)),
                }),
            }),
        },
        FuncOpts::default(),
    );
    let mut program = program_with_natives(
        vec![(0, f)],
        vec![(1, native_impure("touch_world", Vec::new(), Type::Unit))],
    );
    let world_id = ensure_world_struct(&mut program);
    let needs_world = crate::stage_04_effects::common::compute_needs_world(&program);
    augment_signatures(&mut program, world_id, &needs_world).unwrap();
    let needs_world = crate::stage_04_effects::common::compute_needs_world(&program);
    augment_call_sites(&mut program, &needs_world).unwrap();
    augment_body_tails(&mut program, world_id, &needs_world).unwrap();

    // Keeping World outside the If as `Tuple([If, world])` would resolve the
    // incoming parameter after Stage 5 restores the selected arm's scope.
    let BlockTail::Value(Expr::If {
        then_branch,
        else_branch,
        ..
    }) = &program.functions[&0].body.tail
    else {
        panic!("world-carrying If must remain at the function-exit position")
    };
    assert!(matches!(
        &then_branch.tail,
        BlockTail::Value(Expr::Tuple(items))
            if matches!(items.last(), Some(Expr::Var(v)) if v.as_ref() == WORLD_VAR)
    ));
    assert!(matches!(
        &else_branch.tail,
        BlockTail::Value(Expr::Tuple(items))
            if matches!(items.last(), Some(Expr::Var(v)) if v.as_ref() == WORLD_VAR)
    ));

    let after_first = program.functions[&0].body.clone();
    augment_body_tails(&mut program, world_id, &needs_world).unwrap();
    assert_eq!(program.functions[&0].body, after_first);
    crate::stage_04_effects::postcondition::check(&program, world_id)
        .expect("Stage 4 accepts the per-arm If World exits");

    crate::stage_05_ssa::run(&mut program).expect("construct SSA for world-carrying If");
    let function = &program.functions[&0];
    let incoming_world = function
        .signature
        .params
        .last()
        .expect("world parameter")
        .var
        .clone();
    let BlockTail::Value(Expr::If {
        then_branch,
        else_branch,
        ..
    }) = &function.body.tail
    else {
        panic!("SSA must preserve the world-carrying If")
    };
    let Stmt::Let { pattern, .. } = &then_branch.stmts[0] else {
        panic!("world call must bind its returned state")
    };
    let selected_world = pattern
        .last()
        .and_then(Option::as_ref)
        .expect("world result binder");
    assert_ne!(selected_world, &incoming_world);
    assert!(matches!(
        &then_branch.tail,
        BlockTail::Value(Expr::Tuple(items))
            if items.last() == Some(&Expr::Var(selected_world.clone()))
    ));
    assert!(matches!(
        &else_branch.tail,
        BlockTail::Value(Expr::Tuple(items))
            if items.last() == Some(&Expr::Var(incoming_world))
    ));
}

#[test]
fn top_level_match_carries_world_inside_each_value_arm() {
    let f = func(
        "f",
        sig(
            vec![param(
                "choice",
                Type::Struct {
                    struct_id: 9,
                    type_args: Vec::new(),
                },
            )],
            Type::UInt(64),
        ),
        Block {
            stmts: Vec::new(),
            tail: BlockTail::Value(Expr::Match {
                struct_id: 9,
                selector: Box::new(Expr::Var("choice".into())),
                cases: vec![
                    MatchArm {
                        variant: 0,
                        bindings: Vec::new(),
                        body: Box::new(Block {
                            stmts: vec![Stmt::Eval(Expr::Call {
                                fun: 1,
                                type_args: Vec::new(),
                                args: Vec::new(),
                            })],
                            tail: BlockTail::Value(lit_u64(7)),
                        }),
                    },
                    MatchArm {
                        variant: 1,
                        bindings: Vec::new(),
                        body: Box::new(Block {
                            stmts: Vec::new(),
                            tail: BlockTail::Value(lit_u64(8)),
                        }),
                    },
                ],
            }),
        },
        FuncOpts::default(),
    );
    let mut program = program_with_natives(
        vec![(0, f)],
        vec![(1, native_impure("touch_world", Vec::new(), Type::Unit))],
    );
    program.structs.insert(
        9,
        crate::ir::Struct {
            module_id: 0,
            name: "Choice".into(),
            qualified_name: "0x0::m::Choice".into(),
            type_params: Vec::new(),
            fields: Vec::new(),
            variants: Some(vec![
                crate::ir::Variant {
                    name: "Left".into(),
                    tag: 0,
                    fields: Vec::new(),
                },
                crate::ir::Variant {
                    name: "Right".into(),
                    tag: 1,
                    fields: Vec::new(),
                },
            ]),
            is_native: false,
        },
    );
    let world_id = ensure_world_struct(&mut program);
    let needs_world = crate::stage_04_effects::common::compute_needs_world(&program);
    augment_signatures(&mut program, world_id, &needs_world).unwrap();
    let needs_world = crate::stage_04_effects::common::compute_needs_world(&program);
    augment_call_sites(&mut program, &needs_world).unwrap();
    augment_body_tails(&mut program, world_id, &needs_world).unwrap();

    let BlockTail::Value(Expr::Match { cases, .. }) = &program.functions[&0].body.tail else {
        panic!("world-carrying Match must remain at the function-exit position")
    };
    assert!(cases.iter().all(|case| matches!(
        &case.body.tail,
        BlockTail::Value(Expr::Tuple(items))
            if matches!(items.last(), Some(Expr::Var(v)) if v.as_ref() == WORLD_VAR)
    )));
    crate::stage_04_effects::postcondition::check(&program, world_id)
        .expect("Stage 4 accepts the per-arm Match World exits");

    crate::stage_05_ssa::run(&mut program).expect("construct SSA for world-carrying Match");
    let function = &program.functions[&0];
    let incoming_world = function
        .signature
        .params
        .last()
        .expect("world parameter")
        .var
        .clone();
    let BlockTail::Value(Expr::Match { cases, .. }) = &function.body.tail else {
        panic!("SSA must preserve the world-carrying Match")
    };
    let Stmt::Let { pattern, .. } = &cases[0].body.stmts[0] else {
        panic!("world call must bind its returned state")
    };
    let selected_world = pattern
        .last()
        .and_then(Option::as_ref)
        .expect("world result binder");
    assert_ne!(selected_world, &incoming_world);
    assert!(matches!(
        &cases[0].body.tail,
        BlockTail::Value(Expr::Tuple(items))
            if items.last() == Some(&Expr::Var(selected_world.clone()))
    ));
    assert!(matches!(
        &cases[1].body.tail,
        BlockTail::Value(Expr::Tuple(items))
            if items.last() == Some(&Expr::Var(incoming_world))
    ));
}

#[test]
fn return_in_if_arm_gets_augmented() {
    // fn f(c: bool): u64 { if c { return 5 } else { 7 } }
    let f = func(
        "f",
        sig(vec![param("c", Type::Bool)], Type::UInt(64)),
        Block {
            stmts: Vec::new(),
            tail: BlockTail::Value(Expr::If {
                cond: Box::new(Expr::Var(VarId::from("c"))),
                then_branch: Box::new(Block {
                    stmts: Vec::new(),
                    tail: BlockTail::Return(Box::new(lit_u64(5))),
                }),
                else_branch: Box::new(Block {
                    stmts: Vec::new(),
                    tail: BlockTail::Value(lit_u64(7)),
                }),
            }),
        },
        FuncOpts::default(),
    );
    let mut program = program_with(vec![(0, f)]);
    let world_id = ensure_world_struct(&mut program);
    let needs_world = crate::stage_04_effects::common::compute_needs_world(&program);

    augment_signatures(&mut program, world_id, &needs_world).unwrap();
    let needs_world = crate::stage_04_effects::common::compute_needs_world(&program);

    augment_body_tails(&mut program, world_id, &needs_world).unwrap();
    let f_body = body_of(&program, 0);
    let BlockTail::Value(Expr::If {
        then_branch,
        else_branch,
        ..
    }) = &f_body.tail
    else {
        panic!("top-level If must remain the function-exit dispatcher")
    };
    match &then_branch.tail {
        BlockTail::Return(v) => match v.as_ref() {
            Expr::Tuple(items) => {
                assert_eq!(items.len(), 2);
                assert!(matches!(&items[1], Expr::Var(v) if v.as_ref() == WORLD_VAR));
            }
            other => panic!("expected Return(Tuple), got {:?}", other),
        },
        other => panic!("expected Return tail, got {:?}", other),
    }
    assert!(matches!(
        &else_branch.tail,
        BlockTail::Value(Expr::Tuple(items))
            if items.len() == 2
                && matches!(&items[1], Expr::Var(v) if v.as_ref() == WORLD_VAR)
    ));
}

#[test]
fn if_carried_by_return_augments_each_live_exit() {
    let f = func(
        "f",
        sig(vec![param("c", Type::Bool)], Type::UInt(64)),
        Block {
            stmts: Vec::new(),
            tail: BlockTail::Return(Box::new(Expr::If {
                cond: Box::new(Expr::Var("c".into())),
                then_branch: Box::new(Block {
                    stmts: Vec::new(),
                    tail: BlockTail::Value(lit_u64(7)),
                }),
                else_branch: Box::new(Block {
                    stmts: Vec::new(),
                    tail: BlockTail::Value(lit_u64(8)),
                }),
            })),
        },
        FuncOpts::default(),
    );
    let mut program = program_with(vec![(0, f)]);
    let world_id = ensure_world_struct(&mut program);
    let needs_world = crate::stage_04_effects::common::compute_needs_world(&program);
    augment_signatures(&mut program, world_id, &needs_world).unwrap();
    let needs_world = crate::stage_04_effects::common::compute_needs_world(&program);
    augment_body_tails(&mut program, world_id, &needs_world).unwrap();

    let BlockTail::Return(value) = &program.functions[&0].body.tail else {
        panic!("explicit Return must remain explicit")
    };
    let Expr::If {
        then_branch,
        else_branch,
        ..
    } = value.as_ref()
    else {
        panic!("Return must carry the exit-dispatching If directly")
    };
    for branch in [then_branch, else_branch] {
        assert!(matches!(
            &branch.tail,
            BlockTail::Value(Expr::Tuple(items))
                if items.len() == 2
                    && matches!(&items[1], Expr::Var(v) if v.as_ref() == WORLD_VAR)
        ));
    }
}

#[test]
fn break_tail_not_augmented() {
    // A While body with a Break inside. The break carries a value
    // that stage 5 will eventually replace with loop_state; stage 4
    // must NOT touch it.
    let f = func(
        "f",
        sig(Vec::new(), Type::Unit),
        Block {
            stmts: vec![Stmt::Eval(Expr::While {
                header: Box::new(Block {
                    stmts: Vec::new(),
                    tail: BlockTail::Value(Expr::Unit),
                }),
                cond: Box::new(Expr::Const(crate::ir::Const::Bool(true))),
                body: Box::new(Block {
                    stmts: Vec::new(),
                    tail: BlockTail::Break {
                        level: 0,
                        value: Box::new(Expr::Unit),
                    },
                }),
                iter_locals: Vec::new(),
                header_exit_locals: Vec::new(),
                live_out: vec![],
            })],
            tail: BlockTail::Value(Expr::Unit),
        },
        FuncOpts::default(),
    );
    let mut program = program_with(vec![(0, f)]);
    let world_id = ensure_world_struct(&mut program);
    let needs_world = crate::stage_04_effects::common::compute_needs_world(&program);

    augment_signatures(&mut program, world_id, &needs_world).unwrap();
    let needs_world = crate::stage_04_effects::common::compute_needs_world(&program);

    augment_body_tails(&mut program, world_id, &needs_world).unwrap();
    let f_body = body_of(&program, 0);
    // Top-level fall-off wrapped.
    assert!(matches!(&f_body.tail, BlockTail::Value(Expr::Tuple(_))));
    // Break inside While body NOT wrapped.
    match &f_body.stmts[0] {
        Stmt::Eval(Expr::While { body, .. }) => match &body.tail {
            BlockTail::Break { value, .. } => {
                assert!(matches!(value.as_ref(), Expr::Unit));
            }
            other => panic!("expected Break tail, got {:?}", other),
        },
        other => panic!("expected Stmt::Eval(While), got {:?}", other),
    }
}

#[test]
fn abort_tail_not_augmented() {
    // The aborting arm remains untouched while the live arm returns World.
    let f = func(
        "f",
        sig(Vec::new(), Type::UInt(64)),
        Block {
            stmts: Vec::new(),
            tail: BlockTail::Value(Expr::If {
                cond: Box::new(Expr::Const(crate::ir::Const::Bool(true))),
                then_branch: Box::new(Block {
                    stmts: Vec::new(),
                    tail: BlockTail::Abort {
                        code: Box::new(lit_u64(7)),
                    },
                }),
                else_branch: Box::new(Block {
                    stmts: Vec::new(),
                    tail: BlockTail::Value(lit_u64(42)),
                }),
            }),
        },
        FuncOpts::default(),
    );
    let mut program = program_with(vec![(0, f)]);
    let world_id = ensure_world_struct(&mut program);
    let needs_world = crate::stage_04_effects::common::compute_needs_world(&program);

    augment_signatures(&mut program, world_id, &needs_world).unwrap();
    let needs_world = crate::stage_04_effects::common::compute_needs_world(&program);

    augment_body_tails(&mut program, world_id, &needs_world).unwrap();
    let f_body = body_of(&program, 0);
    let BlockTail::Value(Expr::If {
        then_branch,
        else_branch,
        ..
    }) = &f_body.tail
    else {
        panic!("top-level If must remain the function-exit dispatcher")
    };
    match &then_branch.tail {
        BlockTail::Abort { code } => {
            assert!(matches!(
                code.as_ref(),
                Expr::Const(crate::ir::Const::UInt { .. })
            ));
        }
        other => panic!("expected Abort, got {:?}", other),
    }
    assert!(matches!(
        &else_branch.tail,
        BlockTail::Value(Expr::Tuple(items))
            if items.len() == 2
                && matches!(&items[1], Expr::Var(v) if v.as_ref() == WORLD_VAR)
    ));
}

#[test]
fn pure_function_tail_untouched() {
    let f = func(
        "f",
        sig(Vec::new(), Type::UInt(64)),
        body(Vec::new(), lit_u64(42)),
        FuncOpts {
            effects: Effects::PURE,
            ..Default::default()
        },
    );
    let mut program = program_with(vec![(0, f)]);
    let world_id = ensure_world_struct(&mut program);
    let needs_world = crate::stage_04_effects::common::compute_needs_world(&program);

    augment_body_tails(&mut program, world_id, &needs_world).unwrap();
    let f_body = body_of(&program, 0);
    assert!(matches!(&f_body.tail, BlockTail::Value(Expr::Const(_))));
}

#[test]
fn idempotent_two_runs() {
    let f = func(
        "f",
        sig(Vec::new(), Type::UInt(64)),
        body(Vec::new(), lit_u64(42)),
        FuncOpts::default(),
    );
    let mut program = program_with(vec![(0, f)]);
    let world_id = ensure_world_struct(&mut program);
    let needs_world = crate::stage_04_effects::common::compute_needs_world(&program);

    augment_signatures(&mut program, world_id, &needs_world).unwrap();
    let needs_world = crate::stage_04_effects::common::compute_needs_world(&program);

    augment_body_tails(&mut program, world_id, &needs_world).unwrap();
    let after_first = body_of(&program, 0).clone();
    let needs_world = crate::stage_04_effects::common::compute_needs_world(&program);

    augment_body_tails(&mut program, world_id, &needs_world).unwrap();
    assert_eq!(*body_of(&program, 0), after_first);
}

// Suppress unused-import warning.
#[allow(unused_imports)]
use Block as _;
#[allow(unused_imports)]
use MatchArm as _;
