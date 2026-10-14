//! Stage 4 postcondition validator tests.

use crate::ir::builder::{block, tail_value, write_back};
use crate::ir::path::PathStep;
use crate::ir::{
    Block, BlockTail, Effects, Expr, Field, FunctionKind, MatchArm, QuantDomain, QuantifierKind,
    Stmt, Struct, Type, VarId, Variant,
};
use crate::stage_04_effects::common::WORLD_VAR;
use crate::stage_04_effects::postcondition::{check, PostconditionError};
use crate::stage_04_effects::{
    augment_body_tails, augment_call_sites, augment_signatures, ensure_world_struct, world_type,
};

use super::fixtures::*;

#[test]
fn well_formed_passes() {
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

    augment_call_sites(&mut program, &needs_world).unwrap();
    let needs_world = crate::stage_04_effects::common::compute_needs_world(&program);

    augment_body_tails(&mut program, world_id, &needs_world).unwrap();
    check(&program, world_id).expect("postcondition should hold");
}

#[test]
fn pre_ssa_branch_phi_shape_passes_stage4_postcondition() {
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
    let f = func(
        "f",
        sig(vec![param("c", Type::Bool)], Type::UInt(64)),
        body(
            vec![Stmt::Eval(Expr::If {
                cond: Box::new(Expr::Var(VarId::from("c"))),
                then_branch: Box::new(then_branch),
                else_branch: Box::new(else_branch),
            })],
            Expr::Var(VarId::from("t")),
        ),
        FuncOpts {
            effects: Effects::PURE,
            ..Default::default()
        },
    );
    let mut program = program_with(vec![(0, f)]);
    let world_id = ensure_world_struct(&mut program);

    check(&program, world_id).expect("pre-SSA branch phi shape should pass");
}

#[test]
fn impure_missing_world_param_rejects() {
    let f = func(
        "f",
        sig(Vec::new(), Type::Tuple(vec![Type::UInt(64)])),
        body(Vec::new(), Expr::Tuple(vec![lit_u64(42)])),
        FuncOpts::default(),
    );
    let mut program = program_with(vec![(0, f)]);
    let world_id = ensure_world_struct(&mut program);
    // Skip augment_signatures -- the function will have wrong shape.
    let result = check(&program, world_id);
    assert!(matches!(
        result,
        Err(PostconditionError::MalformedSignature { function: 0 })
    ));
}

#[test]
fn impure_missing_world_in_return_rejects() {
    // Function has `world` param but return type is Tuple([u64])
    // (missing trailing world slot).
    let f = func(
        "f",
        sig(
            vec![param(WORLD_VAR, world_type(0))],
            Type::Tuple(vec![Type::UInt(64)]),
        ),
        body(
            Vec::new(),
            Expr::Tuple(vec![lit_u64(42), Expr::Var(VarId::from(WORLD_VAR))]),
        ),
        FuncOpts::default(),
    );
    let mut program = program_with(vec![(0, f)]);
    let world_id = ensure_world_struct(&mut program);
    // ensure_world_struct gave us a fresh id (likely 0), but the
    // function above hard-coded `0`. Adjust the function's param
    // type to match the actual world_id.
    program.functions.get_mut(&0).unwrap().signature.params[0].ty = world_type(world_id);
    let result = check(&program, world_id);
    assert!(matches!(
        result,
        Err(PostconditionError::MalformedSignature { function: 0 })
    ));
}

#[test]
fn pure_function_with_stray_world_param_rejects() {
    let f = func(
        "g",
        sig(vec![param(WORLD_VAR, world_type(0))], Type::UInt(64)),
        body(Vec::new(), lit_u64(42)),
        FuncOpts {
            effects: Effects::PURE,
            ..Default::default()
        },
    );
    let mut program = program_with(vec![(0, f)]);
    let world_id = ensure_world_struct(&mut program);
    program.functions.get_mut(&0).unwrap().signature.params[0].ty = world_type(world_id);
    let result = check(&program, world_id);
    assert!(matches!(
        result,
        Err(PostconditionError::WorldOnPureFunction { function: 0 })
    ));
}

#[test]
fn impure_with_call_missing_world_rejects() {
    let native = native_impure("event::emit", Vec::new(), Type::Unit);
    // Caller's Stmt::Let has Call(0) but no world threading.
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
    // Augment the body tail but skip call-site augmentation.
    let needs_world = crate::stage_04_effects::common::compute_needs_world(&program);

    augment_body_tails(&mut program, world_id, &needs_world).unwrap();
    let result = check(&program, world_id);
    assert!(matches!(
        result,
        Err(PostconditionError::LingeringUnthreadedCall { .. })
    ));
}

#[test]
fn impure_with_unwrapped_return_rejects() {
    // Function has correct signature (world param + world in return)
    // but body's top-level tail doesn't end in Var(world).
    let f = func(
        "f",
        sig(
            vec![param(WORLD_VAR, world_type(0))],
            Type::Tuple(vec![Type::UInt(64), world_type(0)]),
        ),
        body(Vec::new(), lit_u64(42)),
        FuncOpts::default(),
    );
    let mut program = program_with(vec![(0, f)]);
    let world_id = ensure_world_struct(&mut program);
    program.functions.get_mut(&0).unwrap().signature.params[0].ty = world_type(world_id);
    if let Type::Tuple(items) = &mut program.functions.get_mut(&0).unwrap().signature.return_type {
        items[1] = world_type(world_id);
    }
    let result = check(&program, world_id);
    assert!(matches!(
        result,
        Err(PostconditionError::ReturnMissingWorld { function: 0 })
    ));
}

#[test]
fn impure_tuple_ending_in_non_world_variable_rejects() {
    let f = func(
        "f",
        sig(
            vec![
                param(WORLD_VAR, world_type(0)),
                param("amount", Type::UInt(64)),
            ],
            Type::Tuple(vec![Type::UInt(64), world_type(0)]),
        ),
        body(
            Vec::new(),
            Expr::Tuple(vec![lit_u64(42), Expr::Var("amount".into())]),
        ),
        FuncOpts::default(),
    );
    let mut program = program_with(vec![(0, f)]);
    let world_id = ensure_world_struct(&mut program);
    let function = program.functions.get_mut(&0).unwrap();
    function.signature.params[0].ty = world_type(world_id);
    if let Type::Tuple(items) = &mut function.signature.return_type {
        items[1] = world_type(world_id);
    }

    assert!(matches!(
        check(&program, world_id),
        Err(PostconditionError::ReturnMissingWorld { function: 0 })
    ));
}

#[test]
fn world_routed_writeback_rejects_non_world_input() {
    let mut program = program_with(Vec::new());
    let world_id = ensure_world_struct(&mut program);
    let f = func(
        "f",
        sig(
            vec![
                param("parent", Type::UInt(64)),
                param("child", Type::UInt(64)),
                param("amount", Type::UInt(64)),
                param(WORLD_VAR, world_type(world_id)),
            ],
            Type::Tuple(vec![Type::UInt(64), world_type(world_id)]),
        ),
        body(
            vec![Stmt::Let {
                pattern: vec![Some("parent_1".into()), Some("world_1".into())],
                value: write_back("parent", "child", Some("amount")),
            }],
            Expr::Tuple(vec![
                Expr::Var("parent_1".into()),
                Expr::Var(WORLD_VAR.into()),
            ]),
        ),
        FuncOpts::default(),
    );
    program.functions.insert(0, f);

    let result = check(&program, world_id);
    assert!(
        matches!(
            result,
            Err(PostconditionError::MalformedWorldWriteBack { function: 0 })
        ),
        "unexpected result: {result:?}"
    );
}

#[test]
fn world_routed_writeback_rejects_discarded_world_result() {
    let mut program = program_with(Vec::new());
    let world_id = ensure_world_struct(&mut program);
    let f = func(
        "f",
        sig(
            vec![
                param("parent", Type::UInt(64)),
                param("child", Type::UInt(64)),
                param(WORLD_VAR, world_type(world_id)),
            ],
            Type::Tuple(vec![Type::UInt(64), world_type(world_id)]),
        ),
        body(
            vec![Stmt::Let {
                pattern: vec![Some("parent_1".into()), None],
                value: write_back("parent", "child", Some(WORLD_VAR)),
            }],
            Expr::Tuple(vec![
                Expr::Var("parent_1".into()),
                Expr::Var(WORLD_VAR.into()),
            ]),
        ),
        FuncOpts::default(),
    );
    program.functions.insert(0, f);

    assert!(matches!(
        check(&program, world_id),
        Err(PostconditionError::MalformedWorldWriteBack { function: 0 })
    ));
}

#[test]
fn impure_tail_call_without_world_return_rejects() {
    let callee = func(
        "scalar",
        sig(Vec::new(), Type::UInt(64)),
        body(Vec::new(), lit_u64(7)),
        FuncOpts {
            effects: Effects::PURE,
            ..Default::default()
        },
    );
    let caller = func(
        "caller",
        sig(
            vec![param(WORLD_VAR, world_type(0))],
            Type::Tuple(vec![Type::UInt(64), world_type(0)]),
        ),
        body(
            Vec::new(),
            Expr::Call {
                fun: 0,
                type_args: Vec::new(),
                args: Vec::new(),
            },
        ),
        FuncOpts::default(),
    );
    let mut program = program_with(vec![(0, callee), (1, caller)]);
    let world_id = ensure_world_struct(&mut program);
    let caller = program.functions.get_mut(&1).unwrap();
    caller.signature.params[0].ty = world_type(world_id);
    if let Type::Tuple(items) = &mut caller.signature.return_type {
        items[1] = world_type(world_id);
    }

    assert!(matches!(
        check(&program, world_id),
        Err(PostconditionError::ReturnMissingWorld { function: 1 })
    ));
}

#[test]
fn impure_unknown_tail_call_rejects() {
    let caller = func(
        "caller",
        sig(
            vec![param(WORLD_VAR, world_type(0))],
            Type::Tuple(vec![Type::UInt(64), world_type(0)]),
        ),
        body(
            Vec::new(),
            Expr::Call {
                fun: 99,
                type_args: Vec::new(),
                args: Vec::new(),
            },
        ),
        FuncOpts::default(),
    );
    let mut program = program_with(vec![(0, caller)]);
    let world_id = ensure_world_struct(&mut program);
    let caller = program.functions.get_mut(&0).unwrap();
    caller.signature.params[0].ty = world_type(world_id);
    if let Type::Tuple(items) = &mut caller.signature.return_type {
        items[1] = world_type(world_id);
    }

    assert!(matches!(
        check(&program, world_id),
        Err(PostconditionError::ReturnMissingWorld { function: 0 })
    ));
}

#[test]
fn ghost_slots_after_world_pass_for_tuple_variable_and_call_tails() {
    let mut program = program_with(Vec::new());
    let world_id = ensure_world_struct(&mut program);
    let return_type = Type::Tuple(vec![Type::UInt(64), world_type(world_id), Type::Bool]);
    let common_params = || {
        vec![
            param(WORLD_VAR, world_type(world_id)),
            param("ghost", Type::Bool),
        ]
    };

    program.functions.insert(
        0,
        func(
            "direct",
            sig(common_params(), return_type.clone()),
            body(
                Vec::new(),
                Expr::Tuple(vec![
                    lit_u64(1),
                    Expr::Var(WORLD_VAR.into()),
                    Expr::Var("ghost".into()),
                ]),
            ),
            FuncOpts::default(),
        ),
    );
    program.functions.insert(
        1,
        func(
            "variable",
            sig(common_params(), return_type.clone()),
            body(
                vec![Stmt::Let {
                    pattern: vec![Some("payload".into())],
                    value: Expr::Tuple(vec![
                        lit_u64(1),
                        Expr::Var(WORLD_VAR.into()),
                        Expr::Var("ghost".into()),
                    ]),
                }],
                Expr::Var("payload".into()),
            ),
            FuncOpts::default(),
        ),
    );
    program.functions.insert(
        2,
        func(
            "delegate",
            sig(common_params(), return_type.clone()),
            body(
                Vec::new(),
                Expr::Call {
                    fun: 0,
                    type_args: Vec::new(),
                    args: vec![Expr::Var(WORLD_VAR.into()), Expr::Var("ghost".into())],
                },
            ),
            FuncOpts::default(),
        ),
    );
    check(&program, world_id).expect("World stays valid before trailing ghost slots");
}

#[test]
fn impure_pre_ssa_type_error_keeps_known_world_parameter_type() {
    let mut program = program_with(Vec::new());
    let world_id = ensure_world_struct(&mut program);
    let carrier_id = world_id + 1;
    program.structs.insert(
        carrier_id,
        Struct {
            module_id: 0,
            name: "Carrier".into(),
            qualified_name: "MyProject::m::Carrier".into(),
            type_params: Vec::new(),
            fields: Vec::new(),
            variants: Some(vec![Variant {
                name: "Only".into(),
                tag: 0,
                fields: Vec::new(),
            }]),
            is_native: false,
        },
    );
    let carrier = || Expr::Pack {
        struct_id: carrier_id,
        type_args: Vec::new(),
        variant: Some(0),
        fields: Vec::new(),
    };
    let bind_merged = || Block {
        stmts: vec![Stmt::Let {
            pattern: vec![Some("merged".into())],
            value: carrier(),
        }],
        tail: BlockTail::Value(Expr::Unit),
    };
    let branch_merge = Stmt::Eval(Expr::If {
        cond: Box::new(Expr::Var("condition".into())),
        then_branch: Box::new(bind_merged()),
        else_branch: Box::new(bind_merged()),
    });
    let consume_merged = Stmt::Eval(Expr::Match {
        struct_id: carrier_id,
        selector: Box::new(Expr::Var("merged".into())),
        cases: vec![MatchArm {
            variant: 0,
            bindings: Vec::new(),
            body: Box::new(Block::just(Expr::Unit)),
        }],
    });
    let rebind_world = Stmt::Let {
        pattern: vec![Some(WORLD_VAR.into())],
        value: Expr::Call {
            fun: 1,
            type_args: Vec::new(),
            args: vec![Expr::Var(WORLD_VAR.into())],
        },
    };
    program.functions.insert(
        0,
        func(
            "pre_ssa",
            sig(
                vec![
                    param("condition", Type::Bool),
                    param(WORLD_VAR, world_type(world_id)),
                ],
                Type::Tuple(vec![Type::UInt(64), world_type(world_id)]),
            ),
            body(
                vec![rebind_world, branch_merge, consume_merged],
                Expr::Tuple(vec![lit_u64(1), Expr::Var(WORLD_VAR.into())]),
            ),
            FuncOpts::default(),
        ),
    );
    program.functions.insert(
        1,
        func(
            "thread_world",
            sig(
                vec![param(WORLD_VAR, world_type(world_id))],
                Type::Tuple(vec![world_type(world_id)]),
            ),
            body(Vec::new(), Expr::Tuple(vec![Expr::Var(WORLD_VAR.into())])),
            FuncOpts::default(),
        ),
    );

    check(&program, world_id)
        .expect("same-typed world rebindings survive an unrelated pre-SSA merge error");
}

#[test]
fn typed_walk_error_does_not_restore_a_conflicted_world_parameter() {
    let mut program = program_with(Vec::new());
    let world_id = ensure_world_struct(&mut program);
    let carrier_id = world_id + 1;
    program.structs.insert(
        carrier_id,
        Struct {
            module_id: 0,
            name: "Carrier".into(),
            qualified_name: "MyProject::m::Carrier".into(),
            type_params: Vec::new(),
            fields: Vec::new(),
            variants: Some(vec![Variant {
                name: "Only".into(),
                tag: 0,
                fields: Vec::new(),
            }]),
            is_native: false,
        },
    );
    let shadow_world = Stmt::Eval(Expr::If {
        cond: Box::new(Expr::Var("condition".into())),
        then_branch: Box::new(Block {
            stmts: vec![Stmt::Let {
                pattern: vec![Some(WORLD_VAR.into())],
                value: lit_u64(7),
            }],
            tail: BlockTail::Value(Expr::Var(WORLD_VAR.into())),
        }),
        else_branch: Box::new(Block::just(Expr::Unit)),
    });
    let carrier = || Expr::Pack {
        struct_id: carrier_id,
        type_args: Vec::new(),
        variant: Some(0),
        fields: Vec::new(),
    };
    let bind_merged = || Block {
        stmts: vec![Stmt::Let {
            pattern: vec![Some("merged".into())],
            value: carrier(),
        }],
        tail: BlockTail::Value(Expr::Unit),
    };
    let branch_merge = Stmt::Eval(Expr::If {
        cond: Box::new(Expr::Var("condition".into())),
        then_branch: Box::new(bind_merged()),
        else_branch: Box::new(bind_merged()),
    });
    let consume_merged = Stmt::Eval(Expr::Match {
        struct_id: carrier_id,
        selector: Box::new(Expr::Var("merged".into())),
        cases: vec![MatchArm {
            variant: 0,
            bindings: Vec::new(),
            body: Box::new(Block::just(Expr::Unit)),
        }],
    });
    program.functions.insert(
        0,
        func(
            "conflict_before_type_error",
            sig(
                vec![
                    param("condition", Type::Bool),
                    param(WORLD_VAR, world_type(world_id)),
                ],
                Type::Tuple(vec![Type::UInt(64), world_type(world_id)]),
            ),
            body(
                vec![shadow_world, branch_merge, consume_merged],
                Expr::Tuple(vec![lit_u64(1), Expr::Var(WORLD_VAR.into())]),
            ),
            FuncOpts::default(),
        ),
    );

    assert!(matches!(
        check(&program, world_id),
        Err(PostconditionError::ReturnMissingWorld { function: 0 })
    ));
}

#[test]
fn typed_walk_error_does_not_hide_a_later_world_parameter_rebind() {
    let mut program = program_with(Vec::new());
    let world_id = ensure_world_struct(&mut program);
    let carrier_id = world_id + 1;
    program.structs.insert(
        carrier_id,
        Struct {
            module_id: 0,
            name: "Carrier".into(),
            qualified_name: "MyProject::m::Carrier".into(),
            type_params: Vec::new(),
            fields: Vec::new(),
            variants: Some(vec![Variant {
                name: "Only".into(),
                tag: 0,
                fields: Vec::new(),
            }]),
            is_native: false,
        },
    );
    let carrier = || Expr::Pack {
        struct_id: carrier_id,
        type_args: Vec::new(),
        variant: Some(0),
        fields: Vec::new(),
    };
    let bind_merged = || Block {
        stmts: vec![Stmt::Let {
            pattern: vec![Some("merged".into())],
            value: carrier(),
        }],
        tail: BlockTail::Value(Expr::Unit),
    };
    let branch_merge = Stmt::Eval(Expr::If {
        cond: Box::new(Expr::Var("condition".into())),
        then_branch: Box::new(bind_merged()),
        else_branch: Box::new(bind_merged()),
    });
    let consume_merged = Stmt::Eval(Expr::Match {
        struct_id: carrier_id,
        selector: Box::new(Expr::Var("merged".into())),
        cases: vec![MatchArm {
            variant: 0,
            bindings: Vec::new(),
            body: Box::new(Block::just(Expr::Unit)),
        }],
    });
    let shadow_world = Stmt::Let {
        pattern: vec![Some(WORLD_VAR.into())],
        value: lit_u64(7),
    };
    program.functions.insert(
        0,
        func(
            "type_error_before_shadow",
            sig(
                vec![
                    param("condition", Type::Bool),
                    param(WORLD_VAR, world_type(world_id)),
                ],
                Type::Tuple(vec![Type::UInt(64), world_type(world_id)]),
            ),
            body(
                vec![branch_merge, consume_merged, shadow_world],
                Expr::Tuple(vec![lit_u64(1), Expr::Var(WORLD_VAR.into())]),
            ),
            FuncOpts::default(),
        ),
    );

    assert!(matches!(
        check(&program, world_id),
        Err(PostconditionError::ReturnMissingWorld { function: 0 })
    ));
}

#[test]
fn branch_local_world_type_cannot_bless_an_escaping_tail_variable() {
    let mut program = program_with(Vec::new());
    let world_id = ensure_world_struct(&mut program);
    let return_type = Type::Tuple(vec![Type::UInt(64), world_type(world_id)]);
    let bind_merged = |value| Block {
        stmts: vec![Stmt::Let {
            pattern: vec![Some("merged".into())],
            value,
        }],
        tail: BlockTail::Value(Expr::Unit),
    };
    let then_branch = bind_merged(Expr::Tuple(vec![lit_u64(1), Expr::Var(WORLD_VAR.into())]));
    let else_branch = bind_merged(Expr::Tuple(vec![lit_u64(2), lit_u64(3)]));
    program.functions.insert(
        0,
        func(
            "escaping_branch_local",
            sig(
                vec![
                    param("condition", Type::Bool),
                    param(WORLD_VAR, world_type(world_id)),
                ],
                return_type,
            ),
            body(
                vec![Stmt::Eval(Expr::If {
                    cond: Box::new(Expr::Var("condition".into())),
                    then_branch: Box::new(then_branch),
                    else_branch: Box::new(else_branch),
                })],
                Expr::Var("merged".into()),
            ),
            FuncOpts::default(),
        ),
    );

    assert!(matches!(
        check(&program, world_id),
        Err(PostconditionError::ReturnMissingWorld { function: 0 })
    ));
}

#[test]
fn fallback_branch_join_is_order_independent_for_world_rebindings() {
    for world_in_then_branch in [false, true] {
        let mut program = program_with(Vec::new());
        let world_id = ensure_world_struct(&mut program);
        let branch = |value| Block {
            stmts: vec![Stmt::Let {
                pattern: vec![Some("merged".into())],
                value,
            }],
            tail: BlockTail::Value(Expr::Unit),
        };
        let world_branch = branch(Expr::Var(WORLD_VAR.into()));
        let uint_branch = branch(lit_u64(7));
        let (then_branch, else_branch) = if world_in_then_branch {
            (world_branch, uint_branch)
        } else {
            (uint_branch, world_branch)
        };
        program.functions.insert(
            0,
            func(
                "branch_order",
                sig(
                    vec![
                        param("condition", Type::Bool),
                        param(WORLD_VAR, world_type(world_id)),
                    ],
                    Type::Tuple(vec![Type::UInt(64), world_type(world_id)]),
                ),
                body(
                    vec![
                        Stmt::Eval(Expr::If {
                            cond: Box::new(Expr::Var("condition".into())),
                            then_branch: Box::new(then_branch),
                            else_branch: Box::new(else_branch),
                        }),
                        Stmt::Let {
                            pattern: vec![Some(WORLD_VAR.into())],
                            value: Expr::Var("merged".into()),
                        },
                    ],
                    Expr::Tuple(vec![lit_u64(1), Expr::Var(WORLD_VAR.into())]),
                ),
                FuncOpts::default(),
            ),
        );

        assert!(matches!(
            check(&program, world_id),
            Err(PostconditionError::ReturnMissingWorld { function: 0 })
        ));
    }
}

#[test]
fn read_only_loop_helper_may_capture_world_without_returning_it() {
    let mut program = program_with(Vec::new());
    let world_id = ensure_world_struct(&mut program);
    let read_effects = Effects {
        aborts: crate::ir::AbortBit::Total,
        det: crate::ir::DetBit::Det,
        mutation: crate::ir::MutLevel::GlobalMut,
        world_writes: false,
    };
    let read = native_with_effects(
        "read",
        vec![param(WORLD_VAR, world_type(world_id))],
        Type::Tuple(vec![Type::UInt(64), world_type(world_id)]),
        read_effects,
    );
    program.natives.decls.insert(0, read);
    let mut helper = func(
        "f.while_0",
        sig(vec![param(WORLD_VAR, world_type(world_id))], Type::UInt(64)),
        body(
            vec![Stmt::Let {
                pattern: vec![Some("value".into()), Some("next_world".into())],
                value: Expr::Call {
                    fun: 0,
                    type_args: Vec::new(),
                    args: vec![Expr::Var(WORLD_VAR.into())],
                },
            }],
            Expr::Var("value".into()),
        ),
        FuncOpts {
            effects: Effects::PURE,
            ..Default::default()
        },
    );
    helper.kind = FunctionKind::LoopBody { parent: 2, slot: 0 };
    program.functions.insert(1, helper);

    check(&program, world_id).expect("read-only loop helper keeps its natural return type");
}

#[test]
fn buried_world_return_from_explicit_pure_callee_rejects() {
    let mut program = program_with(Vec::new());
    let world_id = ensure_world_struct(&mut program);
    let mut callee = func(
        "read_helper",
        sig(
            vec![param(WORLD_VAR, world_type(world_id))],
            Type::Tuple(vec![world_type(world_id)]),
        ),
        body(Vec::new(), Expr::Tuple(vec![Expr::Var(WORLD_VAR.into())])),
        FuncOpts {
            effects: Effects::PURE,
            ..Default::default()
        },
    );
    callee.explicit_pure = true;
    program.functions.insert(0, callee);
    program.functions.insert(
        1,
        func(
            "caller",
            sig(
                vec![param(WORLD_VAR, world_type(world_id))],
                Type::Tuple(vec![Type::UInt(64), world_type(world_id)]),
            ),
            body(
                vec![Stmt::Eval(Expr::Tuple(vec![Expr::Call {
                    fun: 0,
                    type_args: Vec::new(),
                    args: vec![Expr::Var(WORLD_VAR.into())],
                }]))],
                Expr::Tuple(vec![lit_u64(1), Expr::Var(WORLD_VAR.into())]),
            ),
            FuncOpts::default(),
        ),
    );

    assert!(matches!(
        check(&program, world_id),
        Err(PostconditionError::LingeringUnthreadedCall {
            function: 1,
            callee: 0
        })
    ));
}

#[test]
fn wrong_typed_world_call_argument_rejects_in_let_and_direct_tails() {
    for (direct_tail, callee_effects, caller_effects) in [
        (false, Effects::CONSERVATIVE, Effects::CONSERVATIVE),
        (true, Effects::CONSERVATIVE, Effects::CONSERVATIVE),
        (false, Effects::PURE, Effects::PURE),
        (true, Effects::PURE, Effects::PURE),
        (false, Effects::CONSERVATIVE, Effects::PURE),
        (true, Effects::CONSERVATIVE, Effects::PURE),
    ] {
        let mut program = program_with(Vec::new());
        let world_id = ensure_world_struct(&mut program);
        let return_type = Type::Tuple(vec![world_type(world_id)]);
        program.functions.insert(
            0,
            func(
                "callee",
                sig(
                    vec![param(WORLD_VAR, world_type(world_id))],
                    return_type.clone(),
                ),
                body(Vec::new(), Expr::Tuple(vec![Expr::Var(WORLD_VAR.into())])),
                FuncOpts {
                    effects: callee_effects,
                    ..Default::default()
                },
            ),
        );
        let call = || Expr::Call {
            fun: 0,
            type_args: Vec::new(),
            args: vec![Expr::Var("amount".into())],
        };
        let caller_body = if direct_tail {
            body(Vec::new(), call())
        } else {
            body(
                vec![Stmt::Let {
                    pattern: vec![Some("returned_world".into())],
                    value: call(),
                }],
                Expr::Tuple(vec![Expr::Var("returned_world".into())]),
            )
        };
        program.functions.insert(
            1,
            func(
                "caller",
                sig(
                    vec![
                        param("amount", Type::UInt(64)),
                        param(WORLD_VAR, world_type(world_id)),
                    ],
                    return_type,
                ),
                caller_body,
                FuncOpts {
                    effects: caller_effects,
                    ..Default::default()
                },
            ),
        );

        assert!(matches!(
            check(&program, world_id),
            Err(PostconditionError::LingeringUnthreadedCall {
                function: 1,
                callee: 0
            })
        ));
    }
}

#[test]
fn global_mut_callee_without_declared_world_slots_rejects() {
    let native = native_impure("malformed_native", Vec::new(), Type::Unit);
    let mut program = program_with_natives(Vec::new(), vec![(0, native)]);
    let world_id = ensure_world_struct(&mut program);
    program.functions.insert(
        1,
        func(
            "caller",
            sig(
                vec![param(WORLD_VAR, world_type(world_id))],
                Type::Tuple(vec![world_type(world_id)]),
            ),
            body(
                vec![Stmt::Eval(Expr::Call {
                    fun: 0,
                    type_args: Vec::new(),
                    args: Vec::new(),
                })],
                Expr::Tuple(vec![Expr::Var(WORLD_VAR.into())]),
            ),
            FuncOpts::default(),
        ),
    );

    assert!(matches!(
        check(&program, world_id),
        Err(PostconditionError::LingeringUnthreadedCall {
            function: 1,
            callee: 0
        })
    ));
}

#[test]
fn uncalled_global_mut_native_without_world_slots_rejects() {
    let native = native_impure("malformed_native", Vec::new(), Type::Unit);
    let mut program = program_with_natives(Vec::new(), vec![(0, native)]);
    let world_id = ensure_world_struct(&mut program);

    assert!(matches!(
        check(&program, world_id),
        Err(PostconditionError::MalformedNativeSignature { native: 0 })
    ));
}

#[test]
fn uncalled_global_mut_native_with_duplicate_world_params_rejects() {
    let mut program = program_with_natives(Vec::new(), Vec::new());
    let world_id = ensure_world_struct(&mut program);
    program.natives.decls.insert(
        0,
        native_impure(
            "malformed_native",
            vec![
                param("world_0", world_type(world_id)),
                param("world_1", world_type(world_id)),
            ],
            Type::Tuple(vec![world_type(world_id)]),
        ),
    );

    assert!(matches!(
        check(&program, world_id),
        Err(PostconditionError::MalformedNativeSignature { native: 0 })
    ));
}

#[test]
fn uncalled_global_mut_native_with_duplicate_world_returns_rejects() {
    let mut program = program_with_natives(Vec::new(), Vec::new());
    let world_id = ensure_world_struct(&mut program);
    program.natives.decls.insert(
        0,
        native_impure(
            "malformed_native",
            vec![param(WORLD_VAR, world_type(world_id))],
            Type::Tuple(vec![world_type(world_id), world_type(world_id)]),
        ),
    );

    assert!(matches!(
        check(&program, world_id),
        Err(PostconditionError::MalformedNativeSignature { native: 0 })
    ));
}

#[test]
fn generic_match_payload_cannot_replace_the_current_world() {
    let mut program = program_with(Vec::new());
    let world_id = ensure_world_struct(&mut program);
    let carrier_id = world_id + 1;
    let return_type = Type::Tuple(vec![Type::UInt(64), world_type(world_id)]);
    program.structs.insert(
        carrier_id,
        Struct {
            module_id: 0,
            name: "Carrier".into(),
            qualified_name: "MyProject::m::Carrier".into(),
            type_params: vec!["T".into()],
            fields: Vec::new(),
            variants: Some(vec![
                Variant {
                    name: "NoValue".into(),
                    tag: 0,
                    fields: Vec::new(),
                },
                Variant {
                    name: "Value".into(),
                    tag: 1,
                    fields: vec![Field {
                        name: "payload".into(),
                        field_type: Type::TypeParam(0),
                    }],
                },
            ]),
            is_native: false,
        },
    );
    let carrier_type = Type::Struct {
        struct_id: carrier_id,
        type_args: vec![return_type.clone()],
    };
    let tail = Expr::Match {
        struct_id: carrier_id,
        selector: Box::new(Expr::Var("carrier".into())),
        cases: vec![
            MatchArm {
                variant: 0,
                bindings: Vec::new(),
                body: Box::new(Block::just(Expr::Tuple(vec![
                    lit_u64(0),
                    Expr::Var(WORLD_VAR.into()),
                ]))),
            },
            MatchArm {
                variant: 1,
                bindings: vec!["payload".into()],
                body: Box::new(Block::just(Expr::Var("payload".into()))),
            },
        ],
    };
    program.functions.insert(
        0,
        func(
            "f",
            sig(
                vec![
                    param("carrier", carrier_type),
                    param(WORLD_VAR, world_type(world_id)),
                ],
                return_type,
            ),
            body(Vec::new(), tail),
            FuncOpts::default(),
        ),
    );

    assert!(matches!(
        check(&program, world_id),
        Err(PostconditionError::StaleWorldToken { function: 0 })
    ));
}

#[test]
fn generic_match_payload_world_carrier_is_order_independent() {
    let mut program = program_with(Vec::new());
    let world_id = ensure_world_struct(&mut program);
    let carrier_id = world_id + 1;
    let return_type = Type::Tuple(vec![Type::UInt(64), world_type(world_id)]);
    program.structs.insert(
        carrier_id,
        Struct {
            module_id: 0,
            name: "Carrier".into(),
            qualified_name: "MyProject::m::Carrier".into(),
            type_params: vec!["T".into()],
            fields: Vec::new(),
            variants: Some(vec![
                Variant {
                    name: "Value".into(),
                    tag: 7,
                    fields: vec![Field {
                        name: "payload".into(),
                        field_type: Type::TypeParam(0),
                    }],
                },
                Variant {
                    name: "Other".into(),
                    tag: 9,
                    fields: Vec::new(),
                },
            ]),
            is_native: false,
        },
    );
    let match_value = Expr::Match {
        struct_id: carrier_id,
        selector: Box::new(Expr::Pack {
            struct_id: carrier_id,
            type_args: vec![return_type.clone()],
            variant: Some(7),
            fields: vec![Expr::Tuple(vec![lit_u64(7), Expr::Var(WORLD_VAR.into())])],
        }),
        cases: vec![
            MatchArm {
                variant: 7,
                bindings: vec!["payload".into()],
                body: Box::new(Block::just(Expr::Var("payload".into()))),
            },
            MatchArm {
                variant: 9,
                bindings: Vec::new(),
                body: Box::new(Block::just(Expr::Tuple(vec![
                    lit_u64(9),
                    Expr::Var(WORLD_VAR.into()),
                ]))),
            },
        ],
    };
    program.functions.insert(
        0,
        func(
            "f",
            sig(vec![param(WORLD_VAR, world_type(world_id))], return_type),
            body(
                vec![Stmt::Let {
                    pattern: vec![Some("result".into())],
                    value: match_value,
                }],
                Expr::Var("result".into()),
            ),
            FuncOpts::default(),
        ),
    );

    check(&program, world_id).expect("generic Match payload retains the current World");

    let Stmt::Let {
        value: Expr::Match { cases, .. },
        ..
    } = &mut program.functions.get_mut(&0).unwrap().body.stmts[0]
    else {
        unreachable!()
    };
    cases.swap(0, 1);
    check(&program, world_id).expect("Match arm order does not change payload typing");
}

#[test]
fn quantifier_body_with_pure_call_passes() {
    // forall x in 0..10, contains(x, vec) -- contains is NoMut.
    use crate::ir::{Block, QuantDomain, QuantifierKind};
    let contains_native = native_with_effects(
        "contains",
        vec![param("x", Type::UInt(64))],
        Type::Bool,
        crate::ir::Effects::PURE,
    );
    let caller = func(
        "f",
        sig(Vec::new(), Type::Bool),
        body(
            Vec::new(),
            Expr::Quantifier {
                kind: QuantifierKind::Forall,
                binder: VarId::from("x"),
                binder_type: Type::UInt(64),
                domain: QuantDomain::Range {
                    start: Box::new(lit_u64(0)),
                    end: Box::new(lit_u64(10)),
                },
                body: Box::new(Block {
                    stmts: Vec::new(),
                    tail: BlockTail::Value(Expr::Call {
                        fun: 0,
                        type_args: Vec::new(),
                        args: vec![Expr::Var(VarId::from("x"))],
                    }),
                }),
            },
        ),
        FuncOpts {
            effects: Effects::PURE,
            ..Default::default()
        },
    );
    let mut program = program_with_natives(vec![(1, caller)], vec![(0, contains_native)]);
    let world_id = ensure_world_struct(&mut program);
    check(&program, world_id).expect("postcondition should hold");
}

#[test]
fn quantifier_body_with_local_mut_call_rejects() {
    // forall x in 0..10, push_back(&mut v, x) -- push_back is LocalMut.
    // Quantifier bodies must contain only NoMut callees.
    use crate::ir::{Block, MutLevel, QuantDomain, QuantifierKind};
    let push_back_native = native_with_effects(
        "push_back",
        vec![param("x", Type::UInt(64))],
        Type::Unit,
        crate::ir::Effects {
            aborts: crate::ir::AbortBit::Total,
            det: crate::ir::DetBit::Det,
            mutation: MutLevel::LocalMut,
            world_writes: false,
        },
    );
    let caller = func(
        "f",
        sig(Vec::new(), Type::Unit),
        body(
            Vec::new(),
            Expr::Quantifier {
                kind: QuantifierKind::Forall,
                binder: VarId::from("x"),
                binder_type: Type::UInt(64),
                domain: QuantDomain::Range {
                    start: Box::new(lit_u64(0)),
                    end: Box::new(lit_u64(10)),
                },
                body: Box::new(Block {
                    stmts: Vec::new(),
                    tail: BlockTail::Value(Expr::Call {
                        fun: 0,
                        type_args: Vec::new(),
                        args: vec![Expr::Var(VarId::from("x"))],
                    }),
                }),
            },
        ),
        FuncOpts {
            effects: Effects::PURE,
            ..Default::default()
        },
    );
    let mut program = program_with_natives(vec![(1, caller)], vec![(0, push_back_native)]);
    let world_id = ensure_world_struct(&mut program);
    let result = check(&program, world_id);
    assert!(
        matches!(
            result,
            Err(PostconditionError::MutCallInQuantifier {
                function: 1,
                callee: 0,
                callee_mutation: MutLevel::LocalMut,
            })
        ),
        "expected MutCallInQuantifier on LocalMut callee, got {:?}",
        result
    );
}

#[test]
fn quantifier_body_with_global_mut_call_rejects() {
    // forall x in 0..10, transfer(x, ...) -- transfer is GlobalMut.
    use crate::ir::{Block, MutLevel, QuantDomain, QuantifierKind};
    let transfer_native = native_with_effects(
        "transfer",
        vec![param("o", Type::UInt(64))],
        Type::Unit,
        crate::ir::Effects {
            aborts: crate::ir::AbortBit::Total,
            det: crate::ir::DetBit::Det,
            mutation: MutLevel::GlobalMut,
            world_writes: true,
        },
    );
    let caller = func(
        "f",
        sig(Vec::new(), Type::Unit),
        body(
            Vec::new(),
            Expr::Quantifier {
                kind: QuantifierKind::Forall,
                binder: VarId::from("x"),
                binder_type: Type::UInt(64),
                domain: QuantDomain::Range {
                    start: Box::new(lit_u64(0)),
                    end: Box::new(lit_u64(10)),
                },
                body: Box::new(Block {
                    stmts: Vec::new(),
                    tail: BlockTail::Value(Expr::Call {
                        fun: 0,
                        type_args: Vec::new(),
                        args: vec![Expr::Var(VarId::from("x"))],
                    }),
                }),
            },
        ),
        FuncOpts {
            effects: Effects::PURE,
            ..Default::default()
        },
    );
    let mut program = program_with_natives(vec![(1, caller)], vec![(0, transfer_native)]);
    let world_id = ensure_world_struct(&mut program);
    let result = check(&program, world_id);
    assert!(
        matches!(
            result,
            Err(PostconditionError::MutCallInQuantifier {
                function: 1,
                callee: 0,
                callee_mutation: MutLevel::GlobalMut,
            })
        ),
        "expected MutCallInQuantifier on GlobalMut callee, got {:?}",
        result
    );
}

fn local_mut_call() -> Expr {
    Expr::Call {
        fun: 0,
        type_args: Vec::new(),
        args: Vec::new(),
    }
}

fn assert_nested_quantifier_mutation_rejects(expr: Expr) {
    let local_mut = native_with_effects(
        "local_mut",
        Vec::new(),
        Type::UInt(64),
        Effects {
            aborts: crate::ir::AbortBit::Total,
            det: crate::ir::DetBit::Det,
            mutation: crate::ir::MutLevel::LocalMut,
            world_writes: false,
        },
    );
    let caller = func(
        "f",
        sig(Vec::new(), Type::Unit),
        body(Vec::new(), expr),
        FuncOpts {
            effects: Effects::PURE,
            ..Default::default()
        },
    );
    let mut program = program_with_natives(vec![(1, caller)], vec![(0, local_mut)]);
    let world_id = ensure_world_struct(&mut program);
    assert!(matches!(
        check(&program, world_id),
        Err(PostconditionError::MutCallInQuantifier {
            function: 1,
            callee: 0,
            callee_mutation: crate::ir::MutLevel::LocalMut,
        })
    ));
}

fn quantifier_with_body(expr: Expr) -> Expr {
    Expr::Quantifier {
        kind: QuantifierKind::Forall,
        binder: "x".into(),
        binder_type: Type::UInt(64),
        domain: QuantDomain::Unbounded,
        body: Box::new(Block::just(expr)),
    }
}

#[test]
fn quantifier_nested_under_update_is_discovered() {
    assert_nested_quantifier_mutation_rejects(Expr::Update {
        step: PathStep::Field {
            struct_id: 99,
            field_index: 0,
        },
        base: Box::new(Expr::Unit),
        value: Box::new(quantifier_with_body(local_mut_call())),
    });
}

#[test]
fn quantifier_rejects_mutating_call_in_map_key_operand() {
    assert_nested_quantifier_mutation_rejects(quantifier_with_body(Expr::Borrow {
        step: PathStep::MapKey {
            key: Box::new(local_mut_call()),
            key_type: Type::UInt(64),
            value_type: Type::UInt(64),
            df_value: None,
        },
        base: Box::new(Expr::Unit),
    }));
}

#[test]
fn quantifier_rejects_mutating_call_in_update_value() {
    assert_nested_quantifier_mutation_rejects(quantifier_with_body(Expr::Update {
        step: PathStep::Field {
            struct_id: 99,
            field_index: 0,
        },
        base: Box::new(Expr::Unit),
        value: Box::new(local_mut_call()),
    }));
}

/// Build `callee` (returns `(u64, World)`), an `f`/`f.aborts` spec pair, and a
/// stage-7 continuation fragment `<frag_name>` (`FunctionKind::Synthetic`)
/// whose body drops the callee's returned World slot into a pattern hole --
/// which is what stage 6 leaves behind once the token is dead. `parent_kind`
/// decides whether the fragment descends from the `.aborts` companion or from
/// an ordinary executable `Source` function.
fn program_with_cont_fragment_dropping_world(
    frag_name: &str,
    parent_is_spec: bool,
) -> (crate::ir::Program, crate::ir::StructId) {
    let mut program = program_with(Vec::new());
    let world_id = ensure_world_struct(&mut program);
    let wt = world_type(world_id);

    program.functions.insert(
        0,
        func(
            "callee",
            sig(
                vec![param(WORLD_VAR, wt.clone())],
                Type::Tuple(vec![Type::UInt(64), wt.clone()]),
            ),
            body(
                Vec::new(),
                Expr::Tuple(vec![lit_u64(1), Expr::Var(WORLD_VAR.into())]),
            ),
            FuncOpts {
                effects: crate::ir::Effects::PURE,
                ..Default::default()
            },
        ),
    );
    program.functions.insert(
        1,
        func(
            "f_target",
            sig(Vec::new(), Type::Unit),
            body(Vec::new(), Expr::Unit),
            FuncOpts {
                effects: crate::ir::Effects::PURE,
                ..Default::default()
            },
        ),
    );
    let mut parent = func(
        if parent_is_spec { "f.aborts" } else { "f" },
        sig(Vec::new(), Type::Bool),
        body(Vec::new(), Expr::Const(crate::ir::Const::Bool(true))),
        FuncOpts {
            effects: crate::ir::Effects::PURE,
            ..Default::default()
        },
    );
    if parent_is_spec {
        parent.kind = FunctionKind::Spec {
            kind: crate::ir::SpecKind::Aborts,
            target: 1,
        };
    }
    program.functions.insert(2, parent);

    let mut fragment = func(
        frag_name,
        sig(vec![param(WORLD_VAR, wt)], Type::Bool),
        Block {
            stmts: vec![Stmt::Let {
                // slot 1 is the returned World -- dropped.
                pattern: vec![Some(VarId::from("v")), None],
                value: Expr::Call {
                    fun: 0,
                    type_args: Vec::new(),
                    args: vec![Expr::Var(WORLD_VAR.into())],
                },
            }],
            tail: BlockTail::Value(Expr::Const(crate::ir::Const::Bool(true))),
        },
        FuncOpts {
            effects: crate::ir::Effects::PURE,
            ..Default::default()
        },
    );
    fragment.kind = FunctionKind::Synthetic;
    program.functions.insert(3, fragment);
    (program, world_id)
}

/// Regression: navi `dynamic_health_factor_spec.aborts.cont_0.cont_0`.
///
/// A `.aborts` companion is a proof environment and is exempt from the
/// executable world-threading checks. Stage 7 lifts part of its body into
/// `.cont_N` fragments, and stage 6 then eliminates the World token the
/// fragment no longer uses -- correct, because the fragment exits with an
/// `AbortResult`, not a World. The exemption has to descend with the body.
#[test]
fn cont_fragment_of_a_spec_companion_may_drop_a_dead_world_slot() {
    let (program, world_id) =
        program_with_cont_fragment_dropping_world("f.aborts.cont_0.cont_0", true);
    check(&program, world_id).expect("a proof environment's continuation is a proof environment");
}

/// The dual, so the exemption cannot be read as "any `.cont_N` is exempt":
/// a continuation of an ordinary executable function still has to capture the
/// World slot it is handed.
#[test]
fn cont_fragment_of_an_executable_function_still_rejects_a_dropped_world_slot() {
    let (program, world_id) = program_with_cont_fragment_dropping_world("f.cont_0", false);
    assert!(matches!(
        check(&program, world_id),
        Err(PostconditionError::LingeringUnthreadedCall {
            function: 3,
            callee: 0
        })
    ));
}

// Suppress unused-import warning.
#[allow(unused_imports)]
use BlockTail as _;
