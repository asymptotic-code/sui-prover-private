use crate::ir::builder::write_back;
use crate::ir::{
    BinOp, Block, BlockTail, Effects, Expr, Field, FunId, Function, FunctionKind, MatchArm,
    QuantDomain, QuantifierKind, Stmt, Struct, StructId, Type, Variant,
};
use crate::stage_04_effects::common::WORLD_VAR;
use crate::stage_04_effects::postcondition::{check, PostconditionError};
use crate::stage_04_effects::{ensure_world_struct, world_type};

use super::fixtures::*;

fn step(world_id: StructId) -> Function {
    func(
        "step",
        sig(
            vec![param(WORLD_VAR, world_type(world_id))],
            Type::Tuple(vec![world_type(world_id)]),
        ),
        body(Vec::new(), Expr::Tuple(vec![Expr::Var(WORLD_VAR.into())])),
        FuncOpts::default(),
    )
}

fn call_step(world: &str) -> Expr {
    Expr::Call {
        fun: 0,
        type_args: Vec::new(),
        args: vec![Expr::Var(world.into())],
    }
}

fn threaded_signature(
    world_id: StructId,
    extra: Vec<crate::ir::Param>,
    value: bool,
) -> crate::ir::Signature {
    let mut params = extra;
    params.push(param(WORLD_VAR, world_type(world_id)));
    let mut returns = Vec::new();
    if value {
        returns.push(Type::UInt(64));
    }
    returns.push(world_type(world_id));
    sig(params, Type::Tuple(returns))
}

fn stale(function: FunId, result: Result<(), PostconditionError>) {
    assert!(
        matches!(
            &result,
            Err(PostconditionError::StaleWorldToken { function: found }) if *found == function
        ),
        "expected stale World in function {function}, got {result:?}"
    );
}

fn invalid_world_flow(function: FunId, result: Result<(), PostconditionError>) {
    assert!(
        matches!(
            &result,
            Err(PostconditionError::StaleWorldToken { function: found })
                | Err(PostconditionError::ReturnMissingWorld { function: found })
                if *found == function
        ),
        "expected a closed World-flow failure in function {function}, got {result:?}"
    );
}

#[test]
fn straight_line_calls_must_consume_the_latest_world() {
    let mut program = program_with(Vec::new());
    let world_id = ensure_world_struct(&mut program);
    program.functions.insert(0, step(world_id));
    program.functions.insert(
        1,
        func(
            "caller",
            threaded_signature(world_id, Vec::new(), false),
            body(
                vec![
                    Stmt::Let {
                        pattern: vec![Some("world_1".into())],
                        value: call_step(WORLD_VAR),
                    },
                    Stmt::Let {
                        pattern: vec![Some("world_2".into())],
                        value: call_step("world_1"),
                    },
                ],
                Expr::Tuple(vec![Expr::Var("world_2".into())]),
            ),
            FuncOpts::default(),
        ),
    );

    check(&program, world_id).expect("latest World is threaded linearly");

    let caller = program.functions.get_mut(&1).unwrap();
    let Stmt::Let {
        value: Expr::Call { args, .. },
        ..
    } = &mut caller.body.stmts[1]
    else {
        unreachable!()
    };
    args[0] = Expr::Var(WORLD_VAR.into());
    stale(1, check(&program, world_id));
}

#[test]
fn direct_tail_call_must_consume_the_latest_world() {
    let mut program = program_with(Vec::new());
    let world_id = ensure_world_struct(&mut program);
    program.functions.insert(0, step(world_id));
    program.functions.insert(
        1,
        func(
            "caller",
            threaded_signature(world_id, Vec::new(), false),
            body(
                vec![Stmt::Let {
                    pattern: vec![Some("world_1".into())],
                    value: call_step(WORLD_VAR),
                }],
                call_step("world_1"),
            ),
            FuncOpts::default(),
        ),
    );

    check(&program, world_id).expect("direct tail delegates the latest World");

    program.functions.get_mut(&1).unwrap().body.tail = BlockTail::Value(call_step(WORLD_VAR));
    stale(1, check(&program, world_id));
}

#[test]
fn function_exit_must_return_the_latest_world() {
    let mut program = program_with(Vec::new());
    let world_id = ensure_world_struct(&mut program);
    program.functions.insert(0, step(world_id));
    program.functions.insert(
        1,
        func(
            "caller",
            threaded_signature(world_id, Vec::new(), false),
            body(
                vec![Stmt::Let {
                    pattern: vec![Some("world_1".into())],
                    value: call_step(WORLD_VAR),
                }],
                Expr::Tuple(vec![Expr::Var(WORLD_VAR.into())]),
            ),
            FuncOpts::default(),
        ),
    );

    stale(1, check(&program, world_id));
}

#[test]
fn pre_ssa_if_implicitly_joins_the_canonical_world() {
    let mut program = program_with(Vec::new());
    let world_id = ensure_world_struct(&mut program);
    program.functions.insert(0, step(world_id));
    let update = Block {
        stmts: vec![Stmt::Let {
            pattern: vec![Some(WORLD_VAR.into())],
            value: call_step(WORLD_VAR),
        }],
        tail: BlockTail::Value(Expr::Unit),
    };
    let unchanged = Block::just(Expr::Unit);
    program.functions.insert(
        1,
        func(
            "caller",
            threaded_signature(world_id, vec![param("cond", Type::Bool)], false),
            body(
                vec![Stmt::Eval(Expr::If {
                    cond: Box::new(Expr::Var("cond".into())),
                    then_branch: Box::new(update),
                    else_branch: Box::new(unchanged),
                })],
                Expr::Tuple(vec![Expr::Var(WORLD_VAR.into())]),
            ),
            FuncOpts::default(),
        ),
    );

    check(&program, world_id).expect("pre-SSA canonical rebind becomes an implicit phi");
}

#[test]
fn aborting_eval_branch_does_not_contribute_to_the_world_join() {
    let mut program = program_with(Vec::new());
    let world_id = ensure_world_struct(&mut program);
    program.functions.insert(0, step(world_id));
    let aborting = Block {
        stmts: vec![Stmt::Let {
            pattern: vec![Some("world_gone".into())],
            value: call_step("world_1"),
        }],
        tail: BlockTail::Abort {
            code: Box::new(lit_u64(9)),
        },
    };
    program.functions.insert(
        1,
        func(
            "caller",
            threaded_signature(world_id, vec![param("cond", Type::Bool)], false),
            body(
                vec![
                    Stmt::Let {
                        pattern: vec![Some("world_1".into())],
                        value: call_step(WORLD_VAR),
                    },
                    Stmt::Eval(Expr::If {
                        cond: Box::new(Expr::Var("cond".into())),
                        then_branch: Box::new(Block::just(Expr::Unit)),
                        else_branch: Box::new(aborting),
                    }),
                    Stmt::Let {
                        pattern: vec![Some("world_2".into())],
                        value: call_step("world_1"),
                    },
                ],
                Expr::Tuple(vec![Expr::Var("world_2".into())]),
            ),
            FuncOpts::default(),
        ),
    );

    check(&program, world_id)
        .expect("an arm that aborts leaves the path and cannot advance the join");

    let caller = program.functions.get_mut(&1).unwrap();
    let Stmt::Eval(Expr::If { else_branch, .. }) = &mut caller.body.stmts[1] else {
        unreachable!()
    };
    else_branch.tail = BlockTail::Value(Expr::Unit);
    stale(1, check(&program, world_id));
}

#[test]
fn eval_branch_return_still_validates_its_world() {
    let mut program = program_with(Vec::new());
    let world_id = ensure_world_struct(&mut program);
    program.functions.insert(0, step(world_id));
    let early_exit = Block {
        stmts: Vec::new(),
        tail: BlockTail::Return(Box::new(Expr::Tuple(vec![Expr::Var("world_2".into())]))),
    };
    program.functions.insert(
        1,
        func(
            "caller",
            threaded_signature(world_id, vec![param("cond", Type::Bool)], false),
            body(
                vec![
                    Stmt::Let {
                        pattern: vec![Some("world_1".into())],
                        value: call_step(WORLD_VAR),
                    },
                    Stmt::Let {
                        pattern: vec![Some("world_2".into())],
                        value: call_step("world_1"),
                    },
                    Stmt::Eval(Expr::If {
                        cond: Box::new(Expr::Var("cond".into())),
                        then_branch: Box::new(early_exit),
                        else_branch: Box::new(Block::just(Expr::Unit)),
                    }),
                ],
                Expr::Tuple(vec![Expr::Var("world_2".into())]),
            ),
            FuncOpts::default(),
        ),
    );

    check(&program, world_id).expect("an eval-position early return may carry the current World");

    let caller = program.functions.get_mut(&1).unwrap();
    let Stmt::Eval(Expr::If { then_branch, .. }) = &mut caller.body.stmts[2] else {
        unreachable!()
    };
    then_branch.tail = BlockTail::Return(Box::new(Expr::Tuple(vec![Expr::Var("world_1".into())])));
    stale(1, check(&program, world_id));
}

#[test]
fn ssa_if_phi_carries_each_arms_current_world() {
    let mut program = program_with(Vec::new());
    let world_id = ensure_world_struct(&mut program);
    program.functions.insert(0, step(world_id));
    let updated = Block {
        stmts: vec![Stmt::Let {
            pattern: vec![Some("world_then".into())],
            value: call_step(WORLD_VAR),
        }],
        tail: BlockTail::Value(Expr::Var("world_then".into())),
    };
    let unchanged = Block::just(Expr::Var(WORLD_VAR.into()));
    program.functions.insert(
        1,
        func(
            "caller",
            threaded_signature(world_id, vec![param("cond", Type::Bool)], false),
            body(
                vec![Stmt::Let {
                    pattern: vec![Some("world_phi".into())],
                    value: Expr::If {
                        cond: Box::new(Expr::Var("cond".into())),
                        then_branch: Box::new(updated),
                        else_branch: Box::new(unchanged),
                    },
                }],
                Expr::Tuple(vec![Expr::Var("world_phi".into())]),
            ),
            FuncOpts::default(),
        ),
    );

    check(&program, world_id).expect("SSA phi represents the current World on both paths");

    let caller = program.functions.get_mut(&1).unwrap();
    let Stmt::Let {
        value: Expr::If { then_branch, .. },
        ..
    } = &mut caller.body.stmts[0]
    else {
        unreachable!()
    };
    then_branch.tail = BlockTail::Value(Expr::Var(WORLD_VAR.into()));
    stale(1, check(&program, world_id));
}

#[test]
fn ssa_match_phi_carries_each_arms_current_world() {
    let mut program = program_with(Vec::new());
    let world_id = ensure_world_struct(&mut program);
    let choice_id = world_id + 1;
    program.structs.insert(
        choice_id,
        Struct {
            module_id: 0,
            name: "Choice".into(),
            qualified_name: "MyProject::m::Choice".into(),
            type_params: Vec::new(),
            fields: Vec::new(),
            variants: Some(vec![
                Variant {
                    name: "Left".into(),
                    tag: 0,
                    fields: Vec::new(),
                },
                Variant {
                    name: "Right".into(),
                    tag: 1,
                    fields: Vec::new(),
                },
            ]),
            is_native: false,
        },
    );
    program.functions.insert(0, step(world_id));
    let updated = Block {
        stmts: vec![Stmt::Let {
            pattern: vec![Some("world_left".into())],
            value: call_step(WORLD_VAR),
        }],
        tail: BlockTail::Value(Expr::Var("world_left".into())),
    };
    let unchanged = Block::just(Expr::Var(WORLD_VAR.into()));
    program.functions.insert(
        1,
        func(
            "caller",
            threaded_signature(
                world_id,
                vec![param(
                    "choice",
                    Type::Struct {
                        struct_id: choice_id,
                        type_args: Vec::new(),
                    },
                )],
                false,
            ),
            body(
                vec![Stmt::Let {
                    pattern: vec![Some("world_phi".into())],
                    value: Expr::Match {
                        struct_id: choice_id,
                        selector: Box::new(Expr::Var("choice".into())),
                        cases: vec![
                            MatchArm {
                                variant: 0,
                                bindings: Vec::new(),
                                body: Box::new(updated),
                            },
                            MatchArm {
                                variant: 1,
                                bindings: Vec::new(),
                                body: Box::new(unchanged),
                            },
                        ],
                    },
                }],
                Expr::Tuple(vec![Expr::Var("world_phi".into())]),
            ),
            FuncOpts::default(),
        ),
    );

    check(&program, world_id).expect("Match phi represents the current World on each path");
}

#[test]
fn generic_early_return_carrier_preserves_the_current_world() {
    let mut program = program_with(Vec::new());
    let world_id = ensure_world_struct(&mut program);
    let carrier_id = world_id + 1;
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
                    name: "Continue".into(),
                    tag: 0,
                    fields: Vec::new(),
                },
                Variant {
                    name: "Return".into(),
                    tag: 1,
                    fields: vec![Field {
                        name: "value".into(),
                        field_type: Type::TypeParam(0),
                    }],
                },
            ]),
            is_native: false,
        },
    );
    program.functions.insert(0, step(world_id));
    let return_type = Type::Tuple(vec![Type::UInt(64), world_type(world_id)]);
    let carrier = Expr::If {
        cond: Box::new(Expr::Var("return_now".into())),
        then_branch: Box::new(Block {
            stmts: vec![Stmt::Let {
                pattern: vec![Some("world_2".into())],
                value: call_step("world_1"),
            }],
            tail: BlockTail::Value(Expr::Pack {
                struct_id: carrier_id,
                type_args: vec![return_type.clone()],
                variant: Some(1),
                fields: vec![Expr::Tuple(vec![lit_u64(7), Expr::Var("world_2".into())])],
            }),
        }),
        else_branch: Box::new(Block::just(Expr::Pack {
            struct_id: carrier_id,
            type_args: vec![return_type],
            variant: Some(0),
            fields: Vec::new(),
        })),
    };
    program.functions.insert(
        1,
        func(
            "caller",
            threaded_signature(world_id, vec![param("return_now", Type::Bool)], true),
            body(
                vec![
                    Stmt::Let {
                        pattern: vec![Some("world_1".into())],
                        value: call_step(WORLD_VAR),
                    },
                    Stmt::Let {
                        pattern: vec![Some("carrier".into())],
                        value: carrier,
                    },
                ],
                Expr::Match {
                    struct_id: carrier_id,
                    selector: Box::new(Expr::Var("carrier".into())),
                    cases: vec![
                        MatchArm {
                            variant: 0,
                            bindings: Vec::new(),
                            body: Box::new(Block::just(Expr::Tuple(vec![
                                lit_u64(9),
                                Expr::Var("world_1".into()),
                            ]))),
                        },
                        MatchArm {
                            variant: 1,
                            bindings: vec!["returned".into()],
                            body: Box::new(Block::just(Expr::Var("returned".into()))),
                        },
                    ],
                },
            ),
            FuncOpts::default(),
        ),
    );

    check(&program, world_id).expect("the carrier payload retains its World lineage");

    let caller = program.functions.get_mut(&1).unwrap();
    let Stmt::Let {
        value: Expr::If { then_branch, .. },
        ..
    } = &mut caller.body.stmts[1]
    else {
        unreachable!()
    };
    let BlockTail::Value(Expr::Pack { fields, .. }) = &mut then_branch.tail else {
        unreachable!()
    };
    fields[0] = Expr::Tuple(vec![lit_u64(7), Expr::Var("world_1".into())]);
    stale(1, check(&program, world_id));
}

#[test]
fn matching_an_old_carrier_cannot_rewind_the_world() {
    let mut program = program_with(Vec::new());
    let world_id = ensure_world_struct(&mut program);
    let tag_id = world_id + 1;
    program.structs.insert(
        tag_id,
        Struct {
            module_id: 0,
            name: "Tag".into(),
            qualified_name: "MyProject::m::Tag".into(),
            type_params: Vec::new(),
            fields: Vec::new(),
            variants: Some(vec![
                Variant {
                    name: "A".into(),
                    tag: 0,
                    fields: Vec::new(),
                },
                Variant {
                    name: "B".into(),
                    tag: 1,
                    fields: Vec::new(),
                },
            ]),
            is_native: false,
        },
    );
    program.functions.insert(0, step(world_id));
    let pack = |variant| Expr::Pack {
        struct_id: tag_id,
        type_args: Vec::new(),
        variant: Some(variant),
        fields: Vec::new(),
    };
    program.functions.insert(
        1,
        func(
            "caller",
            threaded_signature(world_id, vec![param("pick_a", Type::Bool)], false),
            body(
                vec![
                    Stmt::Let {
                        pattern: vec![Some("tag".into())],
                        value: Expr::If {
                            cond: Box::new(Expr::Var("pick_a".into())),
                            then_branch: Box::new(Block::just(pack(0))),
                            else_branch: Box::new(Block::just(pack(1))),
                        },
                    },
                    Stmt::Let {
                        pattern: vec![Some("world_1".into())],
                        value: call_step(WORLD_VAR),
                    },
                ],
                Expr::Match {
                    struct_id: tag_id,
                    selector: Box::new(Expr::Var("tag".into())),
                    cases: vec![
                        MatchArm {
                            variant: 0,
                            bindings: Vec::new(),
                            body: Box::new(Block::just(Expr::Tuple(vec![Expr::Var(
                                WORLD_VAR.into(),
                            )]))),
                        },
                        MatchArm {
                            variant: 1,
                            bindings: Vec::new(),
                            body: Box::new(Block::just(Expr::Tuple(vec![Expr::Var(
                                WORLD_VAR.into(),
                            )]))),
                        },
                    ],
                },
            ),
            FuncOpts::default(),
        ),
    );

    stale(1, check(&program, world_id));
}

#[test]
fn carrying_an_old_variant_across_a_branch_cannot_rewind_the_world() {
    let mut program = program_with(Vec::new());
    let world_id = ensure_world_struct(&mut program);
    let tag_id = world_id + 1;
    program.structs.insert(
        tag_id,
        Struct {
            module_id: 0,
            name: "Tag".into(),
            qualified_name: "MyProject::m::Tag".into(),
            type_params: Vec::new(),
            fields: Vec::new(),
            variants: Some(vec![
                Variant {
                    name: "A".into(),
                    tag: 0,
                    fields: Vec::new(),
                },
                Variant {
                    name: "B".into(),
                    tag: 1,
                    fields: Vec::new(),
                },
            ]),
            is_native: false,
        },
    );
    program.functions.insert(0, step(world_id));
    let pack = |variant| Expr::Pack {
        struct_id: tag_id,
        type_args: Vec::new(),
        variant: Some(variant),
        fields: Vec::new(),
    };
    program.functions.insert(
        1,
        func(
            "caller",
            threaded_signature(world_id, vec![param("pick_a", Type::Bool)], false),
            body(
                vec![
                    Stmt::Let {
                        pattern: vec![Some("old_tag".into())],
                        value: pack(0),
                    },
                    Stmt::Let {
                        pattern: vec![Some("tag".into())],
                        value: Expr::If {
                            cond: Box::new(Expr::Var("pick_a".into())),
                            then_branch: Box::new(Block {
                                stmts: vec![Stmt::Let {
                                    pattern: vec![Some("world_1".into())],
                                    value: call_step(WORLD_VAR),
                                }],
                                tail: BlockTail::Value(Expr::Var("old_tag".into())),
                            }),
                            else_branch: Box::new(Block::just(pack(1))),
                        },
                    },
                ],
                Expr::Match {
                    struct_id: tag_id,
                    selector: Box::new(Expr::Var("tag".into())),
                    cases: vec![
                        MatchArm {
                            variant: 0,
                            bindings: Vec::new(),
                            body: Box::new(Block::just(Expr::Tuple(vec![Expr::Var(
                                WORLD_VAR.into(),
                            )]))),
                        },
                        MatchArm {
                            variant: 1,
                            bindings: Vec::new(),
                            body: Box::new(Block::just(Expr::Tuple(vec![Expr::Var(
                                WORLD_VAR.into(),
                            )]))),
                        },
                    ],
                },
            ),
            FuncOpts::default(),
        ),
    );

    stale(1, check(&program, world_id));
}

#[test]
fn quantifier_world_read_uses_a_snapshot_without_advancing_outer_world() {
    let mut program = program_with(Vec::new());
    let world_id = ensure_world_struct(&mut program);
    program.natives.decls.insert(
        0,
        native_with_effects(
            "read",
            vec![
                param("key", Type::UInt(64)),
                param(WORLD_VAR, world_type(world_id)),
            ],
            Type::Tuple(vec![Type::Bool, world_type(world_id)]),
            Effects::WORLD,
        ),
    );
    let predicate = Expr::Quantifier {
        kind: QuantifierKind::Forall,
        binder: "key".into(),
        binder_type: Type::UInt(64),
        domain: QuantDomain::Range {
            start: Box::new(lit_u64(0)),
            end: Box::new(lit_u64(2)),
        },
        body: Box::new(Block {
            stmts: vec![Stmt::Let {
                pattern: vec![Some("present".into()), None],
                value: Expr::Call {
                    fun: 0,
                    type_args: Vec::new(),
                    args: vec![Expr::Var("key".into()), Expr::Var(WORLD_VAR.into())],
                },
            }],
            tail: BlockTail::Value(Expr::Var("present".into())),
        }),
    };
    program.functions.insert(
        1,
        func(
            "caller",
            sig(
                vec![param(WORLD_VAR, world_type(world_id))],
                Type::Tuple(vec![Type::Bool, world_type(world_id)]),
            ),
            body(
                vec![Stmt::Let {
                    pattern: vec![Some("all_present".into())],
                    value: predicate,
                }],
                Expr::Tuple(vec![
                    Expr::Var("all_present".into()),
                    Expr::Var(WORLD_VAR.into()),
                ]),
            ),
            FuncOpts::default(),
        ),
    );

    check(&program, world_id).expect("quantifier reads a fixed World snapshot");

    program.functions.insert(2, step(world_id));
    let caller = program.functions.get_mut(&1).unwrap();
    caller.body.stmts.insert(
        0,
        Stmt::Let {
            pattern: vec![Some("world_1".into())],
            value: Expr::Call {
                fun: 2,
                type_args: Vec::new(),
                args: vec![Expr::Var(WORLD_VAR.into())],
            },
        },
    );
    caller.body.tail = BlockTail::Value(Expr::Tuple(vec![
        Expr::Var("all_present".into()),
        Expr::Var("world_1".into()),
    ]));
    stale(1, check(&program, world_id));
}

#[test]
fn generic_world_instantiation_is_data_not_a_threaded_return_slot() {
    let mut program = program_with(Vec::new());
    let world_id = ensure_world_struct(&mut program);
    let mut generic = native_with_effects(
        "snapshot_value",
        vec![
            param("value", Type::TypeParam(0)),
            param(WORLD_VAR, world_type(world_id)),
        ],
        Type::TypeParam(0),
        Effects::PURE,
    );
    generic.signature.type_params.push("T".into());
    program.natives.decls.insert(0, generic);
    program.functions.insert(
        1,
        func(
            "caller",
            threaded_signature(world_id, Vec::new(), false),
            body(
                vec![Stmt::Let {
                    pattern: vec![Some("snapshot".into())],
                    value: Expr::Call {
                        fun: 0,
                        type_args: vec![world_type(world_id)],
                        args: vec![Expr::Var(WORLD_VAR.into()), Expr::Var(WORLD_VAR.into())],
                    },
                }],
                Expr::Tuple(vec![Expr::Var(WORLD_VAR.into())]),
            ),
            FuncOpts::default(),
        ),
    );

    check(&program, world_id).expect("T := World remains ordinary data");
}

#[test]
fn proof_function_may_reuse_a_world_as_mathematical_input() {
    let mut program = program_with(Vec::new());
    let world_id = ensure_world_struct(&mut program);
    program.functions.insert(0, step(world_id));
    let mut theorem = func(
        "step_correct",
        sig(vec![param(WORLD_VAR, world_type(world_id))], Type::Bool),
        body(
            Vec::new(),
            Expr::BinOp {
                op: BinOp::Eq,
                lhs: Box::new(call_step(WORLD_VAR)),
                rhs: Box::new(call_step(WORLD_VAR)),
            },
        ),
        FuncOpts {
            effects: Effects::PURE,
            ..Default::default()
        },
    );
    theorem.kind = FunctionKind::Theorem {
        target: 0,
        source: 0,
    };
    program.functions.insert(1, theorem);

    check(&program, world_id).expect("proof calls do not impose executable World succession");
}

#[test]
fn abort_family_world_simulation_is_not_an_outward_lifecycle() {
    let mut program = program_with(Vec::new());
    let world_id = ensure_world_struct(&mut program);
    program.functions.insert(0, step(world_id));
    let mut helper = func(
        "source.aborts.while_0",
        sig(vec![param(WORLD_VAR, world_type(world_id))], Type::Unit),
        body(
            vec![
                Stmt::Let {
                    pattern: vec![Some("world_1".into())],
                    value: call_step(WORLD_VAR),
                },
                Stmt::Let {
                    pattern: vec![Some("world_2".into())],
                    value: call_step("world_1"),
                },
            ],
            Expr::Unit,
        ),
        FuncOpts {
            effects: Effects::PURE,
            ..Default::default()
        },
    );
    helper.kind = FunctionKind::Synthetic;
    program.functions.insert(1, helper);

    check(&program, world_id).expect("an abort simulator does not expose its private World state");

    let mut root_spec = program.clone();
    let root = root_spec.functions.get_mut(&1).unwrap();
    root.name = "source.aborts".into();
    root.kind = FunctionKind::Spec {
        kind: crate::ir::SpecKind::Aborts,
        target: 0,
    };
    check(&root_spec, world_id).expect("a root abort spec validates its private World state");

    let root = root_spec.functions.get_mut(&1).unwrap();
    let Stmt::Let {
        value: Expr::Call { args, .. },
        ..
    } = &mut root.body.stmts[1]
    else {
        unreachable!()
    };
    args[0] = Expr::Var(WORLD_VAR.into());
    stale(1, check(&root_spec, world_id));

    let helper = program.functions.get_mut(&1).unwrap();
    let Stmt::Let {
        value: Expr::Call { args, .. },
        ..
    } = &mut helper.body.stmts[1]
    else {
        unreachable!()
    };
    args[0] = Expr::Var(WORLD_VAR.into());
    stale(1, check(&program, world_id));
}

#[test]
fn abort_loop_step_carrier_preserves_current_world_and_snapshots() {
    let mut program = program_with(Vec::new());
    let world_id = ensure_world_struct(&mut program);
    let step_id = world_id + 1;
    program.structs.insert(
        step_id,
        Struct {
            module_id: 0,
            name: "source_aborts_while_0_Step".into(),
            qualified_name: "MyProject::m::source_aborts_while_0_Step".into(),
            type_params: Vec::new(),
            fields: Vec::new(),
            variants: Some(vec![
                Variant {
                    name: "cont".into(),
                    tag: 0,
                    fields: vec![
                        Field {
                            name: "world_2".into(),
                            field_type: world_type(world_id),
                        },
                        Field {
                            name: "world_0".into(),
                            field_type: world_type(world_id),
                        },
                    ],
                },
                Variant {
                    name: "done".into(),
                    tag: 1,
                    fields: Vec::new(),
                },
            ]),
            is_native: false,
        },
    );
    program.functions.insert(0, step(world_id));
    let mut carrier = func(
        "source.aborts.while_0_step",
        sig(
            vec![
                param("world_2", world_type(world_id)),
                param("world_0", world_type(world_id)),
            ],
            Type::Struct {
                struct_id: step_id,
                type_args: Vec::new(),
            },
        ),
        body(
            Vec::new(),
            Expr::Pack {
                struct_id: step_id,
                type_args: Vec::new(),
                variant: Some(0),
                fields: vec![Expr::Var("world_2".into()), Expr::Var("world_0".into())],
            },
        ),
        FuncOpts {
            effects: Effects::PURE,
            ..Default::default()
        },
    );
    carrier.kind = FunctionKind::Synthetic;
    program.functions.insert(1, carrier);

    let carrier_call = |current: &str| Expr::Call {
        fun: 1,
        type_args: Vec::new(),
        args: vec![Expr::Var(current.into()), Expr::Var(WORLD_VAR.into())],
    };
    let mut caller = func(
        "source.aborts.while_0",
        sig(vec![param(WORLD_VAR, world_type(world_id))], Type::Unit),
        body(
            vec![
                Stmt::Let {
                    pattern: vec![Some("world_1".into())],
                    value: call_step(WORLD_VAR),
                },
                Stmt::Let {
                    pattern: vec![Some("carrier".into())],
                    value: carrier_call("world_1"),
                },
                Stmt::Let {
                    pattern: vec![Some("selected".into())],
                    value: Expr::Match {
                        struct_id: step_id,
                        selector: Box::new(Expr::Var("carrier".into())),
                        cases: vec![
                            MatchArm {
                                variant: 0,
                                bindings: vec!["next".into(), "snapshot".into()],
                                body: Box::new(Block::just(Expr::Var("next".into()))),
                            },
                            MatchArm {
                                variant: 1,
                                bindings: Vec::new(),
                                body: Box::new(Block::just(Expr::Var("world_1".into()))),
                            },
                        ],
                    },
                },
                Stmt::Let {
                    pattern: vec![Some("world_3".into())],
                    value: call_step("selected"),
                },
            ],
            Expr::Unit,
        ),
        FuncOpts {
            effects: Effects::PURE,
            ..Default::default()
        },
    );
    caller.kind = FunctionKind::Synthetic;
    program.functions.insert(2, caller);

    crate::stage_04_effects::world_flow::check_function(&program.functions[&2], &program, world_id)
        .expect("loop-step carriers preserve current and snapshot Worlds");

    let caller = program.functions.get_mut(&2).unwrap();
    let Stmt::Let {
        value: Expr::Call { args, .. },
        ..
    } = &mut caller.body.stmts[1]
    else {
        unreachable!()
    };
    args[0] = Expr::Var(WORLD_VAR.into());
    assert!(matches!(
        crate::stage_04_effects::world_flow::check_function(
            &program.functions[&2],
            &program,
            world_id,
        ),
        Err(crate::stage_04_effects::world_flow::WorldFlowError::StaleToken)
    ));
}

#[test]
fn world_routed_writeback_must_consume_the_latest_world() {
    let mut program = program_with(Vec::new());
    let world_id = ensure_world_struct(&mut program);
    let signature = sig(
        vec![
            param("parent", Type::UInt(64)),
            param("child", Type::UInt(64)),
            param(WORLD_VAR, world_type(world_id)),
        ],
        Type::Tuple(vec![Type::UInt(64), world_type(world_id)]),
    );
    program.functions.insert(
        0,
        func(
            "writeback",
            signature,
            body(
                vec![Stmt::Let {
                    pattern: vec![Some("parent_1".into()), Some("world_1".into())],
                    value: write_back("parent", "child", Some(WORLD_VAR)),
                }],
                Expr::Tuple(vec![
                    Expr::Var("parent_1".into()),
                    Expr::Var("world_1".into()),
                ]),
            ),
            FuncOpts::default(),
        ),
    );

    check(&program, world_id).expect("World-routed WriteBack returns the next World");

    let function = program.functions.get_mut(&0).unwrap();
    function.body.stmts.push(Stmt::Let {
        pattern: vec![Some("parent_2".into()), Some("world_2".into())],
        value: write_back("parent_1", "child", Some(WORLD_VAR)),
    });
    function.body.tail = BlockTail::Value(Expr::Tuple(vec![
        Expr::Var("parent_2".into()),
        Expr::Var("world_2".into()),
    ]));
    stale(0, check(&program, world_id));
}

#[test]
fn pre_ssa_while_keeps_the_canonical_world_available() {
    let mut program = program_with(Vec::new());
    let world_id = ensure_world_struct(&mut program);
    program.functions.insert(0, step(world_id));
    let while_expr = Expr::While {
        header: Box::new(Block::just(Expr::Unit)),
        cond: Box::new(Expr::Var("cond".into())),
        body: Box::new(Block {
            stmts: vec![Stmt::Let {
                pattern: vec![Some(WORLD_VAR.into())],
                value: call_step(WORLD_VAR),
            }],
            tail: BlockTail::Continue {
                level: 0,
                value: Box::new(Expr::Unit),
            },
        }),
        iter_locals: Vec::new(),
        header_exit_locals: Vec::new(),
        live_out: Vec::new(),
    };
    program.functions.insert(
        1,
        func(
            "caller",
            threaded_signature(world_id, vec![param("cond", Type::Bool)], false),
            body(
                vec![Stmt::Eval(while_expr)],
                Expr::Tuple(vec![Expr::Var(WORLD_VAR.into())]),
            ),
            FuncOpts::default(),
        ),
    );

    check(&program, world_id).expect("pre-SSA loop exposes an opaque current World at exit");
}

#[test]
fn world_neutral_loops_preserve_the_latest_world() {
    let mut program = program_with(Vec::new());
    let world_id = ensure_world_struct(&mut program);
    program.functions.insert(0, step(world_id));
    let neutral_loop = Expr::While {
        header: Box::new(Block::just(Expr::Unit)),
        cond: Box::new(Expr::Var("cond".into())),
        body: Box::new(Block {
            stmts: Vec::new(),
            tail: BlockTail::Continue {
                level: 0,
                value: Box::new(Expr::Unit),
            },
        }),
        iter_locals: Vec::new(),
        header_exit_locals: Vec::new(),
        live_out: Vec::new(),
    };
    let neutral_ssa_loop = Expr::While {
        header: Box::new(Block::just(Expr::Unit)),
        cond: Box::new(Expr::Var("cond".into())),
        body: Box::new(Block::just(Expr::Var("counter_iter".into()))),
        iter_locals: vec![("counter_iter".into(), Expr::Var("counter".into()))],
        header_exit_locals: vec!["counter_iter".into()],
        live_out: Vec::new(),
    };
    program.functions.insert(
        1,
        func(
            "caller",
            threaded_signature(
                world_id,
                vec![param("cond", Type::Bool), param("counter", Type::UInt(64))],
                false,
            ),
            body(
                vec![
                    Stmt::Let {
                        pattern: vec![Some("world_1".into())],
                        value: call_step(WORLD_VAR),
                    },
                    Stmt::Eval(neutral_loop),
                    Stmt::Let {
                        pattern: vec![Some("counter_after".into())],
                        value: neutral_ssa_loop,
                    },
                    Stmt::Let {
                        pattern: vec![Some("world_2".into())],
                        value: call_step("world_1"),
                    },
                ],
                Expr::Tuple(vec![Expr::Var("world_2".into())]),
            ),
            FuncOpts::default(),
        ),
    );

    check(&program, world_id).expect("a neutral loop does not invalidate the current World");
}

#[test]
fn loop_continue_must_carry_its_paths_current_world() {
    let mut program = program_with(Vec::new());
    let world_id = ensure_world_struct(&mut program);
    program.functions.insert(0, step(world_id));
    let loop_expr = Expr::While {
        header: Box::new(Block::just(Expr::Unit)),
        cond: Box::new(Expr::Var("cond".into())),
        body: Box::new(Block {
            stmts: vec![Stmt::Let {
                pattern: vec![Some("world_next".into())],
                value: call_step("world_iter"),
            }],
            tail: BlockTail::Continue {
                level: 0,
                value: Box::new(Expr::Var("world_next".into())),
            },
        }),
        iter_locals: vec![("world_iter".into(), Expr::Var(WORLD_VAR.into()))],
        header_exit_locals: vec!["world_iter".into()],
        live_out: Vec::new(),
    };
    program.functions.insert(
        1,
        func(
            "caller",
            threaded_signature(world_id, vec![param("cond", Type::Bool)], false),
            body(
                vec![Stmt::Let {
                    pattern: vec![Some("world_after".into())],
                    value: loop_expr,
                }],
                Expr::Tuple(vec![Expr::Var("world_after".into())]),
            ),
            FuncOpts::default(),
        ),
    );

    check(&program, world_id).expect("the loop back-edge carries the updated World");

    let caller = program.functions.get_mut(&1).unwrap();
    let Stmt::Let {
        value: Expr::While { body, .. },
        ..
    } = &mut caller.body.stmts[0]
    else {
        unreachable!()
    };
    body.tail = BlockTail::Continue {
        level: 0,
        value: Box::new(Expr::Var("world_iter".into())),
    };
    stale(1, check(&program, world_id));
}

#[test]
fn loop_condition_exit_uses_post_header_world() {
    // Stage 5 records the SSA value produced by the structured header.
    // Both the condition-false exit and the body entry occur after that
    // write, so validating against the iteration-entry binder is stale.
    let mut program = program_with(Vec::new());
    let world_id = ensure_world_struct(&mut program);
    program.functions.insert(0, step(world_id));
    let loop_expr = Expr::While {
        header: Box::new(Block {
            stmts: vec![Stmt::Let {
                pattern: vec![Some("world_header".into())],
                value: call_step("world_iter"),
            }],
            tail: BlockTail::Value(Expr::Unit),
        }),
        cond: Box::new(Expr::Var("cond".into())),
        body: Box::new(Block {
            stmts: vec![],
            tail: BlockTail::Continue {
                level: 0,
                value: Box::new(Expr::Var("world_header".into())),
            },
        }),
        iter_locals: vec![("world_iter".into(), Expr::Var(WORLD_VAR.into()))],
        header_exit_locals: vec!["world_header".into()],
        live_out: Vec::new(),
    };
    program.functions.insert(
        1,
        func(
            "caller",
            threaded_signature(world_id, vec![param("cond", Type::Bool)], false),
            body(
                vec![Stmt::Let {
                    pattern: vec![Some("world_after".into())],
                    value: loop_expr,
                }],
                Expr::Tuple(vec![Expr::Var("world_after".into())]),
            ),
            FuncOpts::default(),
        ),
    );

    check(&program, world_id).expect("post-header World is the live loop token");
}

#[test]
fn post_ssa_world_advancing_loop_requires_a_world_iter_local() {
    let mut program = program_with(Vec::new());
    let world_id = ensure_world_struct(&mut program);
    program.functions.insert(0, step(world_id));
    let loop_expr = Expr::While {
        header: Box::new(Block::just(Expr::Unit)),
        cond: Box::new(Expr::Var("cond".into())),
        body: Box::new(Block {
            stmts: vec![Stmt::Let {
                pattern: vec![Some("world_next".into())],
                value: call_step(WORLD_VAR),
            }],
            tail: BlockTail::Value(Expr::Var("counter_iter".into())),
        }),
        iter_locals: vec![("counter_iter".into(), Expr::Var("counter".into()))],
        header_exit_locals: vec!["counter_iter".into()],
        live_out: Vec::new(),
    };
    program.functions.insert(
        1,
        func(
            "caller",
            threaded_signature(
                world_id,
                vec![param("cond", Type::Bool), param("counter", Type::UInt(64))],
                false,
            ),
            body(
                vec![Stmt::Let {
                    pattern: vec![Some("counter_after".into())],
                    value: loop_expr,
                }],
                Expr::Tuple(vec![Expr::Var(WORLD_VAR.into())]),
            ),
            FuncOpts::default(),
        ),
    );

    stale(1, check(&program, world_id));
}

#[test]
fn loop_break_must_carry_its_paths_current_world() {
    let mut program = program_with(Vec::new());
    let world_id = ensure_world_struct(&mut program);
    program.functions.insert(0, step(world_id));
    let loop_expr = Expr::While {
        header: Box::new(Block::just(Expr::Unit)),
        cond: Box::new(Expr::Var("cond".into())),
        body: Box::new(Block {
            stmts: vec![Stmt::Let {
                pattern: vec![Some("world_next".into())],
                value: call_step("world_iter"),
            }],
            tail: BlockTail::Break {
                level: 0,
                value: Box::new(Expr::Var("world_iter".into())),
            },
        }),
        iter_locals: vec![("world_iter".into(), Expr::Var(WORLD_VAR.into()))],
        header_exit_locals: vec!["world_iter".into()],
        live_out: Vec::new(),
    };
    program.functions.insert(
        1,
        func(
            "caller",
            threaded_signature(world_id, vec![param("cond", Type::Bool)], false),
            body(
                vec![Stmt::Let {
                    pattern: vec![Some("world_after".into())],
                    value: loop_expr,
                }],
                Expr::Tuple(vec![Expr::Var("world_after".into())]),
            ),
            FuncOpts::default(),
        ),
    );

    stale(1, check(&program, world_id));
}

#[test]
fn labeled_block_exit_rejoins_the_enclosing_flow() {
    let mut program = program_with(Vec::new());
    let world_id = ensure_world_struct(&mut program);
    program.functions.insert(0, step(world_id));
    let labeled = Expr::LabeledBlock {
        body: Box::new(Block {
            stmts: vec![Stmt::Let {
                pattern: vec![Some("world_1".into())],
                value: call_step(WORLD_VAR),
            }],
            tail: BlockTail::ReturnFromBlock {
                level: 0,
                value: Box::new(Expr::Var("world_1".into())),
            },
        }),
        result_ty: world_type(world_id),
    };
    program.functions.insert(
        1,
        func(
            "caller",
            threaded_signature(world_id, Vec::new(), false),
            body(
                vec![
                    Stmt::Let {
                        pattern: vec![Some("escaped".into())],
                        value: labeled,
                    },
                    Stmt::Let {
                        pattern: vec![Some("world_2".into())],
                        value: call_step("escaped"),
                    },
                ],
                Expr::Tuple(vec![Expr::Var("world_2".into())]),
            ),
            FuncOpts::default(),
        ),
    );

    check(&program, world_id).expect("a local exit contributes a live World path");

    let caller = program.functions.get_mut(&1).unwrap();
    let Stmt::Let {
        value: Expr::Call { args, .. },
        ..
    } = &mut caller.body.stmts[1]
    else {
        unreachable!()
    };
    args[0] = Expr::Var(WORLD_VAR.into());
    stale(1, check(&program, world_id));
}

#[test]
fn singleton_tuple_wrapper_is_transparent_at_function_exit() {
    let mut program = program_with(Vec::new());
    let world_id = ensure_world_struct(&mut program);
    program.functions.insert(0, step(world_id));
    program.functions.insert(
        1,
        func(
            "caller",
            threaded_signature(world_id, Vec::new(), false),
            body(Vec::new(), Expr::Tuple(vec![call_step(WORLD_VAR)])),
            FuncOpts::default(),
        ),
    );

    check(&program, world_id).expect("stage-7 singleton wrappers are transparent");
}

#[test]
fn singleton_tuple_wrapper_is_transparent_at_branch_join() {
    let mut program = program_with(Vec::new());
    let world_id = ensure_world_struct(&mut program);
    program.functions.insert(0, step(world_id));
    program.functions.insert(
        1,
        func(
            "caller",
            threaded_signature(world_id, vec![param("cond", Type::Bool)], false),
            body(
                Vec::new(),
                Expr::If {
                    cond: Box::new(Expr::Var("cond".into())),
                    then_branch: Box::new(Block::just(Expr::Tuple(vec![Expr::Var(
                        WORLD_VAR.into(),
                    )]))),
                    else_branch: Box::new(Block::just(Expr::Tuple(vec![call_step(WORLD_VAR)]))),
                },
            ),
            FuncOpts::default(),
        ),
    );

    check(&program, world_id).expect("singleton wrappers do not obscure a World phi");
}

#[test]
fn mismatched_loop_handoffs_are_not_treated_as_dead_branch_values() {
    let mut program = program_with(Vec::new());
    let world_id = ensure_world_struct(&mut program);
    let return_type = Type::Tuple(vec![Type::UInt(64), world_type(world_id)]);
    program.functions.insert(0, step(world_id));

    let mut after = func(
        "loop_after",
        sig(
            vec![param(WORLD_VAR, world_type(world_id))],
            return_type.clone(),
        ),
        body(
            Vec::new(),
            Expr::Tuple(vec![lit_u64(11), Expr::Var(WORLD_VAR.into())]),
        ),
        FuncOpts::default(),
    );
    after.kind = FunctionKind::LoopAfter { parent: 3, slot: 0 };
    program.functions.insert(1, after);

    let handoff = |world: &str| Expr::Call {
        fun: 1,
        type_args: Vec::new(),
        args: vec![Expr::Var(world.into())],
    };
    let transfer = Expr::If {
        cond: Box::new(Expr::Var("choose_handoff".into())),
        then_branch: Box::new(Block::just(handoff("world_1"))),
        else_branch: Box::new(Block::just(handoff("world_1"))),
    };
    let mut loop_body = func(
        "loop_body",
        sig(
            vec![
                param("continue_here", Type::Bool),
                param("choose_handoff", Type::Bool),
                param(WORLD_VAR, world_type(world_id)),
            ],
            return_type.clone(),
        ),
        body(
            vec![
                Stmt::Let {
                    pattern: vec![Some("world_1".into())],
                    value: call_step(WORLD_VAR),
                },
                Stmt::Let {
                    pattern: vec![
                        Some("value".into()),
                        Some("amount".into()),
                        Some("world_2".into()),
                    ],
                    value: Expr::If {
                        cond: Box::new(Expr::Var("continue_here".into())),
                        then_branch: Box::new(Block::just(Expr::Tuple(vec![
                            lit_u64(7),
                            lit_u64(8),
                            Expr::Var("world_1".into()),
                        ]))),
                        else_branch: Box::new(Block::just(transfer)),
                    },
                },
            ],
            Expr::Tuple(vec![Expr::Var("value".into()), Expr::Var("world_2".into())]),
        ),
        FuncOpts::default(),
    );
    loop_body.kind = FunctionKind::LoopBody { parent: 3, slot: 0 };
    program.functions.insert(2, loop_body);
    program.functions.insert(
        3,
        func(
            "parent",
            sig(
                vec![
                    param("continue_here", Type::Bool),
                    param("choose_handoff", Type::Bool),
                    param(WORLD_VAR, world_type(world_id)),
                ],
                return_type,
            ),
            body(
                Vec::new(),
                Expr::Call {
                    fun: 2,
                    type_args: Vec::new(),
                    args: vec![
                        Expr::Var("continue_here".into()),
                        Expr::Var("choose_handoff".into()),
                        Expr::Var(WORLD_VAR.into()),
                    ],
                },
            ),
            FuncOpts::default(),
        ),
    );

    invalid_world_flow(2, check(&program, world_id));

    let mut helper_first = program.clone();
    let Stmt::Let {
        value: Expr::If {
            then_branch,
            else_branch,
            ..
        },
        ..
    } = &mut helper_first.functions.get_mut(&2).unwrap().body.stmts[1]
    else {
        unreachable!()
    };
    std::mem::swap(then_branch, else_branch);
    invalid_world_flow(2, check(&helper_first, world_id));

    let mut non_tail = program.clone();
    non_tail.functions.get_mut(&2).unwrap().body.stmts.insert(
        0,
        Stmt::Let {
            pattern: vec![Some("ignored".into()), Some("world_before".into())],
            value: handoff(WORLD_VAR),
        },
    );
    stale(2, check(&non_tail, world_id));

    let helper = program.functions.get_mut(&2).unwrap();
    let Stmt::Let {
        value: Expr::If { else_branch, .. },
        ..
    } = &mut helper.body.stmts[1]
    else {
        unreachable!()
    };
    let BlockTail::Value(Expr::If { then_branch, .. }) = &mut else_branch.tail else {
        unreachable!()
    };
    let BlockTail::Value(Expr::Call { args, .. }) = &mut then_branch.tail else {
        unreachable!()
    };
    args[0] = Expr::Var(WORLD_VAR.into());
    stale(2, check(&program, world_id));
}

#[test]
fn same_typed_loop_helper_branch_remains_live() {
    let mut program = program_with(Vec::new());
    let world_id = ensure_world_struct(&mut program);
    let return_type = Type::Tuple(vec![Type::UInt(64), world_type(world_id)]);
    program.functions.insert(0, step(world_id));

    let mut after = func(
        "loop_after",
        sig(
            vec![param(WORLD_VAR, world_type(world_id))],
            return_type.clone(),
        ),
        body(
            Vec::new(),
            Expr::Tuple(vec![lit_u64(11), Expr::Var(WORLD_VAR.into())]),
        ),
        FuncOpts::default(),
    );
    after.kind = FunctionKind::LoopAfter { parent: 3, slot: 0 };
    program.functions.insert(1, after);

    let mut loop_body = func(
        "loop_body",
        sig(
            vec![
                param("choose_handoff", Type::Bool),
                param(WORLD_VAR, world_type(world_id)),
            ],
            return_type.clone(),
        ),
        body(
            vec![
                Stmt::Let {
                    pattern: vec![Some("world_1".into())],
                    value: call_step(WORLD_VAR),
                },
                Stmt::Let {
                    pattern: vec![Some("value".into()), Some("branch_world".into())],
                    value: Expr::If {
                        cond: Box::new(Expr::Var("choose_handoff".into())),
                        then_branch: Box::new(Block::just(Expr::Call {
                            fun: 1,
                            type_args: Vec::new(),
                            args: vec![Expr::Var("world_1".into())],
                        })),
                        else_branch: Box::new(Block::just(Expr::Tuple(vec![
                            lit_u64(7),
                            Expr::Var("world_1".into()),
                        ]))),
                    },
                },
                Stmt::Let {
                    pattern: vec![Some("world_2".into())],
                    value: call_step("world_1"),
                },
            ],
            Expr::Tuple(vec![Expr::Var("value".into()), Expr::Var("world_2".into())]),
        ),
        FuncOpts::default(),
    );
    loop_body.kind = FunctionKind::LoopBody { parent: 3, slot: 0 };
    program.functions.insert(2, loop_body);
    program.functions.insert(
        3,
        func(
            "parent",
            sig(
                vec![
                    param("choose_handoff", Type::Bool),
                    param(WORLD_VAR, world_type(world_id)),
                ],
                return_type,
            ),
            body(
                Vec::new(),
                Expr::Call {
                    fun: 2,
                    type_args: Vec::new(),
                    args: vec![
                        Expr::Var("choose_handoff".into()),
                        Expr::Var(WORLD_VAR.into()),
                    ],
                },
            ),
            FuncOpts::default(),
        ),
    );

    stale(2, check(&program, world_id));
}

#[test]
fn native_erasure_through_a_prior_let_does_not_hide_a_live_loop_helper_branch() {
    let mut program = program_with(Vec::new());
    let world_id = ensure_world_struct(&mut program);
    let return_type = Type::Tuple(vec![Type::UInt(64), world_type(world_id)]);
    program.natives.decls.insert(
        4,
        native_with_effects(
            "native_value",
            Vec::new(),
            Type::MutableRef {
                inner: Box::new(Type::UInt(64)),
                root: Box::new(Type::UInt(64)),
            },
            Effects::PURE,
        ),
    );
    program.functions.insert(0, step(world_id));

    let mut after = func(
        "loop_after",
        sig(
            vec![param(WORLD_VAR, world_type(world_id))],
            return_type.clone(),
        ),
        body(
            Vec::new(),
            Expr::Tuple(vec![lit_u64(11), Expr::Var(WORLD_VAR.into())]),
        ),
        FuncOpts::default(),
    );
    after.kind = FunctionKind::LoopAfter { parent: 3, slot: 0 };
    program.functions.insert(1, after);

    let mut loop_body = func(
        "loop_body",
        sig(
            vec![
                param("choose_handoff", Type::Bool),
                param(WORLD_VAR, world_type(world_id)),
            ],
            return_type.clone(),
        ),
        body(
            vec![
                Stmt::Let {
                    pattern: vec![Some("world_1".into())],
                    value: call_step(WORLD_VAR),
                },
                Stmt::Let {
                    pattern: vec![Some("native_value".into())],
                    value: Expr::Call {
                        fun: 4,
                        type_args: Vec::new(),
                        args: Vec::new(),
                    },
                },
                Stmt::Let {
                    pattern: vec![Some("value".into()), Some("branch_world".into())],
                    value: Expr::If {
                        cond: Box::new(Expr::Var("choose_handoff".into())),
                        then_branch: Box::new(Block::just(Expr::Call {
                            fun: 1,
                            type_args: Vec::new(),
                            args: vec![Expr::Var("world_1".into())],
                        })),
                        else_branch: Box::new(Block::just(Expr::Tuple(vec![
                            Expr::Var("native_value".into()),
                            Expr::Var("world_1".into()),
                        ]))),
                    },
                },
                Stmt::Let {
                    pattern: vec![Some("world_2".into())],
                    value: call_step("world_1"),
                },
            ],
            Expr::Tuple(vec![lit_u64(99), Expr::Var("world_2".into())]),
        ),
        FuncOpts::default(),
    );
    loop_body.kind = FunctionKind::LoopBody { parent: 3, slot: 0 };
    program.functions.insert(2, loop_body);
    program.functions.insert(
        3,
        func(
            "parent",
            sig(
                vec![
                    param("choose_handoff", Type::Bool),
                    param(WORLD_VAR, world_type(world_id)),
                ],
                return_type,
            ),
            body(
                Vec::new(),
                Expr::Call {
                    fun: 2,
                    type_args: Vec::new(),
                    args: vec![
                        Expr::Var("choose_handoff".into()),
                        Expr::Var(WORLD_VAR.into()),
                    ],
                },
            ),
            FuncOpts::default(),
        ),
    );

    stale(2, check(&program, world_id));
}

#[test]
fn eval_if_keeps_a_mismatched_loop_helper_branch_live() {
    let mut program = program_with(Vec::new());
    let world_id = ensure_world_struct(&mut program);
    program.functions.insert(0, step(world_id));

    let mut after = func(
        "loop_after",
        sig(
            vec![param(WORLD_VAR, world_type(world_id))],
            Type::Tuple(vec![Type::UInt(64), world_type(world_id)]),
        ),
        body(
            Vec::new(),
            Expr::Tuple(vec![lit_u64(11), Expr::Var(WORLD_VAR.into())]),
        ),
        FuncOpts::default(),
    );
    after.kind = FunctionKind::LoopAfter { parent: 2, slot: 0 };
    program.functions.insert(1, after);
    program.functions.insert(
        2,
        func(
            "caller",
            threaded_signature(world_id, vec![param("cond", Type::Bool)], false),
            body(
                vec![
                    Stmt::Let {
                        pattern: vec![Some("world_1".into())],
                        value: call_step(WORLD_VAR),
                    },
                    Stmt::Eval(Expr::If {
                        cond: Box::new(Expr::Var("cond".into())),
                        then_branch: Box::new(Block::just(Expr::Call {
                            fun: 1,
                            type_args: Vec::new(),
                            args: vec![Expr::Var("world_1".into())],
                        })),
                        else_branch: Box::new(Block::just(Expr::Unit)),
                    }),
                    Stmt::Let {
                        pattern: vec![Some("world_2".into())],
                        value: call_step("world_1"),
                    },
                ],
                Expr::Tuple(vec![Expr::Var("world_2".into())]),
            ),
            FuncOpts::default(),
        ),
    );

    stale(2, check(&program, world_id));
}

#[test]
fn eval_match_keeps_nested_mismatched_loop_helper_branches_live() {
    let mut program = program_with(Vec::new());
    let world_id = ensure_world_struct(&mut program);
    let choice_id = world_id + 1;
    program.structs.insert(
        choice_id,
        Struct {
            module_id: 0,
            name: "Choice".into(),
            qualified_name: "MyProject::m::Choice".into(),
            type_params: Vec::new(),
            fields: Vec::new(),
            variants: Some(vec![Variant {
                name: "choice".into(),
                tag: 7,
                fields: Vec::new(),
            }]),
            is_native: false,
        },
    );
    program.functions.insert(0, step(world_id));
    let mut after = func(
        "loop_after",
        sig(
            vec![param(WORLD_VAR, world_type(world_id))],
            Type::Tuple(vec![Type::UInt(64), world_type(world_id)]),
        ),
        body(
            Vec::new(),
            Expr::Tuple(vec![lit_u64(11), Expr::Var(WORLD_VAR.into())]),
        ),
        FuncOpts::default(),
    );
    after.kind = FunctionKind::LoopAfter { parent: 2, slot: 0 };
    program.functions.insert(1, after);
    program.functions.insert(
        2,
        func(
            "caller",
            threaded_signature(
                world_id,
                vec![
                    param("cond", Type::Bool),
                    param(
                        "choice",
                        Type::Struct {
                            struct_id: choice_id,
                            type_args: Vec::new(),
                        },
                    ),
                ],
                false,
            ),
            body(
                vec![
                    Stmt::Let {
                        pattern: vec![Some("world_1".into())],
                        value: call_step(WORLD_VAR),
                    },
                    Stmt::Eval(Expr::Match {
                        struct_id: choice_id,
                        selector: Box::new(Expr::Var("choice".into())),
                        cases: vec![MatchArm {
                            variant: 7,
                            bindings: Vec::new(),
                            body: Box::new(Block::just(Expr::If {
                                cond: Box::new(Expr::Var("cond".into())),
                                then_branch: Box::new(Block::just(Expr::Call {
                                    fun: 1,
                                    type_args: Vec::new(),
                                    args: vec![Expr::Var("world_1".into())],
                                })),
                                else_branch: Box::new(Block::just(Expr::Unit)),
                            })),
                        }],
                    }),
                    Stmt::Let {
                        pattern: vec![Some("world_2".into())],
                        value: call_step("world_1"),
                    },
                ],
                Expr::Tuple(vec![Expr::Var("world_2".into())]),
            ),
            FuncOpts::default(),
        ),
    );

    stale(2, check(&program, world_id));
}

#[test]
fn mismatched_match_loop_handoffs_fail_closed_in_any_order() {
    let mut program = program_with(Vec::new());
    let world_id = ensure_world_struct(&mut program);
    let choice_id = world_id + 1;
    program.structs.insert(
        choice_id,
        Struct {
            module_id: 0,
            name: "Choice".into(),
            qualified_name: "MyProject::m::Choice".into(),
            type_params: Vec::new(),
            fields: Vec::new(),
            variants: Some(vec![
                Variant {
                    name: "handoff".into(),
                    tag: 0,
                    fields: Vec::new(),
                },
                Variant {
                    name: "ordinary".into(),
                    tag: 1,
                    fields: Vec::new(),
                },
            ]),
            is_native: false,
        },
    );
    let return_type = Type::Tuple(vec![Type::UInt(64), world_type(world_id)]);
    program.functions.insert(0, step(world_id));

    let mut after = func(
        "loop_after",
        sig(
            vec![param(WORLD_VAR, world_type(world_id))],
            return_type.clone(),
        ),
        body(
            Vec::new(),
            Expr::Tuple(vec![lit_u64(11), Expr::Var(WORLD_VAR.into())]),
        ),
        FuncOpts::default(),
    );
    after.kind = FunctionKind::LoopAfter { parent: 3, slot: 0 };
    program.functions.insert(1, after);

    let handoff = || Expr::Call {
        fun: 1,
        type_args: Vec::new(),
        args: vec![Expr::Var("world_1".into())],
    };
    let transfer = Expr::Match {
        struct_id: choice_id,
        selector: Box::new(Expr::Var("choice".into())),
        cases: vec![
            MatchArm {
                variant: 0,
                bindings: Vec::new(),
                body: Box::new(Block::just(handoff())),
            },
            MatchArm {
                variant: 1,
                bindings: Vec::new(),
                body: Box::new(Block::just(Expr::Tuple(vec![
                    lit_u64(7),
                    lit_u64(8),
                    Expr::Var("world_1".into()),
                ]))),
            },
        ],
    };
    let mut loop_body = func(
        "loop_body",
        sig(
            vec![
                param(
                    "choice",
                    Type::Struct {
                        struct_id: choice_id,
                        type_args: Vec::new(),
                    },
                ),
                param(WORLD_VAR, world_type(world_id)),
            ],
            return_type.clone(),
        ),
        body(
            vec![
                Stmt::Let {
                    pattern: vec![Some("world_1".into())],
                    value: call_step(WORLD_VAR),
                },
                Stmt::Let {
                    pattern: vec![
                        Some("value".into()),
                        Some("amount".into()),
                        Some("world_2".into()),
                    ],
                    value: transfer,
                },
            ],
            Expr::Tuple(vec![Expr::Var("value".into()), Expr::Var("world_2".into())]),
        ),
        FuncOpts::default(),
    );
    loop_body.kind = FunctionKind::LoopBody { parent: 3, slot: 0 };
    program.functions.insert(2, loop_body);
    program.functions.insert(
        3,
        func(
            "parent",
            sig(
                vec![
                    param(
                        "choice",
                        Type::Struct {
                            struct_id: choice_id,
                            type_args: Vec::new(),
                        },
                    ),
                    param(WORLD_VAR, world_type(world_id)),
                ],
                return_type,
            ),
            body(
                Vec::new(),
                Expr::Call {
                    fun: 2,
                    type_args: Vec::new(),
                    args: vec![Expr::Var("choice".into()), Expr::Var(WORLD_VAR.into())],
                },
            ),
            FuncOpts::default(),
        ),
    );

    invalid_world_flow(2, check(&program, world_id));

    let mut helper_last = program.clone();
    let Stmt::Let {
        value: Expr::Match { cases, .. },
        ..
    } = &mut helper_last.functions.get_mut(&2).unwrap().body.stmts[1]
    else {
        unreachable!()
    };
    cases.swap(0, 1);
    invalid_world_flow(2, check(&helper_last, world_id));

    let mut nested = program.clone();
    let Stmt::Let {
        value: Expr::Match { cases, .. },
        ..
    } = &mut nested.functions.get_mut(&2).unwrap().body.stmts[1]
    else {
        unreachable!()
    };
    cases[0].body = Box::new(Block::just(Expr::Match {
        struct_id: choice_id,
        selector: Box::new(Expr::Var("choice".into())),
        cases: vec![
            MatchArm {
                variant: 0,
                bindings: Vec::new(),
                body: Box::new(Block::just(handoff())),
            },
            MatchArm {
                variant: 1,
                bindings: Vec::new(),
                body: Box::new(Block::just(handoff())),
            },
        ],
    }));
    invalid_world_flow(2, check(&nested, world_id));
}

#[test]
fn known_match_arm_bindings_do_not_escape_their_lexical_scope() {
    let mut program = program_with(Vec::new());
    let world_id = ensure_world_struct(&mut program);
    let carrier_id = world_id + 1;
    program.structs.insert(
        carrier_id,
        Struct {
            module_id: 0,
            name: "WorldCarrier".into(),
            qualified_name: "MyProject::m::WorldCarrier".into(),
            type_params: Vec::new(),
            fields: Vec::new(),
            variants: Some(vec![Variant {
                name: "carry".into(),
                tag: 0,
                fields: vec![Field {
                    name: "world".into(),
                    field_type: world_type(world_id),
                }],
            }]),
            is_native: false,
        },
    );
    program.functions.insert(0, step(world_id));
    program.functions.insert(
        1,
        func(
            "caller",
            sig(
                vec![
                    param("world_0", world_type(world_id)),
                    param("world_1", world_type(world_id)),
                ],
                Type::Tuple(vec![world_type(world_id)]),
            ),
            body(
                vec![
                    Stmt::Eval(Expr::Match {
                        struct_id: carrier_id,
                        selector: Box::new(Expr::Pack {
                            struct_id: carrier_id,
                            type_args: Vec::new(),
                            variant: Some(0),
                            fields: vec![Expr::Var("world_1".into())],
                        }),
                        cases: vec![MatchArm {
                            variant: 0,
                            bindings: vec!["world_0".into()],
                            body: Box::new(Block::just(Expr::Unit)),
                        }],
                    }),
                    Stmt::Let {
                        pattern: vec![Some("world_2".into())],
                        value: call_step("world_0"),
                    },
                ],
                Expr::Tuple(vec![Expr::Var("world_2".into())]),
            ),
            FuncOpts::default(),
        ),
    );

    stale(1, check(&program, world_id));
}

#[test]
fn terminating_match_arm_bindings_do_not_escape_through_labeled_exits() {
    let mut program = program_with(Vec::new());
    let world_id = ensure_world_struct(&mut program);
    let carrier_id = world_id + 1;
    program.structs.insert(
        carrier_id,
        Struct {
            module_id: 0,
            name: "WorldCarrier".into(),
            qualified_name: "MyProject::m::WorldCarrier".into(),
            type_params: Vec::new(),
            fields: Vec::new(),
            variants: Some(vec![Variant {
                name: "carry".into(),
                tag: 7,
                fields: vec![Field {
                    name: "world".into(),
                    field_type: world_type(world_id),
                }],
            }]),
            is_native: false,
        },
    );
    program.functions.insert(0, step(world_id));
    program.functions.insert(
        1,
        func(
            "caller",
            sig(
                vec![
                    param("world_0", world_type(world_id)),
                    param("world_1", world_type(world_id)),
                ],
                Type::Tuple(vec![world_type(world_id)]),
            ),
            body(
                vec![
                    Stmt::Eval(Expr::LabeledBlock {
                        body: Box::new(Block::just(Expr::Match {
                            struct_id: carrier_id,
                            selector: Box::new(Expr::Pack {
                                struct_id: carrier_id,
                                type_args: Vec::new(),
                                variant: Some(7),
                                fields: vec![Expr::Var("world_1".into())],
                            }),
                            cases: vec![MatchArm {
                                variant: 7,
                                bindings: vec!["world_0".into()],
                                body: Box::new(Block {
                                    stmts: Vec::new(),
                                    tail: BlockTail::ReturnFromBlock {
                                        level: 0,
                                        value: Box::new(Expr::Unit),
                                    },
                                }),
                            }],
                        })),
                        result_ty: Type::Unit,
                    }),
                    Stmt::Let {
                        pattern: vec![Some("world_2".into())],
                        value: call_step("world_0"),
                    },
                ],
                Expr::Tuple(vec![Expr::Var("world_2".into())]),
            ),
            FuncOpts::default(),
        ),
    );

    stale(1, check(&program, world_id));
}

#[test]
fn first_of_multiple_world_params_is_the_lifecycle_channel() {
    let mut program = program_with(Vec::new());
    let world_id = ensure_world_struct(&mut program);
    program.functions.insert(0, step(world_id));
    let mut helper = func(
        "loop_helper",
        sig(
            vec![
                param("world_iter", world_type(world_id)),
                param("world_snapshot", world_type(world_id)),
            ],
            Type::Tuple(vec![world_type(world_id)]),
        ),
        body(
            Vec::new(),
            Expr::Tuple(vec![Expr::Var("world_iter".into())]),
        ),
        FuncOpts {
            effects: Effects {
                world_writes: true,
                ..Effects::PURE
            },
            ..Default::default()
        },
    );
    helper.kind = FunctionKind::LoopBody { parent: 2, slot: 0 };
    program.functions.insert(1, helper);
    program.functions.insert(
        2,
        func(
            "caller",
            threaded_signature(world_id, Vec::new(), false),
            body(
                vec![
                    Stmt::Let {
                        pattern: vec![Some("world_1".into())],
                        value: call_step(WORLD_VAR),
                    },
                    Stmt::Let {
                        pattern: vec![Some("world_2".into())],
                        value: Expr::Call {
                            fun: 1,
                            type_args: Vec::new(),
                            args: vec![Expr::Var("world_1".into()), Expr::Var(WORLD_VAR.into())],
                        },
                    },
                ],
                Expr::Tuple(vec![Expr::Var("world_2".into())]),
            ),
            FuncOpts::default(),
        ),
    );

    check(&program, world_id).expect("later World params may be stable captured snapshots");

    let caller = program.functions.get_mut(&2).unwrap();
    let Stmt::Let {
        value: Expr::Call { args, .. },
        ..
    } = &mut caller.body.stmts[1]
    else {
        unreachable!()
    };
    args.swap(0, 1);
    stale(2, check(&program, world_id));
}

#[test]
fn newest_canonical_world_param_is_the_lifecycle_channel() {
    let mut program = program_with(Vec::new());
    let world_id = ensure_world_struct(&mut program);
    program.functions.insert(0, step(world_id));
    let mut helper = func(
        "continuation",
        sig(
            vec![
                param("world_0", world_type(world_id)),
                param("world_2", world_type(world_id)),
            ],
            Type::Tuple(vec![world_type(world_id)]),
        ),
        body(Vec::new(), Expr::Tuple(vec![Expr::Var("world_2".into())])),
        FuncOpts {
            effects: Effects {
                world_writes: true,
                ..Effects::PURE
            },
            ..Default::default()
        },
    );
    helper.kind = FunctionKind::Synthetic;
    program.functions.insert(1, helper);
    program.functions.insert(
        2,
        func(
            "caller",
            threaded_signature(world_id, Vec::new(), false),
            body(
                vec![
                    Stmt::Let {
                        pattern: vec![Some("world_1".into())],
                        value: call_step(WORLD_VAR),
                    },
                    Stmt::Let {
                        pattern: vec![Some("world_3".into())],
                        value: Expr::Call {
                            fun: 1,
                            type_args: Vec::new(),
                            args: vec![Expr::Var(WORLD_VAR.into()), Expr::Var("world_1".into())],
                        },
                    },
                ],
                Expr::Tuple(vec![Expr::Var("world_3".into())]),
            ),
            FuncOpts::default(),
        ),
    );

    check(&program, world_id).expect("the newest canonical World binder is the channel");

    let caller = program.functions.get_mut(&2).unwrap();
    let Stmt::Let {
        value: Expr::Call { args, .. },
        ..
    } = &mut caller.body.stmts[1]
    else {
        unreachable!()
    };
    args.swap(0, 1);
    stale(2, check(&program, world_id));
}

#[test]
fn abort_loop_live_accumulator_is_the_lifecycle_channel() {
    let mut program = program_with(Vec::new());
    let world_id = ensure_world_struct(&mut program);
    program.functions.insert(0, step(world_id));
    let mut sink = func(
        "sink",
        sig(vec![param(WORLD_VAR, world_type(world_id))], Type::UInt(64)),
        body(Vec::new(), lit_u64(7)),
        FuncOpts {
            effects: Effects::PURE,
            ..Default::default()
        },
    );
    sink.kind = FunctionKind::Synthetic;
    program.functions.insert(4, sink);

    for (fid, (name, lifecycle_var, kind)) in [
        (
            1,
            (
                "source.aborts.while_0.after",
                "__la_world_a",
                FunctionKind::LoopAfter { parent: 3, slot: 0 },
            ),
        ),
        (
            2,
            (
                "source.aborts.while_0_step",
                "__la_world_w",
                FunctionKind::Synthetic,
            ),
        ),
    ] {
        let mut helper = func(
            name,
            sig(
                vec![
                    param("world_0", world_type(world_id)),
                    param(lifecycle_var, world_type(world_id)),
                ],
                Type::UInt(64),
            ),
            body(
                Vec::new(),
                Expr::Call {
                    fun: 4,
                    type_args: Vec::new(),
                    args: vec![Expr::Var(lifecycle_var.into())],
                },
            ),
            FuncOpts {
                effects: Effects::PURE,
                ..Default::default()
            },
        );
        helper.kind = kind;
        program.functions.insert(fid, helper);
    }

    check(&program, world_id).expect("live abort-loop captures carry the continuation World");

    for fid in [1, 2] {
        let helper = program.functions.get_mut(&fid).unwrap();
        let BlockTail::Value(Expr::Call { args, .. }) = &mut helper.body.tail else {
            unreachable!()
        };
        args[0] = Expr::Var("world_0".into());
        stale(fid, check(&program, world_id));
        let helper = program.functions.get_mut(&fid).unwrap();
        let BlockTail::Value(Expr::Call { args, .. }) = &mut helper.body.tail else {
            unreachable!()
        };
        args[0] = Expr::Var(
            if fid == 1 {
                "__la_world_a"
            } else {
                "__la_world_w"
            }
            .into(),
        );
    }

    program.functions.insert(
        3,
        func(
            "caller",
            threaded_signature(world_id, Vec::new(), false),
            body(
                vec![
                    Stmt::Let {
                        pattern: vec![Some("world_1".into())],
                        value: call_step(WORLD_VAR),
                    },
                    Stmt::Let {
                        pattern: vec![Some("value".into())],
                        value: Expr::Call {
                            fun: 1,
                            type_args: Vec::new(),
                            args: vec![Expr::Var(WORLD_VAR.into()), Expr::Var("world_1".into())],
                        },
                    },
                ],
                Expr::Tuple(vec![Expr::Var("world_1".into())]),
            ),
            FuncOpts::default(),
        ),
    );
    check(&program, world_id).expect("abort-helper calls consume their marked lifecycle World");

    let caller = program.functions.get_mut(&3).unwrap();
    let Stmt::Let {
        value: Expr::Call { args, .. },
        ..
    } = &mut caller.body.stmts[1]
    else {
        unreachable!()
    };
    args[1] = Expr::Var(WORLD_VAR.into());
    stale(3, check(&program, world_id));
}

#[test]
fn read_only_multi_world_helper_keeps_snapshot_params_out_of_lineage() {
    let mut program = program_with(Vec::new());
    let world_id = ensure_world_struct(&mut program);
    program.functions.insert(0, step(world_id));
    let mut helper = func(
        "loop_after",
        sig(
            vec![
                param("world_iter", world_type(world_id)),
                param("world_snapshot", world_type(world_id)),
            ],
            Type::UInt(64),
        ),
        body(Vec::new(), lit_u64(7)),
        FuncOpts {
            effects: Effects::PURE,
            ..Default::default()
        },
    );
    helper.kind = FunctionKind::LoopAfter { parent: 2, slot: 0 };
    program.functions.insert(1, helper);
    program.functions.insert(
        2,
        func(
            "caller",
            threaded_signature(world_id, Vec::new(), false),
            body(
                vec![
                    Stmt::Let {
                        pattern: vec![Some("world_1".into())],
                        value: call_step(WORLD_VAR),
                    },
                    Stmt::Let {
                        pattern: vec![Some("value".into())],
                        value: Expr::Call {
                            fun: 1,
                            type_args: Vec::new(),
                            args: vec![Expr::Var(WORLD_VAR.into()), Expr::Var("world_1".into())],
                        },
                    },
                ],
                Expr::Tuple(vec![Expr::Var("world_1".into())]),
            ),
            FuncOpts::default(),
        ),
    );

    check(&program, world_id)
        .expect("read-only helper World captures are snapshots rather than a lifecycle channel");
}

#[test]
fn duplicate_world_return_channels_are_rejected() {
    let mut program = program_with(Vec::new());
    let world_id = ensure_world_struct(&mut program);
    program.functions.insert(
        0,
        func(
            "caller",
            sig(
                vec![param(WORLD_VAR, world_type(world_id))],
                Type::Tuple(vec![world_type(world_id), world_type(world_id)]),
            ),
            body(
                Vec::new(),
                Expr::Tuple(vec![
                    Expr::Var(WORLD_VAR.into()),
                    Expr::Var(WORLD_VAR.into()),
                ]),
            ),
            FuncOpts::default(),
        ),
    );

    stale(0, check(&program, world_id));
}
