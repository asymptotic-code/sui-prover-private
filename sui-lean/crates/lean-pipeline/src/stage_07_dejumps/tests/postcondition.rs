//! Postcondition tests.
//!
//! Verify the postcondition checker fires on programs that violate
//! stage-7-rewrite's structural invariants, and passes on well-formed
//! post-stage-7 programs.

use crate::ir::builder::ProverFnIds;
use crate::ir::{
    Block, BlockTail, Expr, Function, FunctionKind, Module, Param, Program, Signature, SpecKind,
    Type, VarId,
};
use ethnum::U256;

use crate::stage_07_dejumps::postcondition::{check, classify_control_flow, PostconditionError};
use crate::stage_07_dejumps::{self, option_aborts};

fn module() -> Module {
    Module {
        name: "m".to_string(),
        package_name: "p".to_string(),
        address: String::new(),
        required_imports: Vec::new(),
        is_native: false,
    }
}

fn lit_u64(n: u64) -> Expr {
    Expr::Const(crate::ir::Const::UInt {
        bits: 64,
        value: U256::from(n),
    })
}

fn one_fn_program(body: Block) -> Program {
    let f = Function {
        module: 0,
        name: "f".to_string(),
        signature: Signature {
            type_params: Vec::new(),
            params: vec![Param {
                name: "x".to_string(),
                var: VarId::from("x"),
                ty: Type::UInt(64),
            }],
            return_type: Type::UInt(64),
        },
        body,
        kind: FunctionKind::Source,
        effects: crate::ir::Effects::CONSERVATIVE,
        explicit_pure: false,
    };
    let mut p = Program::default();
    p.modules.insert(0, module());
    p.functions.insert(0, f);
    p
}

#[test]
fn passes_on_clean_post_run_program() {
    // After stage_07_dejumps::run(), a simple program should satisfy
    // every postcondition invariant.
    let mut p = one_fn_program(Block {
        stmts: vec![],
        tail: BlockTail::Value(lit_u64(42)),
    });
    let ids = ProverFnIds::default();
    stage_07_dejumps::run(&mut p, &ids).expect("run");
    check(&p, &ids).expect("postcondition passes on clean post-run program");
}

#[test]
fn catches_missing_aborts_companion() {
    // Build a program that has a Source function but no Spec(Aborts)
    // companion. Postcondition should reject.
    let p = one_fn_program(Block {
        stmts: vec![],
        tail: BlockTail::Value(lit_u64(42)),
    });
    let ids = ProverFnIds::default();
    let err = check(&p, &ids).expect_err("expected postcondition failure");
    assert!(
        matches!(
            err,
            PostconditionError::MissingAbortsCompanion { source: 0 }
        ),
        "got {err:?}"
    );
}

#[test]
fn catches_aborts_companion_with_wrong_return_type() {
    // Build a Source function + a hand-crafted Spec(Aborts) whose
    // return type is Type::Bool (wrong shape -- should be
    // Option<MoveAbortCode>).
    let mut p = one_fn_program(Block {
        stmts: vec![],
        tail: BlockTail::Value(lit_u64(42)),
    });
    // Register the synthetic Option / MoveAbortCode so the
    // canonical-type lookup succeeds; otherwise the postcondition
    // can't even distinguish "wrong type" from "type missing".
    let _ = option_aborts::ensure_aborts_types(&mut p);
    p.functions.insert(
        1,
        Function {
            module: 0,
            name: "f.aborts".to_string(),
            signature: Signature {
                type_params: Vec::new(),
                params: Vec::new(),
                return_type: Type::Bool, // wrong shape
            },
            body: Block {
                stmts: vec![],
                tail: BlockTail::Value(Expr::Const(crate::ir::Const::Bool(false))),
            },
            kind: FunctionKind::Spec {
                kind: SpecKind::Aborts,
                target: 0,
            },
            effects: crate::ir::Effects::PURE,
            explicit_pure: false,
        },
    );
    let ids = ProverFnIds::default();
    let err = check(&p, &ids).expect_err("expected postcondition failure");
    assert!(
        matches!(
            err,
            PostconditionError::AbortsReturnTypeMismatch { variant: 1 }
        ),
        "got {err:?}"
    );
}

#[test]
fn catches_lingering_function_tail_return() {
    // Build a Source function whose body's tail is Return(_) (a
    // simulated "phase 2 forgot to collapse") + a well-formed
    // .aborts companion.
    let mut p = one_fn_program(Block {
        stmts: vec![],
        tail: BlockTail::Return(Box::new(lit_u64(42))),
    });
    // Register synth types + a well-formed .aborts companion so the
    // missing-companion check doesn't fire first.
    let types = option_aborts::ensure_aborts_types(&mut p);
    p.functions.insert(
        1,
        Function {
            module: 0,
            name: "f.aborts".to_string(),
            signature: Signature {
                type_params: Vec::new(),
                params: Vec::new(),
                return_type: types.option_abort_code_type(),
            },
            body: Block {
                stmts: vec![],
                tail: BlockTail::Value(Expr::Pack {
                    struct_id: types.option,
                    type_args: vec![types.abort_code_type()],
                    variant: Some(option_aborts::OPTION_NONE_TAG),
                    fields: vec![],
                }),
            },
            kind: FunctionKind::Spec {
                kind: SpecKind::Aborts,
                target: 0,
            },
            effects: crate::ir::Effects::PURE,
            explicit_pure: false,
        },
    );
    let ids = ProverFnIds::default();
    let err = check(&p, &ids).expect_err("expected postcondition failure");
    // Note: the actual error might be from the base validator
    // depending on order. Accept either signal.
    let acceptable = matches!(
        err,
        PostconditionError::LingeringFunctionTailReturn { function: 0 }
            | PostconditionError::BaseValidator(_)
    );
    assert!(acceptable, "got {err:?}");
}

#[test]
fn full_pipeline_with_predicates_runs_cleanly() {
    // Simulate a function that had prover::requires / prover::ensures
    // calls (would normally be removed in phase 1). We don't actually
    // register prover_ids here; the predicates dict is empty. This
    // just verifies the postcondition passes on a slightly more
    // complex program.
    let body = Block {
        stmts: vec![],
        tail: BlockTail::Abort {
            code: Box::new(lit_u64(99)),
        },
    };
    let mut p = one_fn_program(body);
    let ids = ProverFnIds::default();
    stage_07_dejumps::run(&mut p, &ids).expect("run");
    check(&p, &ids).expect("postcondition passes on a function with Abort");
}

fn clean_post_stage_7_program() -> (Program, ProverFnIds) {
    let mut program = one_fn_program(Block::just(lit_u64(42)));
    let ids = ProverFnIds::default();
    stage_07_dejumps::run(&mut program, &ids).expect("run");
    (program, ids)
}

#[test]
fn rejects_self_recursive_return_that_stage_7_cannot_lift() {
    let mut program = one_fn_program(Block {
        stmts: vec![crate::ir::Stmt::Eval(Expr::If {
            cond: Box::new(Expr::Const(crate::ir::Const::Bool(true))),
            then_branch: Box::new(Block {
                stmts: vec![],
                tail: BlockTail::Return(Box::new(lit_u64(1))),
            }),
            else_branch: Box::new(Block::just(lit_u64(2))),
        })],
        tail: BlockTail::Value(Expr::Call {
            fun: 0,
            type_args: vec![],
            args: vec![Expr::Var(VarId::from("x"))],
        }),
    });
    let ids = ProverFnIds::default();
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        stage_07_dejumps::run(&mut program, &ids)
    }));
    #[cfg(debug_assertions)]
    assert!(
        result.is_err(),
        "the debug stage boundary must reject a residual inner Return"
    );
    #[cfg(not(debug_assertions))]
    result
        .expect("stage run must not panic without debug postconditions")
        .expect("stage run");

    let summary = classify_control_flow(&program.functions[&0].body);
    assert!(!summary.function_tail_return);
    assert_eq!(summary.residual_inner_returns, 1);
    assert!(
        program
            .functions
            .values()
            .all(|function| !function.name.starts_with("f.cont_")),
        "self-recursive source must not be split into a continuation"
    );
    assert!(matches!(
        check(&program, &ids),
        Err(PostconditionError::LingeringInnerReturn { function: 0 })
    ));
}

#[test]
fn permits_outer_return_only_for_documented_helper_kind() {
    let (mut program, ids) = clean_post_stage_7_program();
    let function = program.functions.get_mut(&0).unwrap();
    function.kind = FunctionKind::LoopBody { parent: 0, slot: 0 };
    function.body.tail = BlockTail::Return(Box::new(lit_u64(1)));

    check(&program, &ids).expect("loop helper outer Return is permitted");
}

#[test]
fn rejects_every_forbidden_post_stage_7_control_form() {
    let cases = [
        (
            BlockTail::Break {
                level: 0,
                value: Box::new(lit_u64(1)),
            },
            "break",
        ),
        (
            BlockTail::Continue {
                level: 0,
                value: Box::new(lit_u64(1)),
            },
            "continue",
        ),
    ];
    for (tail, label) in cases {
        let (mut program, ids) = clean_post_stage_7_program();
        program.functions.get_mut(&0).unwrap().body.tail = tail;
        assert!(
            matches!(
                check(&program, &ids),
                Err(PostconditionError::LingeringBreakOrContinue { function: 0 })
            ),
            "{label} must fail the post-stage-7 contract"
        );
    }

    let (mut program, ids) = clean_post_stage_7_program();
    program.functions.get_mut(&0).unwrap().body.tail = BlockTail::ReturnFromBlock {
        level: 0,
        value: Box::new(lit_u64(1)),
    };
    assert!(matches!(
        check(&program, &ids),
        Err(PostconditionError::LingeringReturnFromBlock { function: 0 })
    ));

    let (mut program, ids) = clean_post_stage_7_program();
    program.functions.get_mut(&0).unwrap().body.tail = BlockTail::Value(Expr::LabeledBlock {
        body: Box::new(Block::just(lit_u64(1))),
        result_ty: Type::UInt(64),
    });
    assert!(matches!(
        check(&program, &ids),
        Err(PostconditionError::LingeringLabeledBlock { function: 0 })
    ));
}

#[test]
fn rejects_forbidden_control_form_nested_in_an_expression() {
    let (mut program, ids) = clean_post_stage_7_program();
    program.functions.get_mut(&0).unwrap().body.tail = BlockTail::Value(Expr::If {
        cond: Box::new(Expr::Const(crate::ir::Const::Bool(true))),
        then_branch: Box::new(Block {
            stmts: vec![],
            tail: BlockTail::Break {
                level: 0,
                value: Box::new(lit_u64(1)),
            },
        }),
        else_branch: Box::new(Block::just(lit_u64(2))),
    });

    assert!(matches!(
        check(&program, &ids),
        Err(PostconditionError::LingeringBreakOrContinue { function: 0 })
    ));
}

// ---------------------------------------------------------------------------
// Misfiled value chain under an `.aborts.` name.
//
// The shape the retype+splice pass declines to transform when an
// abortable callee precedes the labeled block: a VALUE loop ships under
// an `.aborts.` name, returning Bool rather than AbortResult, and every
// abortable callee it reaches has had its face dropped. Measured at 13
// clusters / 40 defs in sui-system.
// ---------------------------------------------------------------------------

/// Two Source functions, each with a well-formed `.aborts` companion,
/// plus one extra family member named `f.aborts.labeled_0.while_0`.
/// `misfiled` decides whether that member returns Bool (the bug) or the
/// canonical AbortResult (correct).
fn program_with_aborts_family_member(misfiled: bool) -> Program {
    let mut p = one_fn_program(Block {
        stmts: vec![],
        tail: BlockTail::Value(lit_u64(42)),
    });
    let types = option_aborts::ensure_aborts_types(&mut p);

    let mut source = |fid: usize, name: &str| {
        p.functions.insert(
            fid,
            Function {
                module: 0,
                name: name.to_string(),
                signature: Signature {
                    type_params: Vec::new(),
                    params: Vec::new(),
                    return_type: Type::UInt(64),
                },
                body: Block {
                    stmts: vec![],
                    tail: BlockTail::Value(lit_u64(1)),
                },
                kind: FunctionKind::Source,
                effects: crate::ir::Effects::CONSERVATIVE,
                explicit_pure: false,
            },
        );
    };
    // fid 2 is the abortable callee whose face would be dropped.
    source(2, "g");

    let mut aborts_companion = |fid: usize, name: &str, target: usize| {
        p.functions.insert(
            fid,
            Function {
                module: 0,
                name: name.to_string(),
                signature: Signature {
                    type_params: Vec::new(),
                    params: Vec::new(),
                    return_type: types.option_abort_code_type(),
                },
                body: Block {
                    stmts: vec![],
                    tail: BlockTail::Value(Expr::Pack {
                        struct_id: types.option,
                        type_args: vec![types.abort_code_type()],
                        variant: Some(option_aborts::OPTION_NONE_TAG),
                        fields: vec![],
                    }),
                },
                kind: FunctionKind::Spec {
                    kind: SpecKind::Aborts,
                    target,
                },
                effects: crate::ir::Effects::PURE,
                explicit_pure: false,
            },
        );
    };
    aborts_companion(1, "f.aborts", 0);
    aborts_companion(3, "g.aborts", 2);

    // The family member. It calls `g` -- which HAS an abort companion,
    // so `g` is an abort-map key and its face must not be dropped.
    p.functions.insert(
        4,
        Function {
            module: 0,
            name: "f.aborts.labeled_0.while_0".to_string(),
            signature: Signature {
                type_params: Vec::new(),
                params: Vec::new(),
                return_type: if misfiled {
                    Type::Bool
                } else {
                    types.option_abort_code_type()
                },
            },
            body: Block {
                stmts: vec![],
                tail: BlockTail::Value(if misfiled {
                    Expr::Call {
                        fun: 2,
                        type_args: vec![],
                        args: vec![],
                    }
                } else {
                    Expr::Pack {
                        struct_id: types.option,
                        type_args: vec![types.abort_code_type()],
                        variant: Some(option_aborts::OPTION_NONE_TAG),
                        fields: vec![],
                    }
                }),
            },
            kind: FunctionKind::Synthetic,
            effects: crate::ir::Effects::PURE,
            explicit_pure: false,
        },
    );
    p
}

#[test]
fn catches_misfiled_value_chain_under_an_aborts_name() {
    let p = program_with_aborts_family_member(true);
    let ids = ProverFnIds::default();
    let err = check(&p, &ids).expect_err("expected postcondition failure");
    assert!(
        matches!(
            err,
            PostconditionError::MisfiledAbortsFamilyValueChain {
                function: 4,
                dropped_callee: 2
            }
        ),
        "got {err:?}"
    );
}

#[test]
fn allows_a_correctly_retyped_aborts_family_member() {
    // Same shape, but the family member returns AbortResult -- i.e. the
    // retype+splice pass DID fire. Must not be flagged, or the check
    // would reject every correctly-converted chain.
    let p = program_with_aborts_family_member(false);
    let ids = ProverFnIds::default();
    check(&p, &ids).expect("correctly retyped family member must pass");
}
