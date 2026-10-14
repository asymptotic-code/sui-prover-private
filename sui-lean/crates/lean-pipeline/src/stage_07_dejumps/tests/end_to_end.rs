//! End-to-end tests for `stage_07_dejumps::run()`.
//!
//! Verifies that phase 1 (`.aborts` materialisation) + phase 2 step
//! 1 (function-tail Return collapse) compose correctly: an Abort at
//! the function tail flows through Return(Some(_)) and lands as
//! Value(Some(_)).

use crate::ir::builder::ProverFnIds;
use crate::ir::{
    AbortPayloadMode, Block, BlockTail, Expr, Function, FunctionKind, Module, Param, Program,
    Signature, SpecKind, Stmt, TestExpectation, Type, VarId,
};
use ethnum::U256;

use crate::stage_07_dejumps;
use crate::stage_07_dejumps::option_aborts::{
    ensure_aborts_types, OPTION_NONE_TAG, OPTION_SOME_TAG,
};
use crate::stage_07_dejumps::postcondition::classify_control_flow;

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

fn aborts_of(p: &Program, target: usize) -> Option<usize> {
    p.functions.iter().find_map(|(id, fn_)| {
        if let FunctionKind::Spec {
            kind: SpecKind::Aborts,
            target: t,
        } = fn_.kind
        {
            if t == target {
                return Some(*id);
            }
        }
        None
    })
}

#[test]
fn all_spec_companions_share_canonical_metadata() {
    const REQUIRES_ID: usize = 97;
    const ASSERTS_ID: usize = 98;
    const ENSURES_ID: usize = 99;

    let predicate = VarId::from("predicate");
    let spec_call = |fun| {
        crate::ir::Stmt::Eval(Expr::Call {
            fun,
            type_args: vec![],
            args: vec![Expr::Var(predicate.clone())],
        })
    };
    let body = Block {
        stmts: vec![
            crate::ir::Stmt::Let {
                pattern: vec![Some(predicate.clone())],
                value: Expr::Const(crate::ir::Const::Bool(true)),
            },
            spec_call(REQUIRES_ID),
            spec_call(ASSERTS_ID),
            spec_call(ENSURES_ID),
        ],
        tail: BlockTail::Value(lit_u64(0)),
    };
    let mut program = one_fn_program(body);
    program.functions.get_mut(&0).unwrap().signature.type_params = vec!["T".to_string()];
    stage_07_dejumps::run(
        &mut program,
        &ProverFnIds {
            requires: Some(REQUIRES_ID),
            ensures: Some(ENSURES_ID),
            asserts: Some(ASSERTS_ID),
        },
    )
    .expect("run end-to-end");
    let abort_return = ensure_aborts_types(&mut program).option_abort_code_type();

    let companion = |kind| {
        program
            .functions
            .iter()
            .find(|(_, f)| f.kind == (FunctionKind::Spec { kind, target: 0 }))
            .map(|(fid, f)| (*fid, f))
            .expect("spec companion emitted")
    };
    let (aborts_fid, aborts) = companion(SpecKind::Aborts);
    let (requires_fid, requires) = companion(SpecKind::Requires);
    let (asserts_fid, asserts) = companion(SpecKind::Asserts);
    let (ensures_fid, ensures) = companion(SpecKind::Ensures);

    assert_eq!(aborts.name, "f.aborts");
    assert_eq!(requires.name, "f.requires");
    assert_eq!(asserts.name, "f.asserts");
    assert_eq!(ensures.name, "f.ensures");
    assert!(aborts_fid < requires_fid);
    assert!(requires_fid < asserts_fid);
    assert!(asserts_fid < ensures_fid);

    for function in [aborts, requires, asserts, ensures] {
        assert_eq!(function.module, 0);
        assert_eq!(function.signature.type_params, ["T"]);
        assert_eq!(function.effects, crate::ir::Effects::PURE);
        assert!(!function.explicit_pure);
        assert_eq!(function.signature.params[0].var, VarId::from("x"));
    }
    assert_eq!(aborts.signature.params.len(), 1);
    assert_eq!(requires.signature.params.len(), 1);
    assert_eq!(asserts.signature.params.len(), 1);
    assert_eq!(ensures.signature.params.len(), 2);
    assert_eq!(ensures.signature.params[1].name, "result");
    assert_eq!(ensures.signature.params[1].ty, Type::UInt(64));
    assert_eq!(aborts.signature.return_type, abort_return);
    assert_eq!(
        classify_control_flow(&aborts.body).residual_inner_returns,
        0,
        "assert lowering must not leave an inner Return in the .aborts companion"
    );
    assert_eq!(requires.signature.return_type, Type::Prop);
    assert_eq!(asserts.signature.return_type, Type::Bool);
    assert_eq!(ensures.signature.return_type, Type::Prop);
}

#[test]
fn full_run_abort_tail_collapses_to_value_some() {
    // f.body = { tail: Abort{42} }
    // Expected after stage_07_dejumps::run():
    //   f.body unchanged (phase 2 doesn't touch source bodies' Aborts).
    //   f.aborts.body = { tail: Value(Some(MoveAbortCode{42})) }
    //     (phase 1 rewrote Abort -> Return(Some); phase 2 collapsed
    //     function-tail Return to Value.)
    let f_body = Block {
        stmts: vec![],
        tail: BlockTail::Abort {
            code: Box::new(lit_u64(42)),
        },
    };
    let mut p = one_fn_program(f_body);
    let ids = ProverFnIds::default();
    stage_07_dejumps::run(&mut p, &ids).expect("run end-to-end");

    let aborts_fid = aborts_of(&p, 0).expect("f.aborts emitted");
    let aborts = &p.functions[&aborts_fid];

    // Tail must be Value(Pack(Option, Some, [Pack(MoveAbortCode, [42])])).
    match &aborts.body.tail {
        BlockTail::Value(Expr::Pack {
            variant: Some(tag),
            fields,
            ..
        }) => {
            assert_eq!(
                *tag, OPTION_SOME_TAG,
                "function-tail collapsed to Value(Some(...))"
            );
            assert_eq!(fields.len(), 1);
            match &fields[0] {
                Expr::Pack { fields: inner, .. } => {
                    assert_eq!(inner.len(), 1, "MoveAbortCode {{ code }}");
                    assert_eq!(inner[0], lit_u64(42));
                }
                other => panic!("expected Pack(MoveAbortCode), got {other:?}"),
            }
        }
        other => panic!("expected Value(Pack(Some)), got {other:?}"),
    }
}

#[test]
fn observed_test_abort_carries_origin_tag() {
    let f_body = Block {
        stmts: vec![],
        tail: BlockTail::Abort {
            code: Box::new(lit_u64(42)),
        },
    };
    let mut p = one_fn_program(f_body);
    p.modules.get_mut(&0).unwrap().address = format!("{:064x}", 2);
    let ids = ProverFnIds::default();
    stage_07_dejumps::run_with_payload_mode(&mut p, &ids, AbortPayloadMode::ObservedTest)
        .expect("run observed test mode");

    let aborts_fid = aborts_of(&p, 0).expect("f.aborts emitted");
    let BlockTail::Value(Expr::Pack { fields, .. }) = &p.functions[&aborts_fid].body.tail else {
        panic!("expected abort-result pack")
    };
    let Expr::Pack {
        fields: payload, ..
    } = &fields[0]
    else {
        panic!("expected abort-code pack")
    };
    assert_eq!(
        payload,
        &vec![
            lit_u64(42),
            lit_u64(1),
            lit_u64(crate::ir::ObservedErrorKind::Abort.tag())
        ]
    );
    assert_eq!(p.structs[&payload_struct_id(&fields[0])].fields.len(), 3);
    assert_eq!(p.abort_provenance.document().origins[0].tag, 1);
    assert_eq!(p.abort_provenance.document().origins[0].module, "0x2::m");
}

#[test]
fn observed_test_program_normalizes_back_to_exact_proof_payload() {
    let f_body = Block {
        stmts: vec![],
        tail: BlockTail::Abort {
            code: Box::new(lit_u64(42)),
        },
    };
    let mut p = one_fn_program(f_body);
    p.modules.get_mut(&0).unwrap().address = format!("{:064x}", 2);
    stage_07_dejumps::run_with_payload_mode(
        &mut p,
        &ProverFnIds::default(),
        AbortPayloadMode::ObservedTest,
    )
    .expect("run observed test mode");

    crate::ir::AbortProvenance::configure(&mut p, AbortPayloadMode::Proof).unwrap();
    let types = ensure_aborts_types(&mut p);

    assert_eq!(
        p.structs[&types.abort_code]
            .fields
            .iter()
            .map(|field| field.name.as_str())
            .collect::<Vec<_>>(),
        vec!["code"]
    );
    assert_eq!(abort_payload(&p), &[lit_u64(42)]);
    crate::ir::validate::validate_program(&p).expect("normalized proof program is valid");
    assert!(!crate::render::render_program(&p)
        .expect("normalized proof program renders")
        .contains("origin_tag"));
}

#[test]
fn proof_program_normalizes_to_unknown_observed_origin() {
    let f_body = Block {
        stmts: vec![],
        tail: BlockTail::Abort {
            code: Box::new(lit_u64(42)),
        },
    };
    let mut p = one_fn_program(f_body);
    stage_07_dejumps::run(&mut p, &ProverFnIds::default()).expect("run proof mode");

    crate::ir::AbortProvenance::configure(&mut p, AbortPayloadMode::ObservedTest).unwrap();
    let types = ensure_aborts_types(&mut p);

    assert_eq!(p.structs[&types.abort_code].fields.len(), 3);
    assert_eq!(
        abort_payload(&p),
        &[
            lit_u64(42),
            lit_u64(0),
            lit_u64(crate::ir::ObservedErrorKind::Unknown.tag())
        ]
    );
    crate::ir::validate::validate_program(&p).expect("normalized test program is valid");
}

fn abort_payload(p: &Program) -> &[Expr] {
    let aborts_fid = aborts_of(p, 0).expect("f.aborts emitted");
    let BlockTail::Value(Expr::Pack { fields, .. }) = &p.functions[&aborts_fid].body.tail else {
        panic!("expected abort-result pack")
    };
    let Expr::Pack {
        fields: payload, ..
    } = &fields[0]
    else {
        panic!("expected abort-code pack")
    };
    payload
}

fn payload_struct_id(expr: &Expr) -> usize {
    match expr {
        Expr::Pack { struct_id, .. } => *struct_id,
        _ => panic!("expected pack"),
    }
}

#[test]
fn full_run_non_aborting_function_returns_value_none() {
    // f.body = { tail: Value(42) }
    // Expected: f.aborts.body = { tail: Value(None) }
    let f_body = Block {
        stmts: vec![],
        tail: BlockTail::Value(lit_u64(42)),
    };
    let mut p = one_fn_program(f_body);
    let ids = ProverFnIds::default();
    stage_07_dejumps::run(&mut p, &ids).expect("run end-to-end");

    let aborts_fid = aborts_of(&p, 0).expect("f.aborts emitted");
    let aborts = &p.functions[&aborts_fid];

    match &aborts.body.tail {
        BlockTail::Value(Expr::Pack {
            variant: Some(tag),
            fields,
            ..
        }) => {
            assert_eq!(*tag, OPTION_NONE_TAG, "function-tail Value -> Value(None)");
            assert!(fields.is_empty());
        }
        other => panic!("expected Value(Pack(None)), got {other:?}"),
    }
}

#[test]
fn full_run_explicit_return_tail_collapses() {
    // f.body = { tail: Return(99) }  -- explicit `return 99`
    // Expected: f.aborts.body = { tail: Value(None) }
    let f_body = Block {
        stmts: vec![],
        tail: BlockTail::Return(Box::new(lit_u64(99))),
    };
    let mut p = one_fn_program(f_body);
    let ids = ProverFnIds::default();
    stage_07_dejumps::run(&mut p, &ids).expect("run end-to-end");

    let aborts_fid = aborts_of(&p, 0).expect("f.aborts emitted");
    let aborts = &p.functions[&aborts_fid];

    match &aborts.body.tail {
        BlockTail::Value(Expr::Pack {
            variant: Some(tag), ..
        }) => {
            assert_eq!(
                *tag, OPTION_NONE_TAG,
                "Return(_) -> Return(None) (phase 1) -> Value(None) (phase 2)"
            );
        }
        other => panic!("expected Value(Pack(None)), got {other:?}"),
    }

    // Also: source f.body's Return should remain (phase 2 collapses
    // it to Value(99), but for the source variant which kept the
    // original return type u64). Phase 2 runs over Source bodies
    // too, so f.body.tail should now be Value(99).
    let source = &p.functions[&0];
    match &source.body.tail {
        BlockTail::Value(e) => assert_eq!(*e, lit_u64(99)),
        other => panic!("expected source body tail Value(99), got {other:?}"),
    }
}

#[test]
fn full_run_loop_extracts_to_helpers_for_aborts_variant_too() {
    // f.body = { stmts: [Eval(While {..., body: Block { tail:
    //   Continue { level: 0, value: Unit } } })], tail: Value(42) }
    // Expected: both f and f.aborts get LoopBody / LoopAfter
    // sibling helpers; their bodies have no surviving Expr::While.
    let while_expr = Expr::While {
        header: Box::new(Block {
            stmts: vec![],
            tail: BlockTail::Value(Expr::Unit),
        }),
        cond: Box::new(Expr::Const(crate::ir::Const::Bool(false))),
        body: Box::new(Block {
            stmts: vec![],
            tail: BlockTail::Continue {
                level: 0,
                value: Box::new(Expr::Unit),
            },
        }),
        iter_locals: Vec::new(),
        header_exit_locals: Vec::new(),
        live_out: vec![],
    };
    let f_body = Block {
        stmts: vec![crate::ir::Stmt::Eval(while_expr)],
        tail: BlockTail::Value(lit_u64(42)),
    };
    let mut p = one_fn_program(f_body);
    let ids = ProverFnIds::default();
    stage_07_dejumps::run(&mut p, &ids).expect("run end-to-end");

    // Find LoopBody / LoopAfter helpers for f (parent=0) and for
    // f.aborts (parent=aborts_fid).
    let aborts_fid = aborts_of(&p, 0).expect("f.aborts emitted");

    let mut helpers_for_f = 0u32;
    let mut helpers_for_aborts = 0u32;
    for fn_ in p.functions.values() {
        match fn_.kind {
            FunctionKind::LoopBody { parent, .. } | FunctionKind::LoopAfter { parent, .. } => {
                if parent == 0 {
                    helpers_for_f += 1;
                }
                if parent == aborts_fid {
                    helpers_for_aborts += 1;
                }
            }
            _ => {}
        }
    }
    assert_eq!(
        helpers_for_f, 2,
        "f has LoopBody + LoopAfter for its while_0"
    );
    assert_eq!(
        helpers_for_aborts, 2,
        "f.aborts has matching LoopBody + LoopAfter for its cloned while_0"
    );

    // No Expr::While should survive in either body.
    fn contains_while(b: &Block) -> bool {
        for s in &b.stmts {
            let e = match s {
                crate::ir::Stmt::Let { value, .. } => value,
                crate::ir::Stmt::Eval(e) => e,
            };
            if expr_contains_while(e) {
                return true;
            }
        }
        match &b.tail {
            BlockTail::Value(e) => expr_contains_while(e),
            _ => false,
        }
    }
    fn expr_contains_while(e: &Expr) -> bool {
        match e {
            Expr::While { .. } => true,
            Expr::If {
                then_branch,
                else_branch,
                ..
            } => contains_while(then_branch) || contains_while(else_branch),
            Expr::Match { cases, .. } => cases.iter().any(|a| contains_while(&a.body)),
            _ => false,
        }
    }
    let f = &p.functions[&0];
    let f_aborts = &p.functions[&aborts_fid];
    assert!(!contains_while(&f.body), "no surviving While in source f");
    assert!(
        !contains_while(&f_aborts.body),
        "no surviving While in f.aborts"
    );
}

#[test]
fn loop_after_receives_post_header_carried_values() {
    // Post-stage-5 shape for a loop whose header advances a carried token.
    // The cond-false edge runs after `tick_2` is produced, so LoopAfter must
    // receive `tick_2`, not the iteration-entry parameter `tick_1`.
    let while_expr = Expr::While {
        header: Box::new(Block {
            stmts: vec![Stmt::Let {
                pattern: vec![Some("tick_2".into())],
                value: Expr::BinOp {
                    op: crate::ir::ops::BinOp::Add,
                    lhs: Box::new(Expr::Var("tick_1".into())),
                    rhs: Box::new(lit_u64(1)),
                },
            }],
            tail: BlockTail::Value(Expr::Unit),
        }),
        cond: Box::new(Expr::Const(crate::ir::Const::Bool(false))),
        body: Box::new(Block {
            stmts: vec![],
            tail: BlockTail::Value(Expr::Tuple(vec![
                Expr::Var("i_1".into()),
                Expr::Var("tick_2".into()),
            ])),
        }),
        iter_locals: vec![
            ("i_1".into(), Expr::Var("i_0".into())),
            ("tick_1".into(), Expr::Var("tick_0".into())),
        ],
        header_exit_locals: vec!["i_1".into(), "tick_2".into()],
        live_out: vec![],
    };
    let mut program = one_fn_program(Block {
        stmts: vec![Stmt::Let {
            pattern: vec![Some("i_3".into()), Some("tick_3".into())],
            value: while_expr,
        }],
        tail: BlockTail::Value(Expr::Var("tick_3".into())),
    });
    program.functions.get_mut(&0).unwrap().signature.params = vec![
        Param {
            name: "i_0".into(),
            var: "i_0".into(),
            ty: Type::UInt(64),
        },
        Param {
            name: "tick_0".into(),
            var: "tick_0".into(),
            ty: Type::UInt(64),
        },
    ];

    stage_07_dejumps::run(&mut program, &ProverFnIds::default()).expect("extract loop");

    let loop_body = program
        .functions
        .values()
        .find(|f| matches!(f.kind, FunctionKind::LoopBody { parent: 0, .. }))
        .expect("source LoopBody helper");
    let BlockTail::Value(Expr::If { else_branch, .. }) = &loop_body.body.tail else {
        panic!("expected LoopBody to end in the loop condition");
    };
    let BlockTail::Value(Expr::Call { args, .. }) = &else_branch.tail else {
        panic!("expected condition-false LoopAfter call");
    };
    assert_eq!(
        &args[..2],
        &[Expr::Var("i_1".into()), Expr::Var("tick_2".into())],
        "LoopAfter must receive the state produced by the header"
    );
}

#[test]
fn nested_loop_after_captures_outer_header_binding() {
    let inner = Expr::While {
        header: Box::new(Block::just(Expr::Unit)),
        cond: Box::new(Expr::Const(crate::ir::Const::Bool(false))),
        body: Box::new(Block::just(Expr::Unit)),
        iter_locals: vec![],
        header_exit_locals: vec![],
        live_out: vec![],
    };
    let outer = Expr::While {
        header: Box::new(Block {
            stmts: vec![Stmt::Let {
                pattern: vec![Some("header_value".into())],
                value: lit_u64(7),
            }],
            tail: BlockTail::Value(Expr::Unit),
        }),
        cond: Box::new(Expr::Const(crate::ir::Const::Bool(true))),
        body: Box::new(Block {
            stmts: vec![
                Stmt::Eval(inner),
                Stmt::Eval(Expr::Var("header_value".into())),
            ],
            tail: BlockTail::Continue {
                level: 0,
                value: Box::new(Expr::Unit),
            },
        }),
        iter_locals: vec![],
        header_exit_locals: vec![],
        live_out: vec![],
    };
    let mut program = one_fn_program(Block {
        stmts: vec![Stmt::Eval(outer)],
        tail: BlockTail::Value(Expr::Unit),
    });

    stage_07_dejumps::run(&mut program, &ProverFnIds::default()).expect("extract nested loops");
    crate::ir::validate::validate_program(&program)
        .expect("nested continuation must bind the outer header capture");
}

#[test]
fn conditional_break_handoff_is_not_discarded_by_eval() {
    let conditional_break = Expr::If {
        cond: Box::new(Expr::Const(crate::ir::Const::Bool(true))),
        then_branch: Box::new(Block {
            stmts: vec![],
            tail: BlockTail::Break {
                level: 0,
                value: Box::new(Expr::Unit),
            },
        }),
        else_branch: Box::new(Block::just(Expr::Unit)),
    };
    let while_expr = Expr::While {
        header: Box::new(Block::just(Expr::Unit)),
        cond: Box::new(Expr::Const(crate::ir::Const::Bool(true))),
        body: Box::new(Block {
            stmts: vec![Stmt::Eval(conditional_break)],
            tail: BlockTail::Continue {
                level: 0,
                value: Box::new(Expr::Unit),
            },
        }),
        iter_locals: vec![],
        header_exit_locals: vec![],
        live_out: vec![],
    };
    let mut program = one_fn_program(Block {
        stmts: vec![Stmt::Eval(while_expr)],
        tail: BlockTail::Value(lit_u64(42)),
    });

    stage_07_dejumps::run(&mut program, &ProverFnIds::default()).expect("run end-to-end");

    let after_id = program
        .functions
        .iter()
        .find_map(|(id, function)| {
            matches!(function.kind, FunctionKind::LoopAfter { parent: 0, .. }).then_some(*id)
        })
        .expect("source loop-after helper");
    let body = program
        .functions
        .values()
        .find(|function| matches!(function.kind, FunctionKind::LoopBody { parent: 0, .. }))
        .expect("source loop-body helper");

    struct HandoffCalls {
        target: usize,
        eval_depth: usize,
        total: usize,
        discarded: bool,
    }

    impl crate::ir::visit::Visitor for HandoffCalls {
        fn visit_stmt(&mut self, stmt: &Stmt) {
            let is_eval = matches!(stmt, Stmt::Eval(_));
            self.eval_depth += usize::from(is_eval);
            crate::ir::visit::walk_stmt_default(self, stmt);
            self.eval_depth -= usize::from(is_eval);
        }

        fn visit_expr(&mut self, expr: &Expr) {
            if matches!(expr, Expr::Call { fun, .. } if *fun == self.target) {
                self.total += 1;
                self.discarded |= self.eval_depth > 0;
            }
            crate::ir::visit::walk_expr_default(self, expr);
        }
    }

    let mut calls = HandoffCalls {
        target: after_id,
        eval_depth: 0,
        total: 0,
        discarded: false,
    };
    crate::ir::visit::Visitor::visit_block(&mut calls, &body.body);
    assert!(calls.total > 0, "loop body must retain its exit handoff");
    assert!(
        !calls.discarded,
        "a conditional break must exit through LoopAfter, not evaluate and discard its result"
    );
}

#[test]
fn operand_nested_break_is_rejected_before_losing_its_evaluation_context() {
    let conditional_break = Expr::If {
        cond: Box::new(Expr::Const(crate::ir::Const::Bool(true))),
        then_branch: Box::new(Block {
            stmts: vec![],
            tail: BlockTail::Break {
                level: 0,
                value: Box::new(Expr::Unit),
            },
        }),
        else_branch: Box::new(Block::just(lit_u64(1))),
    };
    let while_expr = Expr::While {
        header: Box::new(Block::just(Expr::Unit)),
        cond: Box::new(Expr::Const(crate::ir::Const::Bool(true))),
        body: Box::new(Block {
            stmts: vec![Stmt::Eval(Expr::BinOp {
                op: crate::ir::ops::BinOp::Add,
                lhs: Box::new(conditional_break),
                rhs: Box::new(lit_u64(2)),
            })],
            tail: BlockTail::Continue {
                level: 0,
                value: Box::new(Expr::Unit),
            },
        }),
        iter_locals: vec![],
        header_exit_locals: vec![],
        live_out: vec![],
    };
    let mut program = one_fn_program(Block {
        stmts: vec![Stmt::Eval(while_expr)],
        tail: BlockTail::Value(lit_u64(42)),
    });

    assert_eq!(
        stage_07_dejumps::run(&mut program, &ProverFnIds::default()),
        Err(stage_07_dejumps::Stage7Error::JumpInOperand)
    );
}

#[test]
fn header_exit_arity_mismatch_names_the_offending_function() {
    // A stage-5-shaped `While` -- one loop-carried `iter_locals` slot --
    // paired with the stages-1-4 empty `header_exit_locals`. Stage 7 builds
    // the cond-false `LoopAfter` call from `header_exit_locals`, so lowering
    // this would emit a zero-arg call to a one-param helper.
    //
    // The error must carry the parent's identity: two bare integers are
    // undiagnosable in a package with thousands of functions, and the only
    // recovery is bisecting the corpus.
    let while_expr = Expr::While {
        header: Box::new(Block::just(Expr::Unit)),
        cond: Box::new(Expr::Const(crate::ir::Const::Bool(true))),
        body: Box::new(Block {
            stmts: vec![],
            tail: BlockTail::Continue {
                level: 0,
                value: Box::new(Expr::Var(VarId::from("i_loop"))),
            },
        }),
        iter_locals: vec![(VarId::from("i_loop"), lit_u64(0))],
        header_exit_locals: vec![],
        live_out: vec![],
    };
    let mut program = one_fn_program(Block {
        stmts: vec![Stmt::Eval(while_expr)],
        tail: BlockTail::Value(lit_u64(42)),
    });

    assert_eq!(
        stage_07_dejumps::run(&mut program, &ProverFnIds::default()),
        Err(stage_07_dejumps::Stage7Error::HeaderExitArityMismatch {
            function: 0,
            function_name: "f".to_string(),
            expected: 1,
            found: 0,
        })
    );
}

// ---------------------------------------------------------------------------
// Structural `.ensures` reconstruction: branch-distributed predicates keep
// their `if` guard instead of being flattened into an unconditional `&&`.
// ---------------------------------------------------------------------------

const ENSURES_ID: usize = 99;

fn ensures_call(pred: Expr) -> crate::ir::Stmt {
    crate::ir::Stmt::Eval(Expr::Call {
        fun: ENSURES_ID,
        type_args: vec![],
        args: vec![pred],
    })
}

/// `let <name> := true` plus the `Var(<name>)` to use as a predicate, so
/// the predicate references a bound var (the postcondition validator
/// rejects unbound vars). The bool value is irrelevant to the structure.
fn bound_pred(name: &str) -> (crate::ir::Stmt, Expr) {
    let v = VarId::from(name);
    (
        crate::ir::Stmt::Let {
            pattern: vec![Some(v.clone())],
            value: Expr::Const(crate::ir::Const::Bool(true)),
        },
        Expr::Var(v),
    )
}

fn ensures_of(p: &Program, target: usize) -> Option<usize> {
    p.functions.iter().find_map(|(id, fn_)| {
        if let FunctionKind::Spec {
            kind: SpecKind::Ensures,
            target: t,
        } = fn_.kind
        {
            if t == target {
                return Some(*id);
            }
        }
        None
    })
}

fn run_with_ensures(body: Block) -> Program {
    let mut p = one_fn_program(body);
    let ids = ProverFnIds {
        requires: None,
        ensures: Some(ENSURES_ID),
        asserts: None,
    };
    stage_07_dejumps::run(&mut p, &ids).expect("run end-to-end");
    p
}

#[test]
fn ensures_in_both_branches_keeps_if_not_flat_conjunction() {
    // f.body = { eval if c { ensures!(A) } else { ensures!(B) }; 0 }
    // Expected .ensures tail = If { then: A, else: B } -- NOT `A && B`.
    let (let_a, a) = bound_pred("pa");
    let (let_b, b) = bound_pred("pb");
    let if_expr = Expr::If {
        cond: Box::new(Expr::Const(crate::ir::Const::Bool(true))),
        then_branch: Box::new(Block {
            stmts: vec![let_a, ensures_call(a.clone())],
            tail: BlockTail::Value(Expr::Unit),
        }),
        else_branch: Box::new(Block {
            stmts: vec![let_b, ensures_call(b.clone())],
            tail: BlockTail::Value(Expr::Unit),
        }),
    };
    let body = Block {
        stmts: vec![crate::ir::Stmt::Eval(if_expr)],
        tail: BlockTail::Value(lit_u64(0)),
    };
    let p = run_with_ensures(body);
    let ens = &p.functions[&ensures_of(&p, 0).expect(".ensures emitted")];
    match &ens.body.tail {
        BlockTail::Value(Expr::If {
            then_branch,
            else_branch,
            ..
        }) => {
            assert_eq!(
                then_branch.tail,
                BlockTail::Value(a),
                "then branch predicate preserved"
            );
            assert_eq!(
                else_branch.tail,
                BlockTail::Value(b),
                "else branch predicate preserved"
            );
        }
        other => panic!("expected conditional If ensures, got {other:?} (flattened to A && B?)"),
    }
}

#[test]
fn ensures_in_one_branch_only_guards_with_true_else() {
    // f.body = { eval if c { ensures!(A) } else { }; 0 }
    // Expected .ensures tail = If { then: A, else: true } == `c -> A`.
    let (let_a, a) = bound_pred("pa");
    let if_expr = Expr::If {
        cond: Box::new(Expr::Const(crate::ir::Const::Bool(true))),
        then_branch: Box::new(Block {
            stmts: vec![let_a, ensures_call(a.clone())],
            tail: BlockTail::Value(Expr::Unit),
        }),
        else_branch: Box::new(Block {
            stmts: vec![],
            tail: BlockTail::Value(Expr::Unit),
        }),
    };
    let body = Block {
        stmts: vec![crate::ir::Stmt::Eval(if_expr)],
        tail: BlockTail::Value(lit_u64(0)),
    };
    let p = run_with_ensures(body);
    let ens = &p.functions[&ensures_of(&p, 0).expect(".ensures emitted")];
    match &ens.body.tail {
        BlockTail::Value(Expr::If {
            then_branch,
            else_branch,
            ..
        }) => {
            assert_eq!(then_branch.tail, BlockTail::Value(a));
            assert_eq!(
                else_branch.tail,
                BlockTail::Value(Expr::Const(crate::ir::Const::Bool(true))),
                "empty else branch contributes `true`"
            );
        }
        other => panic!("expected guarded If ensures, got {other:?}"),
    }
}

#[test]
fn flat_top_level_ensures_stay_a_conjunction() {
    // f.body = { ensures!(A); ensures!(B); 0 } -- no branches.
    // Expected .ensures tail = `A && B` (regression guard: structural
    // builder must not change flat specs).
    let (let_a, a) = bound_pred("pa");
    let (let_b, b) = bound_pred("pb");
    let body = Block {
        stmts: vec![
            let_a,
            ensures_call(a.clone()),
            let_b,
            ensures_call(b.clone()),
        ],
        tail: BlockTail::Value(lit_u64(0)),
    };
    let p = run_with_ensures(body);
    let ens = &p.functions[&ensures_of(&p, 0).expect(".ensures emitted")];
    match &ens.body.tail {
        BlockTail::Value(Expr::BinOp {
            op: crate::ir::ops::BinOp::And,
            lhs,
            rhs,
        }) => {
            assert_eq!(**lhs, a);
            assert_eq!(**rhs, b);
        }
        other => panic!("expected flat `A && B`, got {other:?}"),
    }
}

fn source_program_with_effects(body: Block, effects: crate::ir::Effects) -> Program {
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
        effects,
        explicit_pure: false,
    };
    let mut p = Program::default();
    p.modules.insert(0, module());
    p.functions.insert(0, f);
    p
}

/// `if c1 { if c2 { return 1 } }; return 2` -- the inner `return 1`
/// sits in a statement-position (discarded) `if` nested two deep,
/// mirroring `oracle::strategy::validate_price_range_and_history`'s
/// dropped third `return false`.
fn nested_inner_return_body() -> Block {
    let inner_if = Expr::If {
        cond: Box::new(Expr::Const(crate::ir::Const::Bool(true))),
        then_branch: Box::new(Block {
            stmts: vec![],
            tail: BlockTail::Return(Box::new(lit_u64(1))),
        }),
        else_branch: Box::new(Block {
            stmts: vec![],
            tail: BlockTail::Value(Expr::Unit),
        }),
    };
    let outer_if = Expr::If {
        cond: Box::new(Expr::Const(crate::ir::Const::Bool(true))),
        then_branch: Box::new(Block {
            stmts: vec![crate::ir::Stmt::Eval(inner_if)],
            tail: BlockTail::Value(Expr::Unit),
        }),
        else_branch: Box::new(Block {
            stmts: vec![],
            tail: BlockTail::Value(Expr::Unit),
        }),
    };
    Block {
        stmts: vec![crate::ir::Stmt::Eval(outer_if)],
        tail: BlockTail::Return(Box::new(lit_u64(2))),
    }
}

/// True iff any `Stmt::Eval(If/Match)` in `b` (recursively) has a
/// branch whose tail is a `BlockTail::Return` -- the statement-position
/// inner return the renderer silently drops.
fn block_has_stmt_position_return(b: &Block) -> bool {
    fn block_tail_returns(b: &Block) -> bool {
        matches!(b.tail, BlockTail::Return(_))
    }
    for s in &b.stmts {
        let e = match s {
            crate::ir::Stmt::Eval(e) => e,
            crate::ir::Stmt::Let { value, .. } => value,
        };
        if let Expr::If {
            then_branch,
            else_branch,
            ..
        } = e
        {
            if block_tail_returns(then_branch)
                || block_tail_returns(else_branch)
                || block_has_stmt_position_return(then_branch)
                || block_has_stmt_position_return(else_branch)
            {
                return true;
            }
        }
    }
    false
}

#[test]
fn nomut_source_nested_inner_return_is_lifted() {
    // A PURE (`NoMut`) source body with a two-deep statement-position
    // inner return must be lifted: return_lift extracts a Synthetic
    // continuation so no statement-position `Return` -- which the
    // renderer would drop -- survives.
    let mut p = source_program_with_effects(nested_inner_return_body(), crate::ir::Effects::PURE);
    stage_07_dejumps::run(&mut p, &ProverFnIds::default()).expect("run");
    assert!(
        p.functions
            .values()
            .any(|f| matches!(f.kind, FunctionKind::Synthetic)),
        "NoMut source with a nested inner return must be lifted (cont helper created)"
    );
    for f in p.functions.values() {
        if matches!(f.kind, FunctionKind::Source | FunctionKind::Synthetic) {
            assert!(
                !block_has_stmt_position_return(&f.body),
                "statement-position inner Return survived lifting in `{}`",
                f.name
            );
        }
    }
}

#[test]
fn test_function_nested_inner_return_is_lifted() {
    let mut p = source_program_with_effects(nested_inner_return_body(), crate::ir::Effects::PURE);
    p.functions.get_mut(&0).unwrap().kind = FunctionKind::Test {
        expectation: TestExpectation::MustSucceed,
    };

    stage_07_dejumps::run(&mut p, &ProverFnIds::default()).expect("run");

    for f in p.functions.values() {
        if matches!(f.kind, FunctionKind::Test { .. } | FunctionKind::Synthetic) {
            assert!(
                !block_has_stmt_position_return(&f.body),
                "statement-position inner Return survived lifting in `{}`",
                f.name
            );
        }
    }
}

#[test]
fn localmut_source_safe_inner_return_is_lifted() {
    // An effectful (`LocalMut`/`GlobalMut`) source body whose inner return
    // is SAFE to lift -- no continuation captures an outstanding nested
    // `&mut` borrow and the body is not self-recursive -- IS lifted, just
    // like the `NoMut` case. stage_04_effects already augments the inner
    // return with the threaded mutables/world; the lift only preserves it.
    // (This fixture threads no `&mut` at all, so it is trivially safe.)
    let effects = crate::ir::Effects {
        aborts: crate::ir::AbortBit::Partial,
        det: crate::ir::DetBit::Det,
        mutation: crate::ir::MutLevel::LocalMut,
        world_writes: false,
    };
    let mut p = source_program_with_effects(nested_inner_return_body(), effects);
    stage_07_dejumps::run(&mut p, &ProverFnIds::default()).expect("run");
    assert!(
        p.functions
            .values()
            .any(|f| matches!(f.kind, FunctionKind::Synthetic)),
        "safe effectful source with a nested inner return must be lifted (cont helper created)"
    );
    for f in p.functions.values() {
        if matches!(f.kind, FunctionKind::Source | FunctionKind::Synthetic) {
            assert!(
                !block_has_stmt_position_return(&f.body),
                "statement-position inner Return survived lifting in `{}`",
                f.name
            );
        }
    }
}

#[test]
fn mutable_threaded_inner_return_uses_single_in_place_continuation() {
    let declared_root_type = Type::MutableRef {
        inner: Box::new(Type::UInt(64)),
        root: Box::new(Type::UInt(64)),
    };
    let projected_root_type = Type::MutableRef {
        inner: Box::new(Type::UInt(64)),
        root: Box::new(Type::Vector(Box::new(Type::UInt(64)))),
    };
    let nested_type = Type::MutableRef {
        inner: Box::new(Type::Vector(Box::new(Type::UInt(64)))),
        root: Box::new(Type::UInt(64)),
    };
    let return_value = || Expr::Tuple(vec![Expr::Var(VarId::from("state"))]);
    let inner = Expr::If {
        cond: Box::new(Expr::Const(crate::ir::Const::Bool(true))),
        then_branch: Box::new(Block {
            stmts: Vec::new(),
            tail: BlockTail::Return(Box::new(return_value())),
        }),
        else_branch: Box::new(Block::just(Expr::Unit)),
    };
    let outer = Expr::If {
        cond: Box::new(Expr::Const(crate::ir::Const::Bool(true))),
        then_branch: Box::new(Block {
            stmts: vec![crate::ir::Stmt::Eval(inner)],
            tail: BlockTail::Value(Expr::Unit),
        }),
        else_branch: Box::new(Block::just(Expr::Unit)),
    };
    let function = Function {
        module: 0,
        name: "f".into(),
        signature: Signature {
            type_params: Vec::new(),
            params: vec![
                Param {
                    name: "state".into(),
                    var: "state".into(),
                    ty: projected_root_type,
                },
                Param {
                    name: "nested".into(),
                    var: "nested".into(),
                    ty: nested_type,
                },
            ],
            return_type: Type::Tuple(vec![declared_root_type]),
        },
        body: Block {
            stmts: vec![
                crate::ir::Stmt::Eval(outer),
                crate::ir::Stmt::Eval(Expr::Var("nested".into())),
            ],
            tail: BlockTail::Value(return_value()),
        },
        kind: FunctionKind::Source,
        effects: crate::ir::Effects {
            aborts: crate::ir::AbortBit::Partial,
            det: crate::ir::DetBit::Det,
            mutation: crate::ir::MutLevel::LocalMut,
            world_writes: false,
        },
        explicit_pure: false,
    };
    let mut program = Program::default();
    program.modules.insert(0, module());
    program.functions.insert(0, function);

    stage_07_dejumps::run(&mut program, &ProverFnIds::default()).expect("run");

    let source = &program.functions[&0];
    assert_eq!(
        classify_control_flow(&source.body).residual_inner_returns,
        0
    );
    assert!(
        !program.functions.values().any(|function| {
            matches!(function.kind, FunctionKind::Synthetic) && function.name.starts_with("f.cont_")
        }),
        "the source continuation must stay in place instead of capturing the nested borrow"
    );

    struct VarCounter<'a> {
        target: &'a str,
        count: usize,
    }
    impl crate::ir::visit::Visitor for VarCounter<'_> {
        fn visit_var(&mut self, var: &VarId) {
            if var.as_ref() == self.target {
                self.count += 1;
            }
        }
    }
    let count_in = |block: &Block| {
        let mut counter = VarCounter {
            target: "nested",
            count: 0,
        };
        crate::ir::visit::Visitor::visit_block(&mut counter, block);
        counter.count
    };

    let BlockTail::Value(Expr::Match {
        struct_id, cases, ..
    }) = &source.body.tail
    else {
        panic!("mutable-threaded return must lower through a carrier match")
    };
    let option_id = program
        .structs
        .iter()
        .find_map(|(id, decl)| {
            (decl.qualified_name == crate::stage_07_dejumps::option_aborts::OPTION_QUALIFIED_NAME)
                .then_some(*id)
        })
        .expect("carrier type");
    assert_eq!(*struct_id, option_id);
    let no_return = cases
        .iter()
        .find(|arm| arm.variant == OPTION_NONE_TAG)
        .expect("NoAbort arm");
    let returned = cases
        .iter()
        .find(|arm| arm.variant == OPTION_SOME_TAG)
        .expect("Aborted arm");
    assert_eq!(count_in(&no_return.body), 1);
    assert_eq!(count_in(&returned.body), 0);
    assert_eq!(count_in(&source.body), 1, "continuation must not be cloned");

    use crate::ir::invariants::Invariant;
    assert!(
        crate::ir::invariants::baseline::PackFieldValueTypesMatchStructDefinition
            .check(&program)
            .is_ok()
    );
    assert!(
        crate::ir::invariants::baseline::PackFieldTypesMatchStructDefinition
            .check(&program)
            .is_ok()
    );
}

#[test]
fn asymmetric_loop_continue_stays_direct_self_recursion() {
    let state_type = Type::MutableRef {
        inner: Box::new(Type::UInt(64)),
        root: Box::new(Type::UInt(64)),
    };
    let self_call = || Expr::Call {
        fun: 0,
        type_args: Vec::new(),
        args: vec![Expr::Var("state".into())],
    };
    let function = Function {
        module: 0,
        name: "while_1".into(),
        signature: Signature {
            type_params: Vec::new(),
            params: vec![Param {
                name: "state".into(),
                var: "state".into(),
                ty: state_type.clone(),
            }],
            return_type: state_type,
        },
        body: Block {
            stmts: vec![Stmt::Eval(Expr::If {
                cond: Box::new(Expr::Const(crate::ir::Const::Bool(true))),
                then_branch: Box::new(Block {
                    stmts: Vec::new(),
                    tail: BlockTail::Return(Box::new(self_call())),
                }),
                else_branch: Box::new(Block::just(Expr::Unit)),
            })],
            tail: BlockTail::Value(self_call()),
        },
        kind: FunctionKind::LoopBody { parent: 1, slot: 0 },
        effects: crate::ir::Effects::CONSERVATIVE,
        explicit_pure: false,
    };
    let mut program = Program::default();
    program.modules.insert(0, module());
    program.functions.insert(0, function);
    ensure_aborts_types(&mut program);

    stage_07_dejumps::run(&mut program, &ProverFnIds::default()).expect("run");

    let loop_body = &program.functions[&0];
    assert!(loop_body.body.stmts.is_empty());
    let BlockTail::Value(Expr::If {
        then_branch,
        else_branch,
        ..
    }) = &loop_body.body.tail
    else {
        panic!("asymmetric continue must lower to a tail conditional")
    };
    for branch in [then_branch, else_branch] {
        assert!(matches!(
            branch.tail,
            BlockTail::Value(Expr::Call { fun: 0, .. })
        ));
    }
}

#[test]
fn nested_loop_helpers_agree_with_enclosing_loop_return_type() {
    // Regression for the mis-typed inner loop helpers behind
    // sui-system's `insertion_sort_by!` expansion in
    // `process_pending_removals` (see `insert_placeholder` and
    // extract_while's Phase B): an OUTER while in an `if` arm whose
    // post-loop continuation type -- here `(u64, u64)` -- differs
    // from the parent function's return type (`u64`), with an INNER
    // while whose continuation re-enters the outer loop. The inner
    // helpers must carry the outer loop family's return type, not the
    // parent function's: before the placeholder-patching fix, the
    // inner's Phase B resolved its `Call(outer_body)` tail off the
    // outer's placeholder signature, which still carried the parent
    // return type.
    let a = VarId::from("a");
    let b = VarId::from("b");
    let a1 = VarId::from("a1");
    let b1 = VarId::from("b1");
    let a2 = VarId::from("a2");
    let b2 = VarId::from("b2");
    let c = VarId::from("c");
    let c1 = VarId::from("c1");
    let cv = VarId::from("cv");
    let cv2 = VarId::from("cv2");

    let inner_while = Expr::While {
        header: Box::new(Block {
            stmts: vec![Stmt::Let {
                pattern: vec![Some(cv2.clone())],
                value: Expr::Const(crate::ir::Const::Bool(false)),
            }],
            tail: BlockTail::Value(Expr::Unit),
        }),
        cond: Box::new(Expr::Var(cv2.clone())),
        body: Box::new(Block {
            stmts: vec![],
            tail: BlockTail::Value(Expr::Tuple(vec![Expr::Var(c.clone())])),
        }),
        iter_locals: vec![(c.clone(), Expr::Var(a.clone()))],
        header_exit_locals: vec![c.clone()],
        live_out: vec![],
    };
    let outer_while = Expr::While {
        header: Box::new(Block {
            stmts: vec![Stmt::Let {
                pattern: vec![Some(cv.clone())],
                value: Expr::Const(crate::ir::Const::Bool(false)),
            }],
            tail: BlockTail::Value(Expr::Unit),
        }),
        cond: Box::new(Expr::Var(cv.clone())),
        body: Box::new(Block {
            stmts: vec![Stmt::Let {
                pattern: vec![Some(c1.clone())],
                value: inner_while,
            }],
            tail: BlockTail::Value(Expr::Tuple(vec![
                Expr::Var(c1.clone()),
                Expr::Var(b.clone()),
            ])),
        }),
        iter_locals: vec![(a.clone(), lit_u64(0)), (b.clone(), lit_u64(1))],
        header_exit_locals: vec![a.clone(), b.clone()],
        live_out: vec![],
    };
    let body = Block {
        stmts: vec![Stmt::Let {
            pattern: vec![Some(a2.clone()), Some(b2.clone())],
            value: Expr::If {
                cond: Box::new(Expr::Const(crate::ir::Const::Bool(true))),
                then_branch: Box::new(Block {
                    stmts: vec![],
                    tail: BlockTail::Value(Expr::Tuple(vec![lit_u64(0), lit_u64(1)])),
                }),
                else_branch: Box::new(Block {
                    stmts: vec![Stmt::Let {
                        pattern: vec![Some(a1.clone()), Some(b1.clone())],
                        value: outer_while,
                    }],
                    tail: BlockTail::Value(Expr::Tuple(vec![
                        Expr::Var(a1.clone()),
                        Expr::Var(b1.clone()),
                    ])),
                }),
            },
        }],
        tail: BlockTail::Value(Expr::Var(a2.clone())),
    };
    let _ = b2;
    let mut p = one_fn_program(body);
    let ids = ProverFnIds::default();
    stage_07_dejumps::run(&mut p, &ids).expect("run end-to-end");

    // The whole value-side mutual-recursion family -- outer LoopBody
    // and LoopAfter, inner LoopBody and LoopAfter (the inner's after
    // re-enters the outer) -- must share the If-join's `(u64, u64)`,
    // not the parent function's `u64`.
    let helper = |name: &str| {
        p.functions
            .values()
            .find(|f| f.name == name)
            .unwrap_or_else(|| {
                let names: Vec<_> = p.functions.values().map(|f| f.name.clone()).collect();
                panic!("missing helper {name}; have: {names:?}")
            })
    };
    let pair = Type::Tuple(vec![Type::UInt(64), Type::UInt(64)]);
    for name in [
        "f.while_0",
        "f.while_0.after",
        "f.while_1",
        "f.while_1.after",
    ] {
        assert_eq!(
            helper(name).signature.return_type,
            pair,
            "{name} must carry the loop family's pair type"
        );
    }
}
