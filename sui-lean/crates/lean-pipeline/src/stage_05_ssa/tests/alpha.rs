//! Phase 1 alpha-rename tests.
//!
//! Covers:
//! - basic `let` rebind alpha-renaming
//! - multi-base independence
//! - function parameter binding
//! - stage-3 (mut-to-let) shadowing shape: `let r = WriteRef(Var(r), v)`
//! - WriteBack with `LocalRoot(x)` shadowing the LocalRoot var
//! - wildcard (`None`) pattern positions preserved
//! - native functions left untouched
//! - `Match` arm bindings + `Quantifier::binder` freshness and scope isolation
//! - `BorrowLoc` / `BorrowField` references renamed
//! - unbound `Var` rejects with `UnboundReference`

use crate::ir::{
    BinOp, BlockTail, BorrowEdge, BorrowNode, Expr, MatchArm, Param, QuantDomain, QuantifierKind,
    Stmt, Struct, Type, VarId,
};
use crate::stage_05_ssa::{run, Stage5Error};

use super::fixtures::*;

#[test]
fn single_rebind_alpha_renames() {
    // let x = 1; let x = 2; use x
    let stmts = vec![
        Stmt::Let {
            pattern: vec![Some(VarId::from("x"))],
            value: lit_u64(1),
        },
        Stmt::Let {
            pattern: vec![Some(VarId::from("x"))],
            value: lit_u64(2),
        },
    ];
    let mut program = one_fn_program(stmts, Expr::Var(VarId::from("x")), vec![], Type::UInt(64));
    run(&mut program).unwrap();

    let body = body_of(&program);
    assert_eq!(body.stmts.len(), 2);
    match &body.stmts[0] {
        Stmt::Let { pattern, .. } => assert_eq!(pattern, &vec![Some(VarId::from("x_0"))]),
        _ => panic!(),
    }
    match &body.stmts[1] {
        Stmt::Let { pattern, .. } => assert_eq!(pattern, &vec![Some(VarId::from("x_1"))]),
        _ => panic!(),
    }
    assert_eq!(body.tail, BlockTail::Value(Expr::Var(VarId::from("x_1"))));
}

#[test]
fn multi_base_independent_counters() {
    // let x = 1; let y = 2; let x = 3; use (x, y)
    let stmts = vec![
        Stmt::Let {
            pattern: vec![Some("x".into())],
            value: lit_u64(1),
        },
        Stmt::Let {
            pattern: vec![Some("y".into())],
            value: lit_u64(2),
        },
        Stmt::Let {
            pattern: vec![Some("x".into())],
            value: lit_u64(3),
        },
    ];
    let mut program = one_fn_program(
        stmts,
        Expr::Tuple(vec![Expr::Var("x".into()), Expr::Var("y".into())]),
        vec![],
        Type::Tuple(vec![Type::UInt(64), Type::UInt(64)]),
    );
    run(&mut program).unwrap();

    let body = body_of(&program);
    assert_eq!(body.stmts.len(), 3);
    match &body.stmts[0] {
        Stmt::Let { pattern, .. } => assert_eq!(pattern, &vec![Some("x_0".into())]),
        _ => panic!(),
    }
    match &body.stmts[1] {
        Stmt::Let { pattern, .. } => assert_eq!(pattern, &vec![Some("y_0".into())]),
        _ => panic!(),
    }
    match &body.stmts[2] {
        Stmt::Let { pattern, .. } => assert_eq!(pattern, &vec![Some("x_1".into())]),
        _ => panic!(),
    }
    assert_eq!(
        body.tail,
        BlockTail::Value(Expr::Tuple(vec![
            Expr::Var("x_1".into()),
            Expr::Var("y_0".into())
        ]))
    );
}

#[test]
fn function_params_renamed_and_referenced() {
    // fn f(x: u64): u64 { x + 1 }
    let stmts = vec![];
    let tail = Expr::BinOp {
        op: BinOp::Add,
        lhs: Box::new(Expr::Var("x".into())),
        rhs: Box::new(lit_u64(1)),
    };
    let mut program = one_fn_program(
        stmts,
        tail,
        vec![param("x", Type::UInt(64))],
        Type::UInt(64),
    );
    run(&mut program).unwrap();

    let f = &program.functions[&0];
    assert_eq!(f.signature.params.len(), 1);
    assert_eq!(f.signature.params[0].var, "x_0".into());
    // Body's Var(x) resolves to x_0.
    if let BlockTail::Value(Expr::BinOp { lhs, .. }) = &f.body.tail {
        assert_eq!(**lhs, Expr::Var("x_0".into()));
    } else {
        panic!();
    }
}

#[test]
fn write_ref_shadowing_renames_to_fresh() {
    // Stage-3 (mut-to-let) output shape:
    //   let r = BorrowLoc(x)
    //   let r = WriteRef(Var(r), 5)
    // Alpha-rename should produce:
    //   let r_0 = BorrowLoc(x_0)
    //   let r_1 = WriteRef(Var(r_0), 5)
    let stmts = vec![
        Stmt::Let {
            pattern: vec![Some("r".into())],
            value: Expr::BorrowLoc("x".into()),
        },
        Stmt::Let {
            pattern: vec![Some("r".into())],
            value: Expr::WriteRef {
                reference: Box::new(Expr::Var("r".into())),
                value: Box::new(lit_u64(5)),
            },
        },
    ];
    let mut program = one_fn_program(
        stmts,
        Expr::Unit,
        vec![param("x", Type::UInt(64))],
        Type::Unit,
    );
    run(&mut program).unwrap();

    let body = body_of(&program);
    assert_eq!(body.stmts.len(), 2);
    // Stmt 0: let r_0 = BorrowLoc(x_0)
    match &body.stmts[0] {
        Stmt::Let { pattern, value } => {
            assert_eq!(pattern, &vec![Some("r_0".into())]);
            assert_eq!(value, &Expr::BorrowLoc("x_0".into()));
        }
        _ => panic!(),
    }
    // Stmt 1: let r_1 = WriteRef(Var(r_0), 5)
    match &body.stmts[1] {
        Stmt::Let { pattern, value } => {
            assert_eq!(pattern, &vec![Some("r_1".into())]);
            match value {
                Expr::WriteRef {
                    reference,
                    value: v,
                } => {
                    assert_eq!(**reference, Expr::Var("r_0".into()));
                    assert_eq!(**v, lit_u64(5));
                }
                _ => panic!(),
            }
        }
        _ => panic!(),
    }
}

#[test]
fn write_back_localroot_shadowing_renames_to_fresh() {
    // Stage-3 (mut-to-let) WriteBack shape:
    //   let x = WriteBack(LocalRoot(x), Direct, child)
    // Alpha-rename should produce:
    //   let x_1 = WriteBack(LocalRoot(x_0), Direct, child_0)
    // (assuming x is a function param and child is bound earlier.)
    let stmts = vec![
        Stmt::Let {
            pattern: vec![Some("child".into())],
            value: Expr::BorrowLoc("x".into()),
        },
        Stmt::Let {
            pattern: vec![Some("x".into())],
            value: Expr::WriteBack {
                node: BorrowNode::LocalRoot("x".into()),
                edge: BorrowEdge::Direct,
                child: "child".into(),
                world: None,
            },
        },
    ];
    let mut program = one_fn_program(
        stmts,
        Expr::Unit,
        vec![param("x", Type::UInt(64))],
        Type::Unit,
    );
    run(&mut program).unwrap();

    let body = body_of(&program);
    // Stmt 0: let child_0 = BorrowLoc(x_0)
    match &body.stmts[0] {
        Stmt::Let { pattern, value } => {
            assert_eq!(pattern, &vec![Some("child_0".into())]);
            assert_eq!(value, &Expr::BorrowLoc("x_0".into()));
        }
        _ => panic!(),
    }
    // Stmt 1: let x_1 = WriteBack(LocalRoot(x_0), Direct, child_0)
    match &body.stmts[1] {
        Stmt::Let { pattern, value } => {
            assert_eq!(pattern, &vec![Some("x_1".into())]);
            match value {
                Expr::WriteBack {
                    node, edge, child, ..
                } => {
                    assert_eq!(*node, BorrowNode::LocalRoot("x_0".into()));
                    assert_eq!(*edge, BorrowEdge::Direct);
                    assert_eq!(*child, VarId::from("child_0"));
                }
                _ => panic!(),
            }
        }
        _ => panic!(),
    }
}

#[test]
fn wildcard_pattern_positions_preserved() {
    // let (a, _) = (1, 2); use a
    let stmts = vec![Stmt::Let {
        pattern: vec![Some("a".into()), None],
        value: Expr::Tuple(vec![lit_u64(1), lit_u64(2)]),
    }];
    let mut program = one_fn_program(stmts, Expr::Var("a".into()), vec![], Type::UInt(64));
    run(&mut program).unwrap();

    let body = body_of(&program);
    match &body.stmts[0] {
        Stmt::Let { pattern, .. } => {
            assert_eq!(pattern.len(), 2);
            assert_eq!(pattern[0], Some(VarId::from("a_0")));
            assert!(pattern[1].is_none(), "wildcard preserved");
        }
        _ => panic!(),
    }
    assert_eq!(body.tail, BlockTail::Value(Expr::Var("a_0".into())));
}

#[test]
fn native_function_left_untouched() {
    // Obsolete: natives now live in program.natives.decls, not
    // program.functions; stages walk only functions, so this
    // behavior is structurally guaranteed.
}

#[test]
fn match_arm_bindings_fresh_and_scoped() {
    // match s with V0(a) => a | V1(b) => b
    // Outer scope has no `a` or `b`; each arm gets a fresh binding,
    // scoped to its body.
    let mut p = Program::default();
    p.modules.insert(0, module());
    p.structs.insert(
        9,
        Struct {
            module_id: 0,
            name: "E".into(),
            qualified_name: "p::m::E".into(),
            type_params: Vec::new(),
            fields: Vec::new(),
            variants: Some(vec![
                crate::ir::Variant {
                    name: "V0".into(),
                    tag: 0,
                    fields: vec![crate::ir::Field {
                        name: "a".into(),
                        field_type: Type::UInt(64),
                    }],
                },
                crate::ir::Variant {
                    name: "V1".into(),
                    tag: 1,
                    fields: vec![crate::ir::Field {
                        name: "b".into(),
                        field_type: Type::UInt(64),
                    }],
                },
            ]),
            is_native: false,
        },
    );

    let selector = Expr::Var("s".into());
    let arm0 = MatchArm {
        variant: 0,
        bindings: vec!["a".into()],
        body: Box::new(body(vec![], Expr::Var("a".into()))),
    };
    let arm1 = MatchArm {
        variant: 1,
        bindings: vec!["b".into()],
        body: Box::new(body(vec![], Expr::Var("b".into()))),
    };
    let tail = Expr::Match {
        struct_id: 9,
        selector: Box::new(selector),
        cases: vec![arm0, arm1],
    };

    let s_param = Param {
        name: "s".into(),
        var: "s".into(),
        ty: Type::Struct {
            struct_id: 9,
            type_args: vec![],
        },
    };
    let f = func(
        "f",
        sig(vec![s_param], Type::UInt(64)),
        body(vec![], tail),
        FuncOpts::default(),
    );
    p.functions.insert(0, f);

    run(&mut p).unwrap();

    let f = &p.functions[&0];
    if let BlockTail::Value(Expr::Match { cases, .. }) = &f.body.tail {
        // V0 arm: binding "a" → fresh "a_0"; body tail uses Var("a_0").
        assert_eq!(cases[0].bindings, vec![VarId::from("a_0")]);
        assert_eq!(
            cases[0].body.tail,
            BlockTail::Value(Expr::Var("a_0".into()))
        );
        // V1 arm: binding "b" → fresh "b_0"; body tail uses Var("b_0").
        assert_eq!(cases[1].bindings, vec![VarId::from("b_0")]);
        assert_eq!(
            cases[1].body.tail,
            BlockTail::Value(Expr::Var("b_0".into()))
        );
    } else {
        panic!("expected Match");
    }
}

#[test]
fn quantifier_binder_fresh_and_scoped_to_body() {
    // Outer has a let x = 5; then a forall quantifier with binder x;
    // the binder gets a fresh name; outer x_0 unaffected.
    let stmts = vec![
        Stmt::Let {
            pattern: vec![Some("x".into())],
            value: lit_u64(5),
        },
        Stmt::Eval(Expr::Quantifier {
            kind: QuantifierKind::Forall,
            binder: "x".into(),
            binder_type: Type::UInt(64),
            domain: QuantDomain::Unbounded,
            body: Box::new(body(
                vec![],
                Expr::BinOp {
                    op: BinOp::Gt,
                    lhs: Box::new(Expr::Var("x".into())),
                    rhs: Box::new(lit_u64(0)),
                },
            )),
        }),
    ];
    let mut program = one_fn_program(stmts, Expr::Var("x".into()), vec![], Type::UInt(64));
    run(&mut program).unwrap();

    let body = body_of(&program);
    // Outer let: x_0
    match &body.stmts[0] {
        Stmt::Let { pattern, .. } => assert_eq!(pattern, &vec![Some(VarId::from("x_0"))]),
        _ => panic!(),
    }
    // Quantifier binder: fresh (counter advanced => x_1).
    match &body.stmts[1] {
        Stmt::Eval(Expr::Quantifier { binder, body, .. }) => {
            assert_eq!(*binder, VarId::from("x_1"));
            // Body references Var(x) → resolves to the quantifier's
            // x_1 (the body's scope clone).
            if let BlockTail::Value(Expr::BinOp { lhs, .. }) = &body.tail {
                assert_eq!(**lhs, Expr::Var("x_1".into()));
            } else {
                panic!();
            }
        }
        _ => panic!(),
    }
    // Outer tail Var(x) resolves to the outer x_0.
    assert_eq!(body.tail, BlockTail::Value(Expr::Var("x_0".into())));
}

#[test]
fn borrow_field_base_renames_through() {
    let stmts = vec![
        Stmt::Let {
            pattern: vec![Some("r0".into())],
            value: Expr::BorrowLoc("x".into()),
        },
        Stmt::Let {
            pattern: vec![Some("r1".into())],
            value: Expr::Borrow {
                step: crate::ir::path::PathStep::Field {
                    struct_id: 7,
                    field_index: 0,
                },
                base: Box::new(Expr::Var("r0".into())),
            },
        },
    ];
    let mut p = one_fn_program(
        stmts,
        Expr::Unit,
        vec![param("x", Type::UInt(64))],
        Type::Unit,
    );
    p.structs.insert(
        7,
        Struct {
            module_id: 0,
            name: "S".into(),
            qualified_name: "p::m::S".into(),
            type_params: Vec::new(),
            fields: vec![crate::ir::Field {
                name: "f0".into(),
                field_type: Type::UInt(64),
            }],
            variants: None,
            is_native: false,
        },
    );
    run(&mut p).unwrap();

    let body = body_of(&p);
    match &body.stmts[1] {
        Stmt::Let {
            value: Expr::Borrow { base, .. },
            ..
        } => {
            assert_eq!(**base, Expr::Var("r0_0".into()));
        }
        _ => panic!(),
    }
}

#[test]
fn unbound_var_rejects() {
    // Body references `y` with no binding.
    let stmts = vec![];
    let tail = Expr::Var("y".into());
    let mut program = one_fn_program(stmts, tail, vec![], Type::UInt(64));
    let err = run(&mut program).unwrap_err();
    assert_eq!(
        err,
        Stage5Error::UnboundReference {
            function: 0,
            var: "y".into(),
        }
    );
}

#[test]
fn no_op_on_empty_body() {
    let stmts = vec![];
    let mut program = one_fn_program(stmts, Expr::Unit, vec![], Type::Unit);
    let before = program.clone();
    run(&mut program).unwrap();
    assert_eq!(program, before);
}

#[test]
fn deterministic_byte_identical_output() {
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
    let mut p1 = one_fn_program(stmts.clone(), Expr::Var("x".into()), vec![], Type::UInt(64));
    let mut p2 = one_fn_program(stmts, Expr::Var("x".into()), vec![], Type::UInt(64));
    run(&mut p1).unwrap();
    run(&mut p2).unwrap();
    assert_eq!(p1, p2);
}

// Bring `Program` into scope for the `match_arm_bindings_fresh_and_scoped` test.
use crate::ir::Program;
