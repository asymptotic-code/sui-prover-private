//! Additional coverage tests, addressing gaps surfaced in code review.

use crate::ir::{BinOp, Block, BlockTail, Expr, Stmt, Struct, Type};
use crate::stage_05_ssa::postcondition::{check, PostconditionError};
use crate::stage_05_ssa::run;

use super::fixtures::*;

// ----------------------------------------------------------------------------
// Phi-nested-in-phi (Stmt::Eval(If) inside another If's arm at stmt level)
// ----------------------------------------------------------------------------

#[test]
fn nested_phi_inside_outer_arm() {
    // let x = 0;
    // if c {
    //     if d { let x = 1 } else { let x = 2 }     <- inner phi
    // };
    // use x
    let inner_then = Block {
        stmts: vec![Stmt::Let {
            pattern: vec![Some("x".into())],
            value: lit_u64(1),
        }],
        tail: BlockTail::Value(Expr::Unit),
    };
    let inner_else = Block {
        stmts: vec![Stmt::Let {
            pattern: vec![Some("x".into())],
            value: lit_u64(2),
        }],
        tail: BlockTail::Value(Expr::Unit),
    };
    let outer_then = Block {
        stmts: vec![Stmt::Eval(Expr::If {
            cond: Box::new(Expr::Var("d".into())),
            then_branch: Box::new(inner_then),
            else_branch: Box::new(inner_else),
        })],
        tail: BlockTail::Value(Expr::Unit),
    };
    let outer_else = Block {
        stmts: vec![],
        tail: BlockTail::Value(Expr::Unit),
    };
    let stmts = vec![
        Stmt::Let {
            pattern: vec![Some("x".into())],
            value: lit_u64(0),
        },
        Stmt::Eval(Expr::If {
            cond: Box::new(Expr::Var("c".into())),
            then_branch: Box::new(outer_then),
            else_branch: Box::new(outer_else),
        }),
    ];
    let mut p = one_fn_program(
        stmts,
        Expr::Var("x".into()),
        vec![param("c", Type::Bool), param("d", Type::Bool)],
        Type::UInt(64),
    );
    run(&mut p).expect("nested phi should succeed");
    check(&p).expect("postcondition should pass");

    let body = body_of(&p);
    // Outer Stmt::Eval(If) should have become Stmt::Let{pattern:[x_<outer>], value: If}
    // since both inner branches define x (or half-phi via outer).
    match &body.stmts[1] {
        Stmt::Let { pattern, value } => {
            assert_eq!(pattern.len(), 1, "outer phi has 1 var");
            assert!(matches!(value, Expr::If { .. }));
            // The body tail uses the outer phi name.
            let outer_phi = pattern[0].as_ref().unwrap();
            assert_eq!(body.tail, BlockTail::Value(Expr::Var(outer_phi.clone())));
        }
        other => panic!("expected outer Stmt::Let, got {:?}", other),
    }
}

// ----------------------------------------------------------------------------
// Match inside a loop body (the cross-product of phi & loop_state)
// ----------------------------------------------------------------------------

#[test]
fn match_inside_loop_body_with_phi() {
    // let i = 0;
    // while (i < n) {
    //     match s { V0 => { let i = i + 1 } | V1 => { let i = i + 2 } }
    // };
    // use i
    let mut p = crate::ir::Program::default();
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
                    fields: vec![],
                },
                crate::ir::Variant {
                    name: "V1".into(),
                    tag: 1,
                    fields: vec![],
                },
            ]),
            is_native: false,
        },
    );

    let arm0 = crate::ir::MatchArm {
        variant: 0,
        bindings: vec![],
        body: Box::new(Block {
            stmts: vec![Stmt::Let {
                pattern: vec![Some("i".into())],
                value: Expr::BinOp {
                    op: BinOp::Add,
                    lhs: Box::new(Expr::Var("i".into())),
                    rhs: Box::new(lit_u64(1)),
                },
            }],
            tail: BlockTail::Value(Expr::Unit),
        }),
    };
    let arm1 = crate::ir::MatchArm {
        variant: 1,
        bindings: vec![],
        body: Box::new(Block {
            stmts: vec![Stmt::Let {
                pattern: vec![Some("i".into())],
                value: Expr::BinOp {
                    op: BinOp::Add,
                    lhs: Box::new(Expr::Var("i".into())),
                    rhs: Box::new(lit_u64(2)),
                },
            }],
            tail: BlockTail::Value(Expr::Unit),
        }),
    };

    let while_body = Block {
        stmts: vec![Stmt::Eval(Expr::Match {
            struct_id: 9,
            selector: Box::new(Expr::Var("s".into())),
            cases: vec![arm0, arm1],
        })],
        tail: BlockTail::Continue {
            level: 0,
            value: Box::new(Expr::Unit),
        },
    };

    let stmts = vec![
        Stmt::Let {
            pattern: vec![Some("i".into())],
            value: lit_u64(0),
        },
        Stmt::Eval(Expr::While {
            header: Box::new(Block {
                stmts: vec![],
                tail: BlockTail::Value(Expr::Unit),
            }),
            cond: Box::new(Expr::BinOp {
                op: BinOp::Lt,
                lhs: Box::new(Expr::Var("i".into())),
                rhs: Box::new(Expr::Var("n".into())),
            }),
            body: Box::new(while_body),
            iter_locals: Vec::new(),
            header_exit_locals: Vec::new(),
            live_out: vec![],
        }),
    ];
    let f = func(
        "f",
        sig(
            vec![
                crate::ir::Param {
                    name: "s".into(),
                    var: "s".into(),
                    ty: Type::Struct {
                        struct_id: 9,
                        type_args: vec![],
                    },
                },
                crate::ir::Param {
                    name: "n".into(),
                    var: "n".into(),
                    ty: Type::UInt(64),
                },
            ],
            Type::UInt(64),
        ),
        body(stmts, Expr::Var("i".into())),
        FuncOpts::default(),
    );
    p.functions.insert(0, f);

    run(&mut p).expect("match inside loop should succeed");
    check(&p).expect("postcondition should pass");
}

// ----------------------------------------------------------------------------
// Multi-binding Stmt::Let pattern + phi (the pattern_arity > 1 path)
// ----------------------------------------------------------------------------

#[test]
fn multi_binding_let_pattern_plus_phi() {
    // let (z0, z1) = if c {
    //     let x = 1;
    //     (x, x)        <- arm tail is Tuple([Var(x), Var(x)])
    // } else {
    //     let x = 2;
    //     (x, x)
    // };
    // use (z0, z1, x)
    // Pattern arity = 2; phi over x = 1 phi var; expected combined pattern arity = 3.
    let then_body = Block {
        stmts: vec![Stmt::Let {
            pattern: vec![Some("x".into())],
            value: lit_u64(1),
        }],
        tail: BlockTail::Value(Expr::Tuple(vec![
            Expr::Var("x".into()),
            Expr::Var("x".into()),
        ])),
    };
    let else_body = Block {
        stmts: vec![Stmt::Let {
            pattern: vec![Some("x".into())],
            value: lit_u64(2),
        }],
        tail: BlockTail::Value(Expr::Tuple(vec![
            Expr::Var("x".into()),
            Expr::Var("x".into()),
        ])),
    };
    let stmts = vec![Stmt::Let {
        pattern: vec![Some("z0".into()), Some("z1".into())],
        value: Expr::If {
            cond: Box::new(Expr::Var("c".into())),
            then_branch: Box::new(then_body),
            else_branch: Box::new(else_body),
        },
    }];
    let mut p = one_fn_program(
        stmts,
        Expr::Tuple(vec![
            Expr::Var("z0".into()),
            Expr::Var("z1".into()),
            Expr::Var("x".into()),
        ]),
        vec![param("c", Type::Bool), param("x", Type::UInt(64))],
        Type::Tuple(vec![Type::UInt(64), Type::UInt(64), Type::UInt(64)]),
    );
    run(&mut p).expect("multi-binding let + phi should succeed");
    check(&p).expect("postcondition should pass");

    let body = body_of(&p);
    // The Let pattern should be [z0_0, z1_0, x_<phi>] (3 slots).
    match &body.stmts[0] {
        Stmt::Let { pattern, value } => {
            assert_eq!(pattern.len(), 3, "pattern is 2 original + 1 phi");
            if let Expr::If { then_branch, .. } = value {
                // Then arm tail must be a Tuple of 3 elements (orig 2 + phi 1).
                if let BlockTail::Value(Expr::Tuple(elems)) = &then_branch.tail {
                    assert_eq!(elems.len(), 3, "arm tail has 3 elements after phi");
                } else {
                    panic!("expected Tuple tail, got {:?}", then_branch.tail);
                }
            }
        }
        _ => panic!(),
    }
}

// ----------------------------------------------------------------------------
// Postcondition negative tests: arity mismatch hand-built
// ----------------------------------------------------------------------------

#[test]
fn postcondition_accepts_body_tail_if_with_explicit_continues() {
    let then_body = Block {
        stmts: vec![],
        tail: BlockTail::Continue {
            level: 0,
            value: Box::new(Expr::Tuple(vec![
                Expr::Var("a_0".into()),
                Expr::Var("b_0".into()),
            ])),
        },
    };
    let else_body = Block {
        stmts: vec![],
        tail: BlockTail::Continue {
            level: 0,
            value: Box::new(Expr::Tuple(vec![
                Expr::Var("a_0".into()),
                Expr::Var("b_0".into()),
            ])),
        },
    };
    let body = Block {
        stmts: vec![],
        tail: BlockTail::Value(Expr::If {
            cond: Box::new(Expr::Var("c_0".into())),
            then_branch: Box::new(then_body),
            else_branch: Box::new(else_body),
        }),
    };
    let while_e = Expr::While {
        header: Box::new(Block {
            stmts: vec![],
            tail: BlockTail::Value(Expr::Unit),
        }),
        cond: Box::new(Expr::Var("c_0".into())),
        body: Box::new(body),
        iter_locals: vec![
            ("a_0".into(), Expr::Var("a_init".into())),
            ("b_0".into(), Expr::Var("b_init".into())),
        ],
        header_exit_locals: vec!["a_0".into(), "b_0".into()],
        live_out: vec![],
    };
    let stmts = vec![
        Stmt::Let {
            pattern: vec![Some("a_init".into())],
            value: lit_u64(0),
        },
        Stmt::Let {
            pattern: vec![Some("b_init".into())],
            value: lit_u64(0),
        },
        Stmt::Eval(while_e),
    ];
    let p = one_fn_program(
        stmts,
        Expr::Unit,
        vec![param("c_0", Type::Bool)],
        Type::Unit,
    );

    check(&p).expect("tail if whose arms continue should not be treated as a scalar body tail");
}

#[test]
fn run_accepts_loop_body_tail_if_with_explicit_continues() {
    let then_body = Block {
        stmts: vec![Stmt::Let {
            pattern: vec![Some("a".into())],
            value: Expr::BinOp {
                op: BinOp::Add,
                lhs: Box::new(Expr::Var("a".into())),
                rhs: Box::new(lit_u64(1)),
            },
        }],
        tail: BlockTail::Continue {
            level: 0,
            value: Box::new(Expr::Unit),
        },
    };
    let else_body = Block {
        stmts: vec![Stmt::Let {
            pattern: vec![Some("b".into())],
            value: Expr::BinOp {
                op: BinOp::Add,
                lhs: Box::new(Expr::Var("b".into())),
                rhs: Box::new(lit_u64(1)),
            },
        }],
        tail: BlockTail::Continue {
            level: 0,
            value: Box::new(Expr::Unit),
        },
    };
    let while_body = Block {
        stmts: vec![],
        tail: BlockTail::Value(Expr::If {
            cond: Box::new(Expr::Var("c".into())),
            then_branch: Box::new(then_body),
            else_branch: Box::new(else_body),
        }),
    };
    let stmts = vec![
        Stmt::Let {
            pattern: vec![Some("a".into())],
            value: lit_u64(0),
        },
        Stmt::Let {
            pattern: vec![Some("b".into())],
            value: lit_u64(0),
        },
        Stmt::Eval(Expr::While {
            header: Box::new(Block {
                stmts: vec![],
                tail: BlockTail::Value(Expr::Unit),
            }),
            cond: Box::new(Expr::Var("c".into())),
            body: Box::new(while_body),
            iter_locals: Vec::new(),
            header_exit_locals: Vec::new(),
            live_out: vec![],
        }),
    ];
    let mut p = one_fn_program(
        stmts,
        Expr::Tuple(vec![Expr::Var("a".into()), Expr::Var("b".into())]),
        vec![param("c", Type::Bool)],
        Type::Tuple(vec![Type::UInt(64), Type::UInt(64)]),
    );

    run(&mut p).expect("stage 5 should handle tail if with explicit continues");
    check(&p).expect("stage 5 postcondition should accept rewritten tail if");
}

#[test]
fn postcondition_rejects_break_arity_mismatch() {
    // Hand-built: While with iter_locals.len()=2 but Break carries
    // a single Var (arity 1).
    let body = Block {
        stmts: vec![],
        tail: BlockTail::Break {
            level: 0,
            value: Box::new(Expr::Var("a_0".into())),
        },
    };
    let while_e = Expr::While {
        header: Box::new(Block {
            stmts: vec![],
            tail: BlockTail::Value(Expr::Unit),
        }),
        cond: Box::new(Expr::Var("c_0".into())),
        body: Box::new(body),
        iter_locals: vec![
            ("a_0".into(), Expr::Var("a_init".into())),
            ("b_0".into(), Expr::Var("b_init".into())),
        ],
        header_exit_locals: vec!["a_0".into(), "b_0".into()],
        live_out: vec![],
    };
    let stmts = vec![
        Stmt::Let {
            pattern: vec![Some("a_init".into())],
            value: lit_u64(0),
        },
        Stmt::Let {
            pattern: vec![Some("b_init".into())],
            value: lit_u64(0),
        },
        Stmt::Eval(while_e),
    ];
    let p = one_fn_program(
        stmts,
        Expr::Unit,
        vec![param("c_0", Type::Bool)],
        Type::Unit,
    );
    let err = check(&p).unwrap_err();
    assert!(
        matches!(
            err,
            PostconditionError::JumpArityMismatch {
                level: 0,
                expected: 2,
                actual: 1,
                ..
            }
        ),
        "expected JumpArityMismatch 2 vs 1, got {:?}",
        err
    );
}

#[test]
fn postcondition_rejects_body_tail_arity_mismatch() {
    // Hand-built: While with iter_locals.len()=2 but body's tail
    // Value carries a single Var (arity 1).
    let body = Block {
        stmts: vec![],
        tail: BlockTail::Value(Expr::Var("a_0".into())),
    };
    let while_e = Expr::While {
        header: Box::new(Block {
            stmts: vec![],
            tail: BlockTail::Value(Expr::Unit),
        }),
        cond: Box::new(Expr::Var("c_0".into())),
        body: Box::new(body),
        iter_locals: vec![
            ("a_0".into(), Expr::Var("a_init".into())),
            ("b_0".into(), Expr::Var("b_init".into())),
        ],
        header_exit_locals: vec!["a_0".into(), "b_0".into()],
        live_out: vec![],
    };
    let stmts = vec![
        Stmt::Let {
            pattern: vec![Some("a_init".into())],
            value: lit_u64(0),
        },
        Stmt::Let {
            pattern: vec![Some("b_init".into())],
            value: lit_u64(0),
        },
        Stmt::Eval(while_e),
    ];
    let p = one_fn_program(
        stmts,
        Expr::Unit,
        vec![param("c_0", Type::Bool)],
        Type::Unit,
    );
    let err = check(&p).unwrap_err();
    assert!(
        matches!(
            err,
            PostconditionError::BodyTailArityMismatch {
                expected: 2,
                actual: 1,
                ..
            }
        ),
        "expected BodyTailArityMismatch 2 vs 1, got {:?}",
        err
    );
}
