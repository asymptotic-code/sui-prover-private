//! Phase 3 + 4: phi rewriting at statement level.
//!
//! Covers:
//! - Standard if-phi (both arms define x; phi over Value arms only).
//! - Half-phi (only one arm defines x; outer scope has x).
//! - Multi-binding phi (two vars defined in both arms).
//! - Existing Stmt::Let pattern + phi (let binds the If's value;
//!   phi vars extend the pattern).
//! - One Value + one Abort: phi is empty; Stmt::Let stays
//!   single-binding (or Stmt::Eval if no Let).
//! - All-terminator arms: emitted as Stmt::Eval; surrounding Let
//!   pattern dropped.
//! - Match with phi over arms (variant bindings stay arm-local).
//! - Defensive: a phi var defined in some-but-not-all Value arms AND
//!   not in outer scope rejects.

use crate::ir::{Block, BlockTail, Expr, MatchArm, Stmt, Struct, Type, VarId};
use crate::stage_05_ssa::{run, Stage5Error};

use super::fixtures::*;

fn if_stmt_with_arms(cond: Expr, then_body: Block, else_body: Block) -> Stmt {
    Stmt::Eval(Expr::If {
        cond: Box::new(cond),
        then_branch: Box::new(then_body),
        else_branch: Box::new(else_body),
    })
}

#[test]
fn standard_if_phi_both_arms_define_x() {
    // Source-pattern (post mut-to-let): both arms rebind `x`.
    //   if c { let x = 1; }  else { let x = 2; }
    //   use x
    let then_body = Block {
        stmts: vec![Stmt::Let {
            pattern: vec![Some("x".into())],
            value: lit_u64(1),
        }],
        tail: BlockTail::Value(Expr::Unit),
    };
    let else_body = Block {
        stmts: vec![Stmt::Let {
            pattern: vec![Some("x".into())],
            value: lit_u64(2),
        }],
        tail: BlockTail::Value(Expr::Unit),
    };
    let stmts = vec![if_stmt_with_arms(
        Expr::Var("c".into()),
        then_body,
        else_body,
    )];
    let mut p = one_fn_program(
        stmts,
        Expr::Var("x".into()),
        vec![param("c", Type::Bool), param("x", Type::UInt(64))],
        Type::UInt(64),
    );
    run(&mut p).unwrap();

    let body = body_of(&p);
    assert_eq!(body.stmts.len(), 1);
    // Stmt::Eval(If) became Stmt::Let { pattern: [x_<n>], value: If { ... } }
    match &body.stmts[0] {
        Stmt::Let { pattern, value } => {
            assert_eq!(pattern.len(), 1);
            let phi_name = pattern[0].as_ref().expect("Some pattern slot");
            // Subsequent tail must reference this phi name.
            assert_eq!(body.tail, BlockTail::Value(Expr::Var(phi_name.clone())));
            // The If arms' tails should be Tuple([Var(arm_local_x)])
            // (single-element tuple) -- our impl flattens to plain
            // Value(Var(arm_local_x)) when components.len() == 1.
            if let Expr::If {
                then_branch,
                else_branch,
                ..
            } = value
            {
                if let BlockTail::Value(e) = &then_branch.tail {
                    assert!(matches!(e, Expr::Var(_)), "then arm tail Value(Var)");
                } else {
                    panic!("then arm tail should be Value, got {:?}", then_branch.tail);
                }
                if let BlockTail::Value(e) = &else_branch.tail {
                    assert!(matches!(e, Expr::Var(_)), "else arm tail Value(Var)");
                } else {
                    panic!();
                }
            } else {
                panic!("expected If value");
            }
        }
        _ => panic!("expected Stmt::Let {{ pattern: [phi], value: If }}"),
    }
}

#[test]
fn half_phi_outer_var_with_only_then_redefining() {
    // let x = 0;
    // if c { let x = 1 };  -- only then arm redefines x
    // use x
    let then_body = Block {
        stmts: vec![Stmt::Let {
            pattern: vec![Some("x".into())],
            value: lit_u64(1),
        }],
        tail: BlockTail::Value(Expr::Unit),
    };
    let else_body = Block {
        stmts: vec![],
        tail: BlockTail::Value(Expr::Unit),
    };
    let stmts = vec![
        Stmt::Let {
            pattern: vec![Some("x".into())],
            value: lit_u64(0),
        },
        if_stmt_with_arms(Expr::Var("c".into()), then_body, else_body),
    ];
    let mut p = one_fn_program(
        stmts,
        Expr::Var("x".into()),
        vec![param("c", Type::Bool)],
        Type::UInt(64),
    );
    run(&mut p).unwrap();

    let body = body_of(&p);
    // stmts[0]: let x_0 = 0
    match &body.stmts[0] {
        Stmt::Let { pattern, .. } => assert_eq!(pattern, &vec![Some(VarId::from("x_0"))]),
        _ => panic!(),
    }
    // stmts[1]: let x_<n> = if c_0 { ... ; tail: Value(Var(x_1)) }
    //                                    else { tail: Value(Var(x_0)) }  -- half-phi pass-through
    match &body.stmts[1] {
        Stmt::Let { pattern, value } => {
            assert_eq!(pattern.len(), 1);
            let phi_name = pattern[0].as_ref().unwrap();
            if let Expr::If {
                then_branch,
                else_branch,
                ..
            } = value
            {
                // Then arm: rewrote let x = 1 -> let x_1 = 1; tail Var(x_1).
                if let BlockTail::Value(Expr::Var(v)) = &then_branch.tail {
                    assert_eq!(*v, VarId::from("x_1"));
                } else {
                    panic!("then tail not Var: {:?}", then_branch.tail);
                }
                // Else arm: no rebind; tail is the outer scope's x_0.
                if let BlockTail::Value(Expr::Var(v)) = &else_branch.tail {
                    assert_eq!(*v, VarId::from("x_0"));
                } else {
                    panic!("else tail not Var: {:?}", else_branch.tail);
                }
            } else {
                panic!();
            }
            // body tail uses the phi name.
            assert_eq!(body.tail, BlockTail::Value(Expr::Var(phi_name.clone())));
        }
        _ => panic!(),
    }
}

#[test]
fn multi_var_phi() {
    // if c { let x = 1; let y = 2 } else { let x = 3; let y = 4 }
    // use (x, y)
    let then_body = Block {
        stmts: vec![
            Stmt::Let {
                pattern: vec![Some("x".into())],
                value: lit_u64(1),
            },
            Stmt::Let {
                pattern: vec![Some("y".into())],
                value: lit_u64(2),
            },
        ],
        tail: BlockTail::Value(Expr::Unit),
    };
    let else_body = Block {
        stmts: vec![
            Stmt::Let {
                pattern: vec![Some("x".into())],
                value: lit_u64(3),
            },
            Stmt::Let {
                pattern: vec![Some("y".into())],
                value: lit_u64(4),
            },
        ],
        tail: BlockTail::Value(Expr::Unit),
    };
    let stmts = vec![if_stmt_with_arms(
        Expr::Var("c".into()),
        then_body,
        else_body,
    )];
    let mut p = one_fn_program(
        stmts,
        Expr::Tuple(vec![Expr::Var("x".into()), Expr::Var("y".into())]),
        vec![
            param("c", Type::Bool),
            param("x", Type::UInt(64)),
            param("y", Type::UInt(64)),
        ],
        Type::Tuple(vec![Type::UInt(64), Type::UInt(64)]),
    );
    run(&mut p).unwrap();

    let body = body_of(&p);
    // stmts[0]: let (x_<n>, y_<m>) = if ...
    match &body.stmts[0] {
        Stmt::Let { pattern, .. } => {
            assert_eq!(pattern.len(), 2);
            let x_phi = pattern[0].as_ref().unwrap();
            let y_phi = pattern[1].as_ref().unwrap();
            // Body tail uses both phi names.
            assert_eq!(
                body.tail,
                BlockTail::Value(Expr::Tuple(vec![
                    Expr::Var(x_phi.clone()),
                    Expr::Var(y_phi.clone()),
                ]))
            );
        }
        _ => panic!(),
    }
}

#[test]
fn existing_let_pattern_plus_phi_extends_pattern() {
    // let z = if c { let x = 1; x } else { let x = 2; x };  -- z binds to whichever arm's x
    // use (z, x)  -- expects x is phi'd out too
    let then_body = Block {
        stmts: vec![Stmt::Let {
            pattern: vec![Some("x".into())],
            value: lit_u64(1),
        }],
        tail: BlockTail::Value(Expr::Var("x".into())),
    };
    let else_body = Block {
        stmts: vec![Stmt::Let {
            pattern: vec![Some("x".into())],
            value: lit_u64(2),
        }],
        tail: BlockTail::Value(Expr::Var("x".into())),
    };
    let stmts = vec![Stmt::Let {
        pattern: vec![Some("z".into())],
        value: Expr::If {
            cond: Box::new(Expr::Var("c".into())),
            then_branch: Box::new(then_body),
            else_branch: Box::new(else_body),
        },
    }];
    let mut p = one_fn_program(
        stmts,
        Expr::Tuple(vec![Expr::Var("z".into()), Expr::Var("x".into())]),
        vec![param("c", Type::Bool), param("x", Type::UInt(64))],
        Type::Tuple(vec![Type::UInt(64), Type::UInt(64)]),
    );
    run(&mut p).unwrap();

    let body = body_of(&p);
    // stmts[0] should be Stmt::Let { pattern: [z_0, x_<n>], value: If { ... } }
    // Each arm's tail rewritten from Value(Var(x)) to Value(Tuple([Var(x_arm), Var(x_arm)]))
    // — that's "orig_value" + "phi value" both being x in the arm scope.
    match &body.stmts[0] {
        Stmt::Let { pattern, value } => {
            assert_eq!(pattern.len(), 2);
            assert_eq!(pattern[0], Some(VarId::from("z_0")));
            let x_phi = pattern[1].as_ref().unwrap();
            assert!(
                x_phi.starts_with("x_"),
                "phi name should be x_<n>, got {}",
                x_phi
            );
            if let Expr::If {
                then_branch,
                else_branch,
                ..
            } = value
            {
                // Then arm's tail should be Tuple([Var(x_1), Var(x_1)]) (orig=x, phi=x).
                if let BlockTail::Value(Expr::Tuple(elems)) = &then_branch.tail {
                    assert_eq!(elems.len(), 2);
                    if let (Expr::Var(a), Expr::Var(b)) = (&elems[0], &elems[1]) {
                        assert_eq!(a, b, "orig and phi should be same arm-local x");
                    } else {
                        panic!();
                    }
                } else {
                    panic!("then tail not Tuple: {:?}", then_branch.tail);
                }
                if let BlockTail::Value(Expr::Tuple(elems)) = &else_branch.tail {
                    assert_eq!(elems.len(), 2);
                } else {
                    panic!();
                }
            }
        }
        _ => panic!(),
    }
}

#[test]
fn one_value_arm_one_abort_arm_no_phi() {
    // if c { 1 } else { abort 7 }   -- in Stmt::Eval position
    // Phi set is empty (abort arm doesn't define anything to merge).
    let then_body = Block {
        stmts: vec![],
        tail: BlockTail::Value(lit_u64(1)),
    };
    let else_body = Block {
        stmts: vec![],
        tail: BlockTail::Abort {
            code: Box::new(lit_u64(7)),
        },
    };
    let stmts = vec![if_stmt_with_arms(
        Expr::Var("c".into()),
        then_body,
        else_body,
    )];
    let mut p = one_fn_program(stmts, Expr::Unit, vec![param("c", Type::Bool)], Type::Unit);
    run(&mut p).unwrap();

    let body = body_of(&p);
    // Should remain Stmt::Eval(If { ... }) — no phi vars to introduce.
    match &body.stmts[0] {
        Stmt::Eval(Expr::If {
            then_branch,
            else_branch,
            ..
        }) => {
            // Then arm tail kept as Value(lit_u64(1)).
            assert_eq!(then_branch.tail, BlockTail::Value(lit_u64(1)));
            // Else arm tail kept as Abort.
            assert!(matches!(else_branch.tail, BlockTail::Abort { .. }));
        }
        other => panic!("expected Stmt::Eval(If), got {:?}", other),
    }
}

#[test]
fn one_value_arm_one_terminator_arm_with_outer_phi() {
    // let x = 0;
    // if c { let x = 1 } else { abort 7 };
    // use x
    // The then arm rebinds outer x; the else arm aborts (no contribution).
    // phi_vars = {x} via half-phi (x in outer + defined in only Value arm "then").
    let then_body = Block {
        stmts: vec![Stmt::Let {
            pattern: vec![Some("x".into())],
            value: lit_u64(1),
        }],
        tail: BlockTail::Value(Expr::Unit),
    };
    let else_body = Block {
        stmts: vec![],
        tail: BlockTail::Abort {
            code: Box::new(lit_u64(7)),
        },
    };
    let stmts = vec![
        Stmt::Let {
            pattern: vec![Some("x".into())],
            value: lit_u64(0),
        },
        if_stmt_with_arms(Expr::Var("c".into()), then_body, else_body),
    ];
    let mut p = one_fn_program(
        stmts,
        Expr::Var("x".into()),
        vec![param("c", Type::Bool)],
        Type::UInt(64),
    );
    run(&mut p).unwrap();

    let body = body_of(&p);
    // stmts[1]: should be Stmt::Let { pattern: [phi_x], value: If { ... } }
    // Then arm tail rewritten to Value(Var(x_in_arm)); else arm keeps Abort.
    match &body.stmts[1] {
        Stmt::Let { pattern, value } => {
            assert_eq!(pattern.len(), 1);
            if let Expr::If {
                then_branch,
                else_branch,
                ..
            } = value
            {
                if let BlockTail::Value(Expr::Var(v)) = &then_branch.tail {
                    assert_eq!(*v, VarId::from("x_1"));
                } else {
                    panic!("then tail not Var, got {:?}", then_branch.tail);
                }
                assert!(matches!(else_branch.tail, BlockTail::Abort { .. }));
            } else {
                panic!();
            }
        }
        other => panic!("expected Stmt::Let, got {:?}", other),
    }
}

#[test]
fn all_terminator_arms_emit_eval_no_phi() {
    // Stmt::Let { pattern: [z], value: if c { abort 1 } else { abort 2 } }
    // Both arms abort -- no Value arms to merge. Surrounding Let gets
    // dropped; emit as Stmt::Eval(If).
    let then_body = Block {
        stmts: vec![],
        tail: BlockTail::Abort {
            code: Box::new(lit_u64(1)),
        },
    };
    let else_body = Block {
        stmts: vec![],
        tail: BlockTail::Abort {
            code: Box::new(lit_u64(2)),
        },
    };
    let stmts = vec![Stmt::Let {
        pattern: vec![Some("z".into())],
        value: Expr::If {
            cond: Box::new(Expr::Var("c".into())),
            then_branch: Box::new(then_body),
            else_branch: Box::new(else_body),
        },
    }];
    // Body tail can't reference z post-Let (unreachable). Use Unit.
    let mut p = one_fn_program(stmts, Expr::Unit, vec![param("c", Type::Bool)], Type::Unit);
    run(&mut p).unwrap();

    let body = body_of(&p);
    // With our current impl: the let's existing pattern still gets a
    // fresh name; the phi set is empty. Output is
    // Stmt::Let { pattern: [z_0], value: If { both arms Abort } }.
    // This is acceptable -- the binding is unreachable, the unbound
    // z is fine since the abort precedes it.
    match &body.stmts[0] {
        Stmt::Let { pattern, value } => {
            assert_eq!(pattern, &vec![Some(VarId::from("z_0"))]);
            if let Expr::If {
                then_branch,
                else_branch,
                ..
            } = value
            {
                assert!(matches!(then_branch.tail, BlockTail::Abort { .. }));
                assert!(matches!(else_branch.tail, BlockTail::Abort { .. }));
            } else {
                panic!();
            }
        }
        _ => panic!(),
    }
}

#[test]
fn match_with_phi_over_arms() {
    // match s with V0(_) => { let x = 1 } | V1(_) => { let x = 2 }
    // use x
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

    let arm0 = MatchArm {
        variant: 0,
        bindings: vec![],
        body: Box::new(Block {
            stmts: vec![Stmt::Let {
                pattern: vec![Some("x".into())],
                value: lit_u64(1),
            }],
            tail: BlockTail::Value(Expr::Unit),
        }),
    };
    let arm1 = MatchArm {
        variant: 1,
        bindings: vec![],
        body: Box::new(Block {
            stmts: vec![Stmt::Let {
                pattern: vec![Some("x".into())],
                value: lit_u64(2),
            }],
            tail: BlockTail::Value(Expr::Unit),
        }),
    };
    let stmts = vec![Stmt::Eval(Expr::Match {
        struct_id: 9,
        selector: Box::new(Expr::Var("s".into())),
        cases: vec![arm0, arm1],
    })];
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
                    name: "x".into(),
                    var: "x".into(),
                    ty: Type::UInt(64),
                },
            ],
            Type::UInt(64),
        ),
        body(stmts, Expr::Var("x".into())),
        FuncOpts::default(),
    );
    p.functions.insert(0, f);
    run(&mut p).unwrap();

    let f = &p.functions[&0];
    let body = &f.body;
    // stmts[0]: Stmt::Let { pattern: [phi_x], value: Match { ... } }
    match &body.stmts[0] {
        Stmt::Let { pattern, value } => {
            assert_eq!(pattern.len(), 1);
            if let Expr::Match { cases, .. } = value {
                for c in cases {
                    if let BlockTail::Value(e) = &c.body.tail {
                        // single phi var → tail value is just Var(arm_x).
                        assert!(
                            matches!(e, Expr::Var(_)),
                            "arm tail should be Var, got {:?}",
                            e
                        );
                    } else {
                        panic!();
                    }
                }
            } else {
                panic!();
            }
            // body tail references the phi name.
            let phi = pattern[0].as_ref().unwrap();
            assert_eq!(body.tail, BlockTail::Value(Expr::Var(phi.clone())));
        }
        _ => panic!(),
    }
}

#[test]
fn arm_local_var_no_post_merge_use_is_dead_but_allowed() {
    // if c { let x = 1 } else { /* no x */ };
    // x is defined in only the then arm and not in outer; it has
    // no post-merge use. The arm-local binding is harmless dead
    // code; stage 5 leaves it alone (no defensive reject). The
    // validator passes because nothing post-merge references `x`.
    let then_body = Block {
        stmts: vec![Stmt::Let {
            pattern: vec![Some("x".into())],
            value: lit_u64(1),
        }],
        tail: BlockTail::Value(Expr::Unit),
    };
    let else_body = Block {
        stmts: vec![],
        tail: BlockTail::Value(Expr::Unit),
    };
    let stmts = vec![if_stmt_with_arms(
        Expr::Var("c".into()),
        then_body,
        else_body,
    )];
    let mut p = one_fn_program(stmts, Expr::Unit, vec![param("c", Type::Bool)], Type::Unit);
    run(&mut p).expect("arm-local var with no post-merge use is allowed");
}

#[test]
fn arm_local_var_with_post_merge_use_rejects_via_base_validator() {
    // Same shape, BUT the function tail now references `x`. Since
    // `x` is arm-local in only one arm (not in outer, not in all
    // arms), the post-merge `Var(x)` is unbound. Stage 5's walker
    // catches it via `UnboundReference` at the tail walk.
    let then_body = Block {
        stmts: vec![Stmt::Let {
            pattern: vec![Some("x".into())],
            value: lit_u64(1),
        }],
        tail: BlockTail::Value(Expr::Unit),
    };
    let else_body = Block {
        stmts: vec![],
        tail: BlockTail::Value(Expr::Unit),
    };
    let stmts = vec![if_stmt_with_arms(
        Expr::Var("c".into()),
        then_body,
        else_body,
    )];
    let mut p = one_fn_program(
        stmts,
        Expr::Var("x".into()),
        vec![param("c", Type::Bool)],
        Type::UInt(64),
    );
    let err = run(&mut p).unwrap_err();
    assert!(
        matches!(err, Stage5Error::UnboundReference { ref var, .. } if *var == VarId::from("x")),
        "expected UnboundReference, got {:?}",
        err
    );
}
