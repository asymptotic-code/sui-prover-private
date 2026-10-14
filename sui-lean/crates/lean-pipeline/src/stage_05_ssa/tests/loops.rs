//! Phase 5 + 6: While `loop_state` synthesis + Continue/Break value
//! rewrites + cross-level Break/Continue.
//!
//! Covers:
//! - Simple counter loop -- `loop_state = [i]`; Continue carries the
//!   updated i; post-loop name binds to the loop's exit value.
//! - Two-var loop_state.
//! - Empty loop_state (body bindings not referenced post-loop) -- no
//!   surrounding Stmt::Let; emitted as Stmt::Eval.
//! - Sequential while loops: each gets its own loop_state.
//! - Inner-Break (level 0) carries innermost loop_state.
//! - Cross-level Break (level 1) carries outer's loop_state from
//!   inside an inner loop.
//! - Cross-level Continue (level 1).
//! - Defensive: `UninitFromZeroIterLoop` when loop body binds a var
//!   referenced post-loop but never bound in outer.

use crate::ir::{BinOp, Block, BlockTail, BorrowEdge, BorrowNode, Expr, Stmt, Type, VarId};
use crate::stage_05_ssa::{run, Stage5Error};

use super::fixtures::*;

/// Build `Stmt::Eval(While { header, cond, body })`.
fn while_eval(header: Block, cond: Expr, body: Block) -> Stmt {
    Stmt::Eval(Expr::While {
        header: Box::new(header),
        cond: Box::new(cond),
        body: Box::new(body),
        iter_locals: Vec::new(),
        header_exit_locals: Vec::new(),
        live_out: vec![],
    })
}

fn empty_header() -> Block {
    Block {
        stmts: vec![],
        tail: BlockTail::Value(Expr::Unit),
    }
}

#[test]
fn simple_counter_loop_state_threads_i() {
    // let i = 0;
    // while (i < n) { let i = i + 1 };  // body rebinds i
    // use i
    let body = Block {
        stmts: vec![Stmt::Let {
            pattern: vec![Some("i".into())],
            value: Expr::BinOp {
                op: BinOp::Add,
                lhs: Box::new(Expr::Var("i".into())),
                rhs: Box::new(lit_u64(1)),
            },
        }],
        tail: BlockTail::Continue {
            level: 0,
            value: Box::new(Expr::Unit),
        },
    };
    let cond = Expr::BinOp {
        op: BinOp::Lt,
        lhs: Box::new(Expr::Var("i".into())),
        rhs: Box::new(Expr::Var("n".into())),
    };
    let stmts = vec![
        Stmt::Let {
            pattern: vec![Some("i".into())],
            value: lit_u64(0),
        },
        while_eval(empty_header(), cond, body),
    ];
    let mut p = one_fn_program(
        stmts,
        Expr::Var("i".into()),
        vec![param("n", Type::UInt(64))],
        Type::UInt(64),
    );
    run(&mut p).unwrap();

    let body = body_of(&p);
    // stmts[0]: let i_0 = 0
    match &body.stmts[0] {
        Stmt::Let { pattern, .. } => assert_eq!(pattern, &vec![Some(VarId::from("i_0"))]),
        _ => panic!(),
    }
    // stmts[1]: should be Stmt::Let { pattern: [i_<post>], value: While { ... } }
    match &body.stmts[1] {
        Stmt::Let { pattern, value } => {
            assert_eq!(pattern.len(), 1);
            let i_post = pattern[0].as_ref().unwrap();
            // Body tail should reference i_post.
            assert_eq!(body.tail, BlockTail::Value(Expr::Var(i_post.clone())));
            // The While's body: tail Continue carries Tuple([Var(i_inner_rebound)])
            // (single-element collapsed to Var by the impl).
            if let Expr::While {
                body: while_body,
                cond,
                ..
            } = value
            {
                // Body tail must carry the rebound i as a plain Value
                // (the implicit-continue convention). Iteration-local
                // was i_1; body rebind made i_2.
                if let BlockTail::Value(Expr::Var(v)) = &while_body.tail {
                    assert_eq!(*v, VarId::from("i_2"));
                } else {
                    panic!(
                        "expected body tail Value(Var(i_2)), got {:?}",
                        while_body.tail
                    );
                }
                // cond should reference i_1 (the iteration-local).
                if let Expr::BinOp { lhs, .. } = cond.as_ref() {
                    if let Expr::Var(v) = lhs.as_ref() {
                        assert_eq!(*v, VarId::from("i_1"));
                    } else {
                        panic!();
                    }
                } else {
                    panic!();
                }
            } else {
                panic!();
            }
        }
        _ => panic!("expected Stmt::Let for post-loop binding"),
    }
}

#[test]
fn two_var_loop_state() {
    // let i = 0; let sum = 0;
    // while (i < n) { let sum = sum + i; let i = i + 1 };
    // use (i, sum)
    let body = Block {
        stmts: vec![
            Stmt::Let {
                pattern: vec![Some("sum".into())],
                value: Expr::BinOp {
                    op: BinOp::Add,
                    lhs: Box::new(Expr::Var("sum".into())),
                    rhs: Box::new(Expr::Var("i".into())),
                },
            },
            Stmt::Let {
                pattern: vec![Some("i".into())],
                value: Expr::BinOp {
                    op: BinOp::Add,
                    lhs: Box::new(Expr::Var("i".into())),
                    rhs: Box::new(lit_u64(1)),
                },
            },
        ],
        tail: BlockTail::Continue {
            level: 0,
            value: Box::new(Expr::Unit),
        },
    };
    let cond = Expr::BinOp {
        op: BinOp::Lt,
        lhs: Box::new(Expr::Var("i".into())),
        rhs: Box::new(Expr::Var("n".into())),
    };
    let stmts = vec![
        Stmt::Let {
            pattern: vec![Some("i".into())],
            value: lit_u64(0),
        },
        Stmt::Let {
            pattern: vec![Some("sum".into())],
            value: lit_u64(0),
        },
        while_eval(empty_header(), cond, body),
    ];
    let mut p = one_fn_program(
        stmts,
        Expr::Tuple(vec![Expr::Var("i".into()), Expr::Var("sum".into())]),
        vec![param("n", Type::UInt(64))],
        Type::Tuple(vec![Type::UInt(64), Type::UInt(64)]),
    );
    run(&mut p).unwrap();

    let body = body_of(&p);
    // stmts[2]: let (i_<post>, sum_<post>) = while(...)  -- loop_state sorted ["i", "sum"]
    match &body.stmts[2] {
        Stmt::Let { pattern, value } => {
            assert_eq!(pattern.len(), 2);
            let i_post = pattern[0].as_ref().unwrap();
            let sum_post = pattern[1].as_ref().unwrap();
            assert!(i_post.starts_with("i_"));
            assert!(sum_post.starts_with("sum_"));
            // Body tail uses both post names.
            assert_eq!(
                body.tail,
                BlockTail::Value(Expr::Tuple(vec![
                    Expr::Var(i_post.clone()),
                    Expr::Var(sum_post.clone()),
                ]))
            );
            // The body tail carries Tuple([Var(i_inner), Var(sum_inner)])
            // as a plain Value (implicit-continue convention).
            if let Expr::While {
                body: while_body, ..
            } = value
            {
                if let BlockTail::Value(Expr::Tuple(elems)) = &while_body.tail {
                    assert_eq!(elems.len(), 2);
                } else {
                    panic!("expected body tail Value(Tuple), got {:?}", while_body.tail);
                }
            }
        }
        _ => panic!(),
    }
}

#[test]
fn empty_loop_state_emits_eval() {
    // while (c) { /* body doesn't bind anything used post-loop */ };
    // no use of body-bound vars after.
    let body = Block {
        stmts: vec![],
        tail: BlockTail::Continue {
            level: 0,
            value: Box::new(Expr::Unit),
        },
    };
    let stmts = vec![while_eval(empty_header(), Expr::Var("c".into()), body)];
    let mut p = one_fn_program(stmts, Expr::Unit, vec![param("c", Type::Bool)], Type::Unit);
    run(&mut p).unwrap();

    let body = body_of(&p);
    // Should remain Stmt::Eval(While { ... }).
    match &body.stmts[0] {
        Stmt::Eval(Expr::While { .. }) => {} // OK
        other => panic!("expected Stmt::Eval(While), got {:?}", other),
    }
}

#[test]
fn break_carries_loop_state() {
    // let i = 0;
    // while (c) { if (early) { break } else { let i = i + 1; Continue } };
    // use i
    let then_arm = Block {
        stmts: vec![],
        tail: BlockTail::Break {
            level: 0,
            value: Box::new(Expr::Unit),
        },
    };
    let else_arm = Block {
        stmts: vec![Stmt::Let {
            pattern: vec![Some("i".into())],
            value: Expr::BinOp {
                op: BinOp::Add,
                lhs: Box::new(Expr::Var("i".into())),
                rhs: Box::new(lit_u64(1)),
            },
        }],
        tail: BlockTail::Continue {
            level: 0,
            value: Box::new(Expr::Unit),
        },
    };
    let body = Block {
        stmts: vec![Stmt::Eval(Expr::If {
            cond: Box::new(Expr::Var("early".into())),
            then_branch: Box::new(then_arm),
            else_branch: Box::new(else_arm),
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
        while_eval(empty_header(), Expr::Var("c".into()), body),
    ];
    let mut p = one_fn_program(
        stmts,
        Expr::Var("i".into()),
        vec![param("c", Type::Bool), param("early", Type::Bool)],
        Type::UInt(64),
    );
    run(&mut p).unwrap();
    // Just confirm the run succeeded and the post-loop pattern includes i.
    let body = body_of(&p);
    match &body.stmts[1] {
        Stmt::Let { pattern, .. } => {
            assert_eq!(pattern.len(), 1);
        }
        _ => panic!(),
    }
}

#[test]
fn cross_level_break_carries_outer_loop_state() {
    // let outer_x = 0;
    // while (a) {
    //     while (b) {
    //         break 1  // breaks outer loop
    //     }
    //     let outer_x = outer_x + 1;
    //     Continue
    // };
    // use outer_x
    let inner_body = Block {
        stmts: vec![],
        tail: BlockTail::Break {
            level: 1,
            value: Box::new(Expr::Unit),
        },
    };
    let inner_while = while_eval(empty_header(), Expr::Var("b".into()), inner_body);
    let outer_body = Block {
        stmts: vec![
            inner_while,
            Stmt::Let {
                pattern: vec![Some("outer_x".into())],
                value: Expr::BinOp {
                    op: BinOp::Add,
                    lhs: Box::new(Expr::Var("outer_x".into())),
                    rhs: Box::new(lit_u64(1)),
                },
            },
        ],
        tail: BlockTail::Continue {
            level: 0,
            value: Box::new(Expr::Unit),
        },
    };
    let stmts = vec![
        Stmt::Let {
            pattern: vec![Some("outer_x".into())],
            value: lit_u64(0),
        },
        while_eval(empty_header(), Expr::Var("a".into()), outer_body),
    ];
    let mut p = one_fn_program(
        stmts,
        Expr::Var("outer_x".into()),
        vec![param("a", Type::Bool), param("b", Type::Bool)],
        Type::UInt(64),
    );
    run(&mut p).unwrap();

    // Confirm: inner Break level=1 carries outer's loop_state (which is [outer_x]).
    let body = body_of(&p);
    match &body.stmts[1] {
        Stmt::Let {
            value: Expr::While {
                body: outer_body, ..
            },
            ..
        } => {
            // Find the inner While in outer body's stmts.
            let inner = match &outer_body.stmts[0] {
                Stmt::Eval(Expr::While { body, .. }) => (**body).clone(),
                Stmt::Let {
                    value: Expr::While { body, .. },
                    ..
                } => (**body).clone(),
                other => panic!("expected inner While, got {:?}", other),
            };
            // Inner body tail is Break { level: 1, value: ... }
            match &inner.tail {
                BlockTail::Break { level, value } => {
                    assert_eq!(level, &1u32);
                    // Value should be Var(outer_x_iter) (1-element collapsed).
                    if let Expr::Var(v) = value.as_ref() {
                        // outer_x iteration-local; the exact suffix
                        // depends on order, but it must be an
                        // outer_x_<n> name.
                        assert!(v.starts_with("outer_x_"));
                    } else {
                        panic!("Break value not Var: {:?}", value);
                    }
                }
                other => panic!("expected Break tail, got {:?}", other),
            }
        }
        _ => panic!(),
    }
}

#[test]
fn cross_level_continue_carries_outer_loop_state() {
    // let outer_x = 0;
    // while (a) {
    //     while (b) {
    //         continue 1  // continues outer
    //     }
    //     let outer_x = outer_x + 1;
    //     Continue
    // };
    // use outer_x
    let inner_body = Block {
        stmts: vec![],
        tail: BlockTail::Continue {
            level: 1,
            value: Box::new(Expr::Unit),
        },
    };
    let inner_while = while_eval(empty_header(), Expr::Var("b".into()), inner_body);
    let outer_body = Block {
        stmts: vec![
            inner_while,
            Stmt::Let {
                pattern: vec![Some("outer_x".into())],
                value: Expr::BinOp {
                    op: BinOp::Add,
                    lhs: Box::new(Expr::Var("outer_x".into())),
                    rhs: Box::new(lit_u64(1)),
                },
            },
        ],
        tail: BlockTail::Continue {
            level: 0,
            value: Box::new(Expr::Unit),
        },
    };
    let stmts = vec![
        Stmt::Let {
            pattern: vec![Some("outer_x".into())],
            value: lit_u64(0),
        },
        while_eval(empty_header(), Expr::Var("a".into()), outer_body),
    ];
    let mut p = one_fn_program(
        stmts,
        Expr::Var("outer_x".into()),
        vec![param("a", Type::Bool), param("b", Type::Bool)],
        Type::UInt(64),
    );
    // Should succeed.
    run(&mut p).unwrap();
}

#[test]
fn uninit_from_zero_iter_loop_threads_typed_default() {
    // while (c) { let x = 1 }; return x  -- x is body-bound, used
    // post-loop, and typed (u64). Stage 5 now threads it as a
    // loop-carried var with a `default` init rather than rejecting: in
    // valid Move a post-loop read implies the loop ran >= 1, so the
    // default is never observed. (Mirrors cetus MoveSTL
    // `skip_list::insert`'s World dynamic-field store vars.)
    let body = Block {
        stmts: vec![Stmt::Let {
            pattern: vec![Some("x".into())],
            value: lit_u64(1),
        }],
        tail: BlockTail::Continue {
            level: 0,
            value: Box::new(Expr::Unit),
        },
    };
    let stmts = vec![while_eval(empty_header(), Expr::Var("c".into()), body)];
    let mut p = one_fn_program(
        stmts,
        Expr::Var("x".into()),
        vec![param("c", Type::Bool)],
        Type::UInt(64),
    );
    run(&mut p).expect("typed uninit loop-carried var should thread with a default init");
}

#[test]
fn while_with_body_local_var_and_no_post_loop_use_emits_eval() {
    // let stop = false;
    // while (!stop) { /* body uses some local but doesn't rebind stop */ };
    // (function tail Unit; nothing referenced post-loop)
    //
    // body binds `local`, but `local` is NOT referenced in
    // header/cond or post-loop -> not in loop_state.
    // stop is in cond but NOT bound in body -> not in loop_state.
    // loop_state == empty -> Stmt::Eval(While).
    let body = Block {
        stmts: vec![Stmt::Let {
            pattern: vec![Some("local".into())],
            value: lit_u64(7),
        }],
        tail: BlockTail::Continue {
            level: 0,
            value: Box::new(Expr::Unit),
        },
    };
    let cond = Expr::UnOp {
        op: crate::ir::UnOp::Not,
        operand: Box::new(Expr::Var("stop".into())),
    };
    let stmts = vec![
        Stmt::Let {
            pattern: vec![Some("stop".into())],
            value: crate::ir::Expr::Const(crate::ir::Const::Bool(false)),
        },
        while_eval(empty_header(), cond, body),
    ];
    let mut p = one_fn_program(stmts, Expr::Unit, vec![], Type::Unit);
    run(&mut p).unwrap();

    let body = body_of(&p);
    match &body.stmts[1] {
        Stmt::Eval(Expr::While { .. }) => {}
        Stmt::Let { pattern, .. } => panic!(
            "expected Stmt::Eval(While), got Stmt::Let pattern={:?}",
            pattern
        ),
        other => panic!("got {:?}", other),
    }
}

#[test]
fn iter_locals_carry_pre_loop_init_value() {
    // let i = 0;                              // i_0 = 0
    // while (i < n) { let i = i + 1 };        // iter_local i_1 init=Var(i_0)
    // (i not used post-loop, so loop_state is empty unless cond references i)
    // cond references i -> loop_state = [i] -> iter_local = i_1 with init = i_0.
    let body = Block {
        stmts: vec![Stmt::Let {
            pattern: vec![Some("i".into())],
            value: Expr::BinOp {
                op: BinOp::Add,
                lhs: Box::new(Expr::Var("i".into())),
                rhs: Box::new(lit_u64(1)),
            },
        }],
        tail: BlockTail::Continue {
            level: 0,
            value: Box::new(Expr::Unit),
        },
    };
    let cond = Expr::BinOp {
        op: BinOp::Lt,
        lhs: Box::new(Expr::Var("i".into())),
        rhs: Box::new(Expr::Var("n".into())),
    };
    let stmts = vec![
        Stmt::Let {
            pattern: vec![Some("i".into())],
            value: lit_u64(0),
        },
        while_eval(empty_header(), cond, body),
    ];
    let mut p = one_fn_program(
        stmts,
        Expr::Unit,
        vec![param("n", Type::UInt(64))],
        Type::Unit,
    );
    run(&mut p).unwrap();

    let body = body_of(&p);
    // Find the While inside the post-loop Let.
    match &body.stmts[1] {
        Stmt::Let {
            value: Expr::While { iter_locals, .. },
            ..
        } => {
            assert_eq!(iter_locals.len(), 1);
            let (binder, init) = &iter_locals[0];
            // The iter_local binder is i_1.
            assert_eq!(*binder, VarId::from("i_1"));
            // The init expression is Var(i_0) -- the pre-loop SSA
            // name for source-name `i`.
            assert_eq!(*init, Expr::Var(VarId::from("i_0")));
        }
        other => panic!("expected Stmt::Let{{value: While}}, got {:?}", other),
    }
}

#[test]
fn header_mutation_is_loop_carried() {
    // A structured while header runs before every condition check. Mutations
    // there must be carried just like body mutations:
    //
    //   let i = 0;
    //   while ({ tick = tick + 1; i < n }) { i = i + 1 };
    //   tick
    //
    // This is the shape produced for Sui test_scenario::next_with_context,
    // where `tick` is the World token. Omitting header binds from loop-state
    // discovery made every iteration consume the pre-loop token and returned
    // that stale token at the cond-false exit.
    let header = Block {
        stmts: vec![Stmt::Let {
            pattern: vec![Some("tick".into())],
            value: Expr::BinOp {
                op: BinOp::Add,
                lhs: Box::new(Expr::Var("tick".into())),
                rhs: Box::new(lit_u64(1)),
            },
        }],
        tail: BlockTail::Value(Expr::Unit),
    };
    let body = Block {
        stmts: vec![Stmt::Let {
            pattern: vec![Some("i".into())],
            value: Expr::BinOp {
                op: BinOp::Add,
                lhs: Box::new(Expr::Var("i".into())),
                rhs: Box::new(lit_u64(1)),
            },
        }],
        tail: BlockTail::Continue {
            level: 0,
            value: Box::new(Expr::Unit),
        },
    };
    let cond = Expr::BinOp {
        op: BinOp::Lt,
        lhs: Box::new(Expr::Var("i".into())),
        rhs: Box::new(Expr::Var("n".into())),
    };
    let stmts = vec![
        Stmt::Let {
            pattern: vec![Some("i".into())],
            value: lit_u64(0),
        },
        while_eval(header, cond, body),
    ];
    let mut p = one_fn_program(
        stmts,
        Expr::Var("tick".into()),
        vec![param("tick", Type::UInt(64)), param("n", Type::UInt(64))],
        Type::UInt(64),
    );
    run(&mut p).unwrap();

    let body = body_of(&p);
    let (pattern, iter_locals, header_exit_locals) = match &body.stmts[1] {
        Stmt::Let {
            pattern,
            value:
                Expr::While {
                    iter_locals,
                    header_exit_locals,
                    ..
                },
        } => (pattern, iter_locals, header_exit_locals),
        other => panic!("expected loop-result Let, got {:?}", other),
    };
    assert_eq!(
        iter_locals.len(),
        2,
        "i and header-mutated tick must be carried"
    );
    assert_eq!(iter_locals[0].1, Expr::Var(VarId::from("i_0")));
    assert_eq!(iter_locals[1].1, Expr::Var(VarId::from("tick_0")));
    assert_eq!(
        header_exit_locals,
        &vec![VarId::from("i_1"), VarId::from("tick_2")],
        "the cond-false exit must observe the post-header tick"
    );
    assert_eq!(
        pattern.len(),
        2,
        "loop result must expose both carried values"
    );
    let tick_post = pattern[1].as_ref().expect("post-loop tick slot");
    assert_eq!(
        body.tail,
        BlockTail::Value(Expr::Var(tick_post.clone())),
        "function exit must use the post-loop tick"
    );
}

#[test]
fn condition_only_header_guard_is_never_carried() {
    // `limit` and `guard` are rebound by the header before anything reads
    // them, so neither carries a value across the back edge. An `.aborts`
    // companion is the same function's body and must agree: a face that
    // carried them would give its loop helpers a different signature from
    // the source face's for no observable difference.
    let make = |name: &str| {
        let header = Block {
            stmts: vec![
                Stmt::Let {
                    pattern: vec![Some("limit".into())],
                    value: Expr::Var("n".into()),
                },
                Stmt::Let {
                    pattern: vec![Some("guard".into())],
                    value: Expr::BinOp {
                        op: BinOp::Lt,
                        lhs: Box::new(Expr::Var("i".into())),
                        rhs: Box::new(Expr::Var("limit".into())),
                    },
                },
            ],
            tail: BlockTail::Value(Expr::Unit),
        };
        let body = Block {
            stmts: vec![Stmt::Let {
                pattern: vec![Some("i".into())],
                value: Expr::BinOp {
                    op: BinOp::Add,
                    lhs: Box::new(Expr::Var("i".into())),
                    rhs: Box::new(lit_u64(1)),
                },
            }],
            tail: BlockTail::Continue {
                level: 0,
                value: Box::new(Expr::Unit),
            },
        };
        let mut p = one_fn_program(
            vec![
                Stmt::Let {
                    pattern: vec![Some("i".into())],
                    value: lit_u64(0),
                },
                while_eval(header, Expr::Var("guard".into()), body),
            ],
            Expr::Unit,
            vec![
                param("guard", Type::Bool),
                param("limit", Type::UInt(64)),
                param("n", Type::UInt(64)),
            ],
            Type::Unit,
        );
        p.functions.get_mut(&0).unwrap().name = name.to_owned();
        p
    };
    let carried_inits = |p: &crate::ir::Program| match &body_of(p).stmts[1] {
        Stmt::Let {
            value: Expr::While { iter_locals, .. },
            ..
        } => iter_locals
            .iter()
            .map(|(_, init)| init.clone())
            .collect::<Vec<_>>(),
        other => panic!("expected loop-result Let, got {:?}", other),
    };

    let mut source = make("f");
    run(&mut source).unwrap();
    assert_eq!(carried_inits(&source), vec![Expr::Var("i_0".into())]);

    let mut aborts = make("f.aborts");
    run(&mut aborts).unwrap();
    assert_eq!(carried_inits(&aborts), vec![Expr::Var("i_0".into())]);
}

#[test]
fn header_bind_read_only_downstream_is_not_carried() {
    // `mid` is bound by the header on every iteration and read only after
    // that bind (by the condition and by the body). Every read sees the
    // value this iteration wrote, so carrying it would add a parameter to
    // `while_N`, `while_N.after` and the `Step.cont` payload that no reader
    // can distinguish from `default`.
    let header = Block {
        stmts: vec![Stmt::Let {
            pattern: vec![Some("mid".into())],
            value: Expr::BinOp {
                op: BinOp::Add,
                lhs: Box::new(Expr::Var("i".into())),
                rhs: Box::new(lit_u64(1)),
            },
        }],
        tail: BlockTail::Value(Expr::Unit),
    };
    let body = Block {
        stmts: vec![Stmt::Let {
            pattern: vec![Some("i".into())],
            value: Expr::BinOp {
                op: BinOp::Add,
                lhs: Box::new(Expr::Var("mid".into())),
                rhs: Box::new(lit_u64(1)),
            },
        }],
        tail: BlockTail::Continue {
            level: 0,
            value: Box::new(Expr::Unit),
        },
    };
    let cond = Expr::BinOp {
        op: BinOp::Lt,
        lhs: Box::new(Expr::Var("mid".into())),
        rhs: Box::new(Expr::Var("n".into())),
    };
    let mut p = one_fn_program(
        vec![
            Stmt::Let {
                pattern: vec![Some("i".into())],
                value: lit_u64(0),
            },
            while_eval(header, cond, body),
        ],
        Expr::Unit,
        vec![param("n", Type::UInt(64))],
        Type::Unit,
    );
    run(&mut p).unwrap();

    let (iter_locals, header_exit_locals) = match &body_of(&p).stmts[1] {
        Stmt::Let {
            value:
                Expr::While {
                    iter_locals,
                    header_exit_locals,
                    ..
                },
            ..
        } => (iter_locals, header_exit_locals),
        other => panic!("expected loop-result Let, got {:?}", other),
    };
    assert_eq!(
        iter_locals.iter().map(|(b, _)| b).collect::<Vec<_>>(),
        vec![&VarId::from("i_1")],
        "only `i` crosses the back edge"
    );
    assert_eq!(header_exit_locals, &vec![VarId::from("i_1")]);
}

#[test]
fn defensive_uninit_in_cond_only_rejects() {
    // while (x < n) { let x = x + 1 };
    // `x` is referenced in cond and rebound in body, but never in
    // outer scope nor post-loop. Before tightening, this slipped
    // through and produced ill-formed IR caught later by the base
    // validator. Now stage 5 rejects with UninitFromZeroIterLoop.
    let body = Block {
        stmts: vec![Stmt::Let {
            pattern: vec![Some("x".into())],
            value: Expr::BinOp {
                op: BinOp::Add,
                lhs: Box::new(Expr::Var("x".into())),
                rhs: Box::new(lit_u64(1)),
            },
        }],
        tail: BlockTail::Continue {
            level: 0,
            value: Box::new(Expr::Unit),
        },
    };
    let cond = Expr::BinOp {
        op: BinOp::Lt,
        lhs: Box::new(Expr::Var("x".into())),
        rhs: Box::new(Expr::Var("n".into())),
    };
    let stmts = vec![while_eval(empty_header(), cond, body)];
    let mut p = one_fn_program(
        stmts,
        Expr::Unit,
        vec![param("n", Type::UInt(64))],
        Type::Unit,
    );
    let err = run(&mut p).unwrap_err();
    match err {
        Stage5Error::UninitFromZeroIterLoop { vars, .. } => {
            assert_eq!(vars, vec![VarId::from("x")]);
        }
        other => panic!("expected UninitFromZeroIterLoop, got {:?}", other),
    }
}

#[test]
fn write_back_on_capture_lifts_into_loop_state() {
    // Phase A regression: an outer-scope var mutated by a WriteBack
    // chain inside a while body must be lifted into loop_state, even
    // when no sibling stmt of the while references it post-loop.
    //
    // Pre-stage-5 shape (modelling stage 3's mut-to-let on
    //   `while (i < n) { ...; *&mut tick = X; i = i + 1 }`):
    //
    //   let i = 0;
    //   while (i < n) {
    //       let child = BorrowLoc(tick);
    //       let tick  = WriteBack(Reference(tick), Direct, child);
    //       let i     = i + 1;
    //   };
    //   // post-loop continuation: nothing references tick
    //
    // Outer-scope binding: function param `tick`. `tick` is NOT in
    // the surrounding block's refs / cond, but the body rebinds it
    // via WriteBack -- tick is a capture-mutation and must thread
    // through iter_locals. Without the lift, every iteration sees
    // the pre-loop tick value and mutations are silently dropped.
    let body = Block {
        stmts: vec![
            Stmt::Let {
                pattern: vec![Some("child".into())],
                value: Expr::BorrowLoc("tick".into()),
            },
            Stmt::Let {
                pattern: vec![Some("tick".into())],
                value: Expr::WriteBack {
                    node: BorrowNode::Reference("tick".into()),
                    edge: BorrowEdge::Direct,
                    child: "child".into(),
                    world: None,
                },
            },
            Stmt::Let {
                pattern: vec![Some("i".into())],
                value: Expr::BinOp {
                    op: BinOp::Add,
                    lhs: Box::new(Expr::Var("i".into())),
                    rhs: Box::new(lit_u64(1)),
                },
            },
        ],
        tail: BlockTail::Continue {
            level: 0,
            value: Box::new(Expr::Unit),
        },
    };
    let cond = Expr::BinOp {
        op: BinOp::Lt,
        lhs: Box::new(Expr::Var("i".into())),
        rhs: Box::new(Expr::Var("n".into())),
    };
    let stmts = vec![
        Stmt::Let {
            pattern: vec![Some("i".into())],
            value: lit_u64(0),
        },
        while_eval(empty_header(), cond, body),
    ];
    let mut p = one_fn_program(
        stmts,
        Expr::Unit,
        vec![param("tick", Type::UInt(64)), param("n", Type::UInt(64))],
        Type::Unit,
    );
    run(&mut p).unwrap();

    let body = body_of(&p);
    let (pattern, while_expr) = match &body.stmts[1] {
        Stmt::Let { pattern, value } => (pattern, value),
        other => panic!("expected Stmt::Let{{value: While}}, got {:?}", other),
    };
    assert_eq!(
        pattern.len(),
        2,
        "post-loop pattern must include tick (capture) + i (counter); got {:?}",
        pattern,
    );
    let i_post = pattern[0].as_ref().expect("i post slot");
    let tick_post = pattern[1].as_ref().expect("tick post slot");
    assert!(
        i_post.starts_with("i_"),
        "first post slot should be i_<n>, got {:?}",
        i_post,
    );
    assert!(
        tick_post.starts_with("tick_"),
        "second post slot should be tick_<n>, got {:?}",
        tick_post,
    );

    let (iter_locals, while_body) = match while_expr {
        Expr::While {
            iter_locals, body, ..
        } => (iter_locals, body),
        other => panic!("expected Expr::While, got {:?}", other),
    };
    assert_eq!(
        iter_locals.len(),
        2,
        "iter_locals must include the capture; got {:?}",
        iter_locals,
    );
    // BTreeSet ordering: i before tick.
    assert_eq!(iter_locals[0].1, Expr::Var(VarId::from("i_0")));
    assert_eq!(iter_locals[1].1, Expr::Var(VarId::from("tick_0")));

    let tail_value = match &while_body.tail {
        BlockTail::Value(v) => v,
        other => panic!("expected body tail Value(...), got {:?}", other),
    };
    let tuple_elems = match tail_value {
        Expr::Tuple(es) => es,
        other => panic!(
            "expected body tail to pack iter_locals as Tuple, got {:?}",
            other,
        ),
    };
    assert_eq!(
        tuple_elems.len(),
        2,
        "body tail tuple must carry both iter-local exit values; got {:?}",
        tuple_elems,
    );
    for e in tuple_elems {
        match e {
            Expr::Var(_) => {}
            other => panic!("body tail tuple element should be Var, got {:?}", other),
        }
    }
}
