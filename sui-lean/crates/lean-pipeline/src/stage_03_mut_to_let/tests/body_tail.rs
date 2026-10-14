//! Tests for Transform 5: body Return + fall-off tail augmentation.

use crate::ir::builder::{block, just, tail_return, tail_value};
use crate::ir::{Block, BlockTail, Expr, MatchArm, Stmt, Type, VarId};
use crate::stage_03_mut_to_let::{augment_body_tails, augment_signatures};

use super::fixtures::*;

#[test]
fn body_tail_unaffected_for_function_without_mut() {
    // Run signatures first (no-op for non-mut), then body_tail.
    let f = func(
        "f",
        sig(vec![param("x", Type::UInt(64))], Type::UInt(64)),
        body(vec![], Expr::Var(VarId::from("x"))),
        FuncOpts::default(),
    );
    let mut program = program_with(vec![(0, f)]);
    let before = program.clone();
    augment_signatures(&mut program).unwrap();
    augment_body_tails(&mut program).unwrap();
    assert_eq!(program, before);
}

#[test]
fn one_mut_unit_return_void_fn_gets_singleton_tuple_tail() {
    // fn f(x: &mut T) { } -- tail Value(Unit) becomes Value(Tuple([Var(x)])).
    // Always-Tuple: even singleton augmented values are wrapped.
    let f = func(
        "f",
        sig(
            vec![param("x", mut_ref(Type::UInt(64), Type::UInt(64)))],
            Type::Unit,
        ),
        body(vec![], Expr::Unit),
        FuncOpts::default(),
    );
    let mut program = program_with(vec![(0, f)]);
    augment_signatures(&mut program).unwrap();
    augment_body_tails(&mut program).unwrap();

    let body = &program.functions[&0].body;
    match &body.tail {
        BlockTail::Value(Expr::Tuple(items)) => {
            assert_eq!(items.len(), 1);
            assert_eq!(items[0], Expr::Var(VarId::from("x")));
        }
        other => panic!("expected Value(Tuple([Var(x)])), got {:?}", other),
    }
}

#[test]
fn unit_return_preserves_effectful_top_level_tail_before_mut_state() {
    // A Unit-valued control expression can still be effectful. This is the
    // shape produced by a structured C function whose two arms return early,
    // with one arm calling a function that updates threaded mutable-global
    // state. Returning `x` must not erase the conditional call.
    let conditional = Expr::If {
        cond: Box::new(Expr::Const(crate::ir::Const::Bool(true))),
        then_branch: Box::new(block(
            vec![Stmt::Eval(Expr::Call {
                fun: 1,
                type_args: Vec::new(),
                args: Vec::new(),
            })],
            tail_return(Expr::Unit),
        )),
        else_branch: Box::new(block(Vec::new(), tail_return(Expr::Unit))),
    };
    let f = func(
        "f",
        sig(
            vec![param("x", mut_ref(Type::UInt(64), Type::UInt(64)))],
            Type::Unit,
        ),
        body(Vec::new(), conditional),
        FuncOpts::default(),
    );
    let callee = func(
        "effect",
        sig(Vec::new(), Type::Unit),
        body(Vec::new(), Expr::Unit),
        FuncOpts::default(),
    );
    let mut program = program_with(vec![(0, f), (1, callee)]);
    augment_signatures(&mut program).unwrap();
    augment_body_tails(&mut program).unwrap();

    let body = &program.functions[&0].body;
    let Stmt::Eval(Expr::If { then_branch, .. }) = &body.stmts[0] else {
        panic!("effectful Unit tail must be sequenced before returned mutable state")
    };
    assert!(matches!(
        &then_branch.stmts[..],
        [Stmt::Eval(Expr::Call { fun: 1, .. })]
    ));
    assert!(matches!(
        &then_branch.tail,
        BlockTail::Return(value)
            if matches!(value.as_ref(), Expr::Tuple(items)
                if items == &vec![Expr::Var(VarId::from("x"))])
    ));
    assert_eq!(
        body.tail,
        BlockTail::Value(Expr::Tuple(vec![Expr::Var(VarId::from("x"))]))
    );

    let after_once = program.clone();
    augment_body_tails(&mut program).unwrap();
    assert_eq!(program, after_once);
}

#[test]
fn one_mut_value_return_gets_tuple_tail() {
    // fn f(x: &mut T): U { 42 } -- tail Value(42) becomes Value(Tuple([42, Var(x)]))
    let f = func(
        "f",
        sig(
            vec![param("x", mut_ref(Type::UInt(64), Type::UInt(64)))],
            Type::UInt(64),
        ),
        body(vec![], lit_u64(42)),
        FuncOpts::default(),
    );
    let mut program = program_with(vec![(0, f)]);
    augment_signatures(&mut program).unwrap();
    augment_body_tails(&mut program).unwrap();

    match &program.functions[&0].body.tail {
        BlockTail::Value(Expr::Tuple(items)) => {
            assert_eq!(items.len(), 2);
            assert_eq!(items[0], lit_u64(42));
            assert_eq!(items[1], Expr::Var(VarId::from("x")));
        }
        other => panic!("expected Value(Tuple([42, Var(x)])), got {:?}", other),
    }
}

#[test]
fn two_muts_unit_return_gets_tuple_of_muts() {
    let f = func(
        "f",
        sig(
            vec![
                param("x", mut_ref(Type::UInt(64), Type::UInt(64))),
                param("y", mut_ref(Type::Bool, Type::Bool)),
            ],
            Type::Unit,
        ),
        body(vec![], Expr::Unit),
        FuncOpts::default(),
    );
    let mut program = program_with(vec![(0, f)]);
    augment_signatures(&mut program).unwrap();
    augment_body_tails(&mut program).unwrap();

    match &program.functions[&0].body.tail {
        BlockTail::Value(Expr::Tuple(items)) => {
            assert_eq!(items.len(), 2);
            assert_eq!(items[0], Expr::Var(VarId::from("x")));
            assert_eq!(items[1], Expr::Var(VarId::from("y")));
        }
        other => panic!("expected Tuple([Var(x), Var(y)]), got {:?}", other),
    }
}

#[test]
fn existing_tuple_return_flattens() {
    let f = func(
        "f",
        sig(
            vec![param("x", mut_ref(Type::UInt(64), Type::UInt(64)))],
            Type::Tuple(vec![Type::UInt(64), Type::Bool]),
        ),
        body(
            vec![],
            Expr::Tuple(vec![lit_u64(0), Expr::Const(crate::ir::Const::Bool(false))]),
        ),
        FuncOpts::default(),
    );
    let mut program = program_with(vec![(0, f)]);
    augment_signatures(&mut program).unwrap();
    augment_body_tails(&mut program).unwrap();

    match &program.functions[&0].body.tail {
        BlockTail::Value(Expr::Tuple(items)) => {
            // [0, false, Var(x)] -- flattened, not nested
            assert_eq!(items.len(), 3);
            assert_eq!(items[0], lit_u64(0));
            assert_eq!(items[2], Expr::Var(VarId::from("x")));
        }
        other => panic!("expected flattened Tuple, got {:?}", other),
    }
}

#[test]
fn inner_return_in_if_arm_gets_augmented() {
    // fn f(x: &mut T): U { if (c) { return 7 } else { } 0 }
    let then_branch = block(vec![], tail_return(lit_u64(7)));
    let else_branch = block(vec![], tail_value(Expr::Unit));
    let if_expr = Expr::If {
        cond: Box::new(Expr::Const(crate::ir::Const::Bool(true))),
        then_branch: Box::new(then_branch),
        else_branch: Box::new(else_branch),
    };
    let f = func(
        "f",
        sig(
            vec![param("x", mut_ref(Type::UInt(64), Type::UInt(64)))],
            Type::UInt(64),
        ),
        body(vec![Stmt::Eval(if_expr)], lit_u64(0)),
        FuncOpts::default(),
    );
    let mut program = program_with(vec![(0, f)]);
    augment_signatures(&mut program).unwrap();
    augment_body_tails(&mut program).unwrap();

    // Check the inner Return tail in the then-arm is augmented.
    if let Stmt::Eval(Expr::If { then_branch, .. }) = &program.functions[&0].body.stmts[0] {
        match &then_branch.tail {
            BlockTail::Return(value) => match value.as_ref() {
                Expr::Tuple(items) => {
                    assert_eq!(items.len(), 2);
                    assert_eq!(items[0], lit_u64(7));
                    assert_eq!(items[1], Expr::Var(VarId::from("x")));
                }
                other => panic!("expected augmented Tuple, got {:?}", other),
            },
            other => panic!("expected Return tail, got {:?}", other),
        }
    } else {
        panic!("expected If at body stmt 0");
    }

    // Top-level fall-off tail should also be augmented.
    match &program.functions[&0].body.tail {
        BlockTail::Value(Expr::Tuple(items)) => {
            assert_eq!(items.len(), 2);
            assert_eq!(items[0], lit_u64(0));
            assert_eq!(items[1], Expr::Var(VarId::from("x")));
        }
        other => panic!("expected augmented Value tail, got {:?}", other),
    }
}

#[test]
fn inner_value_tail_in_if_arm_not_augmented() {
    // An inner If arm's Value tail (which IS NOT a function exit)
    // should NOT be augmented -- only Return tails are.
    let then_branch = block(vec![], tail_value(lit_u64(7)));
    let else_branch = block(vec![], tail_value(lit_u64(8)));
    let if_expr = Expr::If {
        cond: Box::new(Expr::Const(crate::ir::Const::Bool(true))),
        then_branch: Box::new(then_branch),
        else_branch: Box::new(else_branch),
    };
    let f = func(
        "f",
        sig(
            vec![param("x", mut_ref(Type::UInt(64), Type::UInt(64)))],
            Type::UInt(64),
        ),
        body(vec![], if_expr),
        FuncOpts::default(),
    );
    let mut program = program_with(vec![(0, f)]);
    augment_signatures(&mut program).unwrap();
    augment_body_tails(&mut program).unwrap();

    // A block-bearing result is evaluated in statement position so Stage 5
    // can join both its result and any mutable state changed by one arm.
    let body = &program.functions[&0].body;
    let Stmt::Let { pattern, value } = &body.stmts[0] else {
        panic!("top-level If result must be bound before the augmented tail")
    };
    let [Some(result)] = &pattern[..] else {
        panic!("scalar If result must have one binder: {pattern:?}")
    };
    assert_eq!(result, &VarId::from("__mut_tail_result_0"));
    let Expr::If {
        then_branch,
        else_branch,
        ..
    } = value
    else {
        panic!("expected statementized If, got {value:?}")
    };
    // Inner Value tails feed the If result and remain unaugmented.
    assert_eq!(then_branch.tail, BlockTail::Value(lit_u64(7)));
    assert_eq!(else_branch.tail, BlockTail::Value(lit_u64(8)));
    assert_eq!(
        body.tail,
        BlockTail::Value(Expr::Tuple(vec![
            Expr::Var(result.clone()),
            Expr::Var(VarId::from("x")),
        ]))
    );
}

#[test]
fn block_result_statementization_preserves_tuple_arity_and_avoids_name_collisions() {
    let occupied = VarId::from("__mut_tail_result_0");
    let tuple = |number, flag| {
        Expr::Tuple(vec![
            lit_u64(number),
            Expr::Const(crate::ir::Const::Bool(flag)),
        ])
    };
    let if_expr = Expr::If {
        cond: Box::new(Expr::Var(occupied.clone())),
        then_branch: Box::new(block(Vec::new(), tail_value(tuple(7, true)))),
        else_branch: Box::new(block(Vec::new(), tail_value(tuple(8, false)))),
    };
    let f = func(
        "f",
        sig(
            vec![
                param(occupied.as_ref(), Type::Bool),
                param("x", mut_ref(Type::UInt(64), Type::UInt(64))),
            ],
            Type::Tuple(vec![Type::UInt(64), Type::Bool]),
        ),
        body(Vec::new(), if_expr),
        FuncOpts::default(),
    );
    let mut program = program_with(vec![(0, f)]);
    augment_signatures(&mut program).unwrap();
    augment_body_tails(&mut program).unwrap();

    let body = &program.functions[&0].body;
    let Stmt::Let { pattern, value } = &body.stmts[0] else {
        panic!("tuple-valued If must be statementized")
    };
    let expected_results = [
        VarId::from("__mut_tail_result_1"),
        VarId::from("__mut_tail_result_2"),
    ];
    assert_eq!(
        pattern,
        &expected_results
            .iter()
            .cloned()
            .map(Some)
            .collect::<Vec<_>>()
    );
    assert!(matches!(value, Expr::If { .. }));
    assert_eq!(
        body.tail,
        BlockTail::Value(Expr::Tuple(vec![
            Expr::Var(expected_results[0].clone()),
            Expr::Var(expected_results[1].clone()),
            Expr::Var(VarId::from("x")),
        ]))
    );
}

#[test]
fn idempotent_run_twice() {
    let f = func(
        "f",
        sig(
            vec![param("x", mut_ref(Type::UInt(64), Type::UInt(64)))],
            Type::Unit,
        ),
        body(vec![], Expr::Unit),
        FuncOpts::default(),
    );
    let mut program = program_with(vec![(0, f)]);
    augment_signatures(&mut program).unwrap();
    augment_body_tails(&mut program).unwrap();
    let after_once = program.clone();
    augment_body_tails(&mut program).unwrap();
    assert_eq!(program, after_once);
}

#[test]
fn match_arm_inner_return_augmented() {
    let arm0 = MatchArm {
        variant: 0,
        bindings: Vec::new(),
        body: Box::new(block(vec![], tail_return(lit_u64(1)))),
    };
    let match_expr = Expr::Match {
        struct_id: 0,
        selector: Box::new(Expr::Var(VarId::from("x"))),
        cases: vec![arm0],
    };
    let f = func(
        "f",
        sig(
            vec![param("x", mut_ref(Type::UInt(64), Type::UInt(64)))],
            Type::UInt(64),
        ),
        body(vec![Stmt::Eval(match_expr)], lit_u64(0)),
        FuncOpts::default(),
    );
    let mut program = program_with(vec![(0, f)]);
    augment_signatures(&mut program).unwrap();
    augment_body_tails(&mut program).unwrap();

    if let Stmt::Eval(Expr::Match { cases, .. }) = &program.functions[&0].body.stmts[0] {
        match &cases[0].body.tail {
            BlockTail::Return(value) => match value.as_ref() {
                Expr::Tuple(items) => {
                    assert_eq!(items.len(), 2);
                    assert_eq!(items[0], lit_u64(1));
                    assert_eq!(items[1], Expr::Var(VarId::from("x")));
                }
                other => panic!("expected Tuple, got {:?}", other),
            },
            other => panic!("expected Return tail, got {:?}", other),
        }
    } else {
        panic!("expected Match at body stmt 0");
    }
    let _ = just(Expr::Unit); // silence import lint
}

fn loop_expr(body: Block) -> Expr {
    Expr::While {
        header: Box::new(just(Expr::Unit)),
        cond: Box::new(Expr::Const(crate::ir::Const::Bool(true))),
        body: Box::new(body),
        iter_locals: Vec::new(),
        header_exit_locals: Vec::new(),
        live_out: Vec::new(),
    }
}

#[test]
fn loop_terminal_control_is_not_given_a_false_fallthrough() {
    // The outer loop body chooses either a nested loop followed by Continue,
    // or Break. Neither arm reaches a join. Replacing this terminal If with
    // `Eval(If); Value(Unit)` manufactures an implicit-continue edge; after
    // loop extraction that edge recursively invokes the outer loop with its
    // unchanged state and discards the nested-loop result.
    let nested_loop = loop_expr(Block {
        stmts: Vec::new(),
        tail: BlockTail::Break {
            level: 0,
            value: Box::new(Expr::Unit),
        },
    });
    let terminal = Expr::If {
        cond: Box::new(Expr::Const(crate::ir::Const::Bool(true))),
        then_branch: Box::new(Block {
            stmts: vec![Stmt::Eval(nested_loop)],
            tail: BlockTail::Continue {
                level: 0,
                value: Box::new(Expr::Unit),
            },
        }),
        else_branch: Box::new(Block {
            stmts: Vec::new(),
            tail: BlockTail::Break {
                level: 0,
                value: Box::new(Expr::Unit),
            },
        }),
    };
    let f = func(
        "f",
        sig(
            vec![param("x", mut_ref(Type::UInt(64), Type::UInt(64)))],
            Type::Unit,
        ),
        body(
            vec![Stmt::Eval(loop_expr(Block::just(terminal)))],
            Expr::Unit,
        ),
        FuncOpts::default(),
    );
    let mut program = program_with(vec![(0, f)]);
    augment_signatures(&mut program).unwrap();
    augment_body_tails(&mut program).unwrap();

    let Stmt::Eval(Expr::While { body, .. }) = &program.functions[&0].body.stmts[0] else {
        panic!("outer loop must remain in statement position")
    };
    assert!(body.stmts.is_empty());
    assert!(matches!(body.tail, BlockTail::Value(Expr::If { .. })));
}

#[test]
fn fallthrough_loop_control_is_still_statementized() {
    // A value-producing conditional does have a reachable join. Even in a
    // loop body it must stay in statement position for Stage 5 to merge state
    // written by either arm.
    let fallthrough = Expr::If {
        cond: Box::new(Expr::Const(crate::ir::Const::Bool(true))),
        then_branch: Box::new(just(Expr::Unit)),
        else_branch: Box::new(just(Expr::Unit)),
    };
    let f = func(
        "f",
        sig(
            vec![param("x", mut_ref(Type::UInt(64), Type::UInt(64)))],
            Type::Unit,
        ),
        body(
            vec![Stmt::Eval(loop_expr(Block::just(fallthrough)))],
            Expr::Unit,
        ),
        FuncOpts::default(),
    );
    let mut program = program_with(vec![(0, f)]);
    augment_signatures(&mut program).unwrap();
    augment_body_tails(&mut program).unwrap();

    let Stmt::Eval(Expr::While { body, .. }) = &program.functions[&0].body.stmts[0] else {
        panic!("outer loop must remain in statement position")
    };
    assert!(matches!(
        body.stmts.as_slice(),
        [Stmt::Eval(Expr::If { .. })]
    ));
    assert_eq!(body.tail, BlockTail::Value(Expr::Unit));
}
