//! Full stage-3 pipeline tests: caller + callee together, all
//! transforms running, verifying the composed effect.

use crate::ir::builder::{block, tail_return, tail_value};
use crate::ir::{BlockTail, Expr, Stmt, Type, VarId};
use crate::stage_03_mut_to_let::postcondition::check;
use crate::stage_03_mut_to_let::run;

use super::fixtures::*;

#[test]
fn caller_and_callee_with_one_mut_each() {
    // callee: g(p: &mut u64): () { *p = 42 }
    let callee_body = vec![let_borrow_loc("r", "p"), eval_write_ref("r", lit_u64(42))];
    let callee = func(
        "g",
        sig(
            vec![param("p", mut_ref(Type::UInt(64), Type::UInt(64)))],
            Type::Unit,
        ),
        body(callee_body, Expr::Unit),
        FuncOpts::default(),
    );

    // caller: f(v: &mut u64) { g(v) }
    let caller_body = vec![Stmt::Eval(Expr::Call {
        fun: 1,
        type_args: Vec::new(),
        args: vec![Expr::Var(VarId::from("v"))],
    })];
    let caller = func(
        "f",
        sig(
            vec![param("v", mut_ref(Type::UInt(64), Type::UInt(64)))],
            Type::Unit,
        ),
        body(caller_body, Expr::Unit),
        FuncOpts::default(),
    );

    let mut program = program_with(vec![(0, caller), (1, callee)]);
    run(&mut program).unwrap();
    assert_eq!(check(&program), Ok(()));

    // Always-Tuple: callee signature return Tuple([Mutation u64])
    assert_eq!(
        program.functions[&1].signature.return_type,
        Type::Tuple(vec![mut_ref(Type::UInt(64), Type::UInt(64))])
    );
    // Callee body tail: Value(Tuple([Var(p)]))
    match &program.functions[&1].body.tail {
        BlockTail::Value(Expr::Tuple(items)) => {
            assert_eq!(items.len(), 1);
            assert_eq!(items[0], Expr::Var(VarId::from("p")));
        }
        other => panic!("callee tail wrong: {:?}", other),
    }
    // Verify callee body has the WriteRef position-shifted (no Stmt::Eval(WriteRef))
    for stmt in &program.functions[&1].body.stmts {
        if let Stmt::Eval(Expr::WriteRef { .. }) = stmt {
            panic!("expected WriteRef in Let position, got Stmt::Eval");
        }
    }

    // Always-Tuple: caller signature return Tuple([Mutation u64])
    assert_eq!(
        program.functions[&0].signature.return_type,
        Type::Tuple(vec![mut_ref(Type::UInt(64), Type::UInt(64))])
    );
    // Caller's call: Stmt::Let { pattern: [Some(v)], value: Call(g, [v]) }
    // (head_count = augmented_arity 1 - muts.len() 1 = 0, so no leading None)
    match &program.functions[&0].body.stmts[0] {
        Stmt::Let { pattern, .. } => {
            assert_eq!(pattern, &vec![Some(VarId::from("v"))]);
        }
        other => panic!("expected augmented Stmt::Let, got {:?}", other),
    }
    // Caller body tail: Value(Tuple([Var(v)]))
    match &program.functions[&0].body.tail {
        BlockTail::Value(Expr::Tuple(items)) => {
            assert_eq!(items.len(), 1);
            assert_eq!(items[0], Expr::Var(VarId::from("v")));
        }
        other => panic!("caller tail wrong: {:?}", other),
    }
}

#[test]
fn caller_captures_return_value_and_mut_state() {
    // callee: g(p: &mut u64): u64 { 42 }
    let callee = func(
        "g",
        sig(
            vec![param("p", mut_ref(Type::UInt(64), Type::UInt(64)))],
            Type::UInt(64),
        ),
        body(vec![], lit_u64(42)),
        FuncOpts::default(),
    );

    // caller: f(v: &mut u64): u64 { let r = g(v); r }
    let caller_body = vec![Stmt::Let {
        pattern: vec![Some(VarId::from("r"))],
        value: Expr::Call {
            fun: 1,
            type_args: Vec::new(),
            args: vec![Expr::Var(VarId::from("v"))],
        },
    }];
    let caller = func(
        "f",
        sig(
            vec![param("v", mut_ref(Type::UInt(64), Type::UInt(64)))],
            Type::UInt(64),
        ),
        body(caller_body, Expr::Var(VarId::from("r"))),
        FuncOpts::default(),
    );

    let mut program = program_with(vec![(0, caller), (1, callee)]);
    run(&mut program).unwrap();
    assert_eq!(check(&program), Ok(()));

    // Verify the augmentation:
    // Caller signature.return_type: Tuple([u64, mut_ref])
    let expected_ret = Type::Tuple(vec![
        Type::UInt(64),
        mut_ref(Type::UInt(64), Type::UInt(64)),
    ]);
    assert_eq!(program.functions[&0].signature.return_type, expected_ret);

    // Caller's call stmt pattern: [Some(r), Some(v)]
    match &program.functions[&0].body.stmts[0] {
        Stmt::Let { pattern, .. } => {
            assert_eq!(pattern.len(), 2);
            assert_eq!(pattern[0], Some(VarId::from("r")));
            assert_eq!(pattern[1], Some(VarId::from("v")));
        }
        other => panic!("expected augmented Stmt::Let, got {:?}", other),
    }

    // Caller's body tail: Value(Tuple([Var(r), Var(v)]))
    match &program.functions[&0].body.tail {
        BlockTail::Value(Expr::Tuple(items)) => {
            assert_eq!(items.len(), 2);
            assert_eq!(items[0], Expr::Var(VarId::from("r")));
            assert_eq!(items[1], Expr::Var(VarId::from("v")));
        }
        other => panic!("caller tail wrong: {:?}", other),
    }
}

#[test]
fn pattern_4a_self_return_augments_correctly() {
    // Pattern 4a: callee returns its &mut input directly.
    // Without the always-Tuple invariant, the original (single mut_ref_type)
    // return would be indistinguishable from the augmented form and
    // signatures.rs would skip augmentation. Always-Tuple fixes this:
    // augmented form is always Tuple([_, _]) -- arity 2.
    let callee = func(
        "id",
        sig(
            vec![param("x", mut_ref(Type::UInt(64), Type::UInt(64)))],
            mut_ref(Type::UInt(64), Type::UInt(64)),
        ),
        body(vec![], Expr::Var(VarId::from("x"))),
        FuncOpts::default(),
    );
    let caller_body = vec![Stmt::Let {
        pattern: vec![Some(VarId::from("r"))],
        value: Expr::Call {
            fun: 1,
            type_args: Vec::new(),
            args: vec![Expr::Var(VarId::from("y"))],
        },
    }];
    let caller = func(
        "caller",
        sig(
            vec![param("y", mut_ref(Type::UInt(64), Type::UInt(64)))],
            Type::Unit,
        ),
        body(caller_body, Expr::Unit),
        FuncOpts::default(),
    );

    let mut program = program_with(vec![(0, caller), (1, callee)]);
    run(&mut program).unwrap();
    assert_eq!(check(&program), Ok(()));

    // Callee signature: Tuple([&mut T, &mut T]) (arity 2 = original + mut).
    let expected_callee_ret = Type::Tuple(vec![
        mut_ref(Type::UInt(64), Type::UInt(64)),
        mut_ref(Type::UInt(64), Type::UInt(64)),
    ]);
    assert_eq!(
        program.functions[&1].signature.return_type,
        expected_callee_ret
    );

    // Callee body tail: Tuple([Var(x), Var(x)]).
    match &program.functions[&1].body.tail {
        BlockTail::Value(Expr::Tuple(items)) => {
            assert_eq!(items.len(), 2);
            assert_eq!(items[0], Expr::Var(VarId::from("x")));
            assert_eq!(items[1], Expr::Var(VarId::from("x")));
        }
        other => panic!("callee tail wrong: {:?}", other),
    }

    // Caller's call: pattern [Some(r), Some(y)] (arity 2 matching augmented sig).
    match &program.functions[&0].body.stmts[0] {
        Stmt::Let { pattern, .. } => {
            assert_eq!(pattern.len(), 2);
            assert_eq!(pattern[0], Some(VarId::from("r")));
            assert_eq!(pattern[1], Some(VarId::from("y")));
        }
        other => panic!("expected augmented Stmt::Let, got {:?}", other),
    }
}

#[test]
fn stmt_eval_call_to_non_unit_returning_mut_callee() {
    // Stmt::Eval(Call(g)) where g returns u64 + has &mut p:
    // augmented sig = Tuple([u64, Mutation T]), arity 2.
    // Caller's pattern after augmentation needs head_count=1 None slots
    // to match arity 2. Previously call_augment emitted arity-1 pattern,
    // a silent IR inconsistency.
    let callee = func(
        "g",
        sig(
            vec![param("p", mut_ref(Type::UInt(64), Type::UInt(64)))],
            Type::UInt(64),
        ),
        body(vec![], lit_u64(42)),
        FuncOpts::default(),
    );
    let caller_body = vec![Stmt::Eval(Expr::Call {
        fun: 1,
        type_args: Vec::new(),
        args: vec![Expr::Var(VarId::from("v"))],
    })];
    let caller = func(
        "f",
        sig(
            vec![param("v", mut_ref(Type::UInt(64), Type::UInt(64)))],
            Type::Unit,
        ),
        body(caller_body, Expr::Unit),
        FuncOpts::default(),
    );

    let mut program = program_with(vec![(0, caller), (1, callee)]);
    run(&mut program).unwrap();
    assert_eq!(check(&program), Ok(()));

    // Caller's call: pattern [None, Some(v)] (arity 2 matching augmented sig).
    match &program.functions[&0].body.stmts[0] {
        Stmt::Let { pattern, .. } => {
            assert_eq!(pattern.len(), 2);
            assert_eq!(pattern[0], None);
            assert_eq!(pattern[1], Some(VarId::from("v")));
        }
        other => panic!(
            "expected augmented Stmt::Let with None head, got {:?}",
            other
        ),
    }
}

#[test]
fn native_callee_non_unit_return_with_mut_gets_head_slot() {
    // Native callees get their IR signature augmented uniformly
    // (Tuple([orig_ret, mut_ref_types...])). Call-site augmentation
    // computes head_count from the signature's arity directly --
    // for a native pop_back-shape callee (UInt(64) return + 1 &mut),
    // the augmented signature is Tuple([UInt(64), MutableRef<UInt(64)>])
    // (arity 2). `Stmt::Eval(Call)` produces a 2-slot pattern:
    // [None, Some(v)] (the original return is discarded, the mut
    // arg's post-call state is bound back to v).
    let callee = func(
        "pop_back",
        sig(
            vec![param("v", mut_ref(Type::UInt(64), Type::UInt(64)))],
            Type::UInt(64),
        ),
        empty_body(),
        FuncOpts {
            native: true,
            module: 0,
        },
    );
    let caller_body = vec![Stmt::Eval(Expr::Call {
        fun: 1,
        type_args: Vec::new(),
        args: vec![Expr::Var(VarId::from("v"))],
    })];
    let caller = func(
        "f",
        sig(
            vec![param("v", mut_ref(Type::UInt(64), Type::UInt(64)))],
            Type::Unit,
        ),
        body(caller_body, Expr::Unit),
        FuncOpts::default(),
    );
    let mut program = program_with(vec![(0, caller), (1, callee)]);
    run(&mut program).unwrap();
    assert_eq!(check(&program), Ok(()));

    // Native callee's IR signature is now augmented: UInt(64) + 1 &mut
    // -> Tuple([UInt(64), MutableRef<UInt(64), UInt(64)>]).
    assert_eq!(
        program.functions[&1].signature.return_type,
        Type::Tuple(vec![
            Type::UInt(64),
            mut_ref(Type::UInt(64), Type::UInt(64))
        ])
    );
    // Caller's pattern: [None, Some(v)] (arity 2 = augmented arity).
    match &program.functions[&0].body.stmts[0] {
        Stmt::Let { pattern, .. } => {
            assert_eq!(
                pattern.len(),
                2,
                "native callee with non-Unit return + mut needs head None slot"
            );
            assert_eq!(pattern[0], None);
            assert_eq!(pattern[1], Some(VarId::from("v")));
        }
        other => panic!("expected augmented Stmt::Let, got {:?}", other),
    }
}

#[test]
fn full_run_is_idempotent() {
    let callee = func(
        "g",
        sig(
            vec![param("p", mut_ref(Type::UInt(64), Type::UInt(64)))],
            Type::Unit,
        ),
        body(vec![], Expr::Unit),
        FuncOpts::default(),
    );
    let caller_body = vec![Stmt::Eval(Expr::Call {
        fun: 1,
        type_args: Vec::new(),
        args: vec![Expr::Var(VarId::from("v"))],
    })];
    let caller = func(
        "f",
        sig(
            vec![param("v", mut_ref(Type::UInt(64), Type::UInt(64)))],
            Type::Unit,
        ),
        body(caller_body, Expr::Unit),
        FuncOpts::default(),
    );
    let mut program = program_with(vec![(0, caller), (1, callee)]);
    run(&mut program).unwrap();
    let after_once = program.clone();
    run(&mut program).unwrap();
    assert_eq!(program, after_once);
}

#[test]
fn multi_muts_of_same_type() {
    // fn f(x: &mut T, y: &mut T): () { }  (Unit return, 2 muts same type)
    let f = func(
        "f",
        sig(
            vec![
                param("x", mut_ref(Type::UInt(64), Type::UInt(64))),
                param("y", mut_ref(Type::UInt(64), Type::UInt(64))),
            ],
            Type::Unit,
        ),
        body(vec![], Expr::Unit),
        FuncOpts::default(),
    );
    let mut program = program_with(vec![(0, f)]);
    run(&mut program).unwrap();
    assert_eq!(check(&program), Ok(()));

    // Sig: Tuple([&mut T, &mut T])
    assert_eq!(
        program.functions[&0].signature.return_type,
        Type::Tuple(vec![
            mut_ref(Type::UInt(64), Type::UInt(64)),
            mut_ref(Type::UInt(64), Type::UInt(64)),
        ])
    );
    // Body tail: Tuple([Var(x), Var(y)])
    match &program.functions[&0].body.tail {
        BlockTail::Value(Expr::Tuple(items)) => {
            assert_eq!(items.len(), 2);
            assert_eq!(items[0], Expr::Var(VarId::from("x")));
            assert_eq!(items[1], Expr::Var(VarId::from("y")));
        }
        other => panic!("unexpected: {:?}", other),
    }
}

#[test]
fn pattern_4b_sub_field_return() {
    // fn field(s: &mut S): &mut U { let r0 = &s; ... }
    // Simplified: body tail is BorrowField off the mut param
    // Sig augments to Tuple([&mut U, &mut S]).
    let body_block = body(
        vec![],
        Expr::Borrow {
            step: crate::ir::path::PathStep::Field {
                struct_id: 7,
                field_index: 0,
            },
            base: Box::new(Expr::Var(VarId::from("s"))),
        },
    );
    let f = func(
        "field",
        sig(
            vec![param("s", mut_ref(Type::UInt(64), Type::UInt(64)))],
            mut_ref(Type::Bool, Type::UInt(64)), // returns &mut U where U=Bool
        ),
        body_block,
        FuncOpts::default(),
    );
    let mut program = program_with(vec![(0, f)]);
    run(&mut program).unwrap();
    assert_eq!(check(&program), Ok(()));

    // Sig: Tuple([&mut Bool, &mut UInt(64)])
    assert_eq!(
        program.functions[&0].signature.return_type,
        Type::Tuple(vec![
            mut_ref(Type::Bool, Type::UInt(64)),
            mut_ref(Type::UInt(64), Type::UInt(64)),
        ])
    );
    // Body tail: Tuple([BorrowField(...), Var(s)])
    match &program.functions[&0].body.tail {
        BlockTail::Value(Expr::Tuple(items)) => {
            assert_eq!(items.len(), 2);
            assert!(matches!(
                items[0],
                Expr::Borrow {
                    step: crate::ir::path::PathStep::Field { .. },
                    ..
                }
            ));
            assert_eq!(items[1], Expr::Var(VarId::from("s")));
        }
        other => panic!("unexpected: {:?}", other),
    }
}

#[test]
fn recursive_function_with_mut_param() {
    // fn f(x: &mut T): u64 { let r = f(x); r }
    // Stage 2 lifts the recursive call into a Stmt::Let. Stage 3 then
    // destructures the augmented return and rebinds x.
    let f_body = vec![Stmt::Let {
        pattern: vec![Some(VarId::from("r"))],
        value: Expr::Call {
            fun: 0, // self-reference
            type_args: Vec::new(),
            args: vec![Expr::Var(VarId::from("x"))],
        },
    }];
    let f = func(
        "f",
        sig(
            vec![param("x", mut_ref(Type::UInt(64), Type::UInt(64)))],
            Type::UInt(64),
        ),
        body(f_body, Expr::Var(VarId::from("r"))),
        FuncOpts::default(),
    );
    let mut program = program_with(vec![(0, f)]);
    run(&mut program).unwrap();
    assert_eq!(check(&program), Ok(()));

    // Recursive Stmt::Let pattern: [Some(r), Some(x)] (arity 2 matching augmented sig)
    match &program.functions[&0].body.stmts[0] {
        Stmt::Let { pattern, .. } => {
            assert_eq!(pattern.len(), 2);
            assert_eq!(pattern[0], Some(VarId::from("r")));
            assert_eq!(pattern[1], Some(VarId::from("x")));
        }
        other => panic!("unexpected: {:?}", other),
    }
    // Body tail: Tuple([Var(r), Var(x)])
    match &program.functions[&0].body.tail {
        BlockTail::Value(Expr::Tuple(items)) => {
            assert_eq!(items.len(), 2);
            assert_eq!(items[0], Expr::Var(VarId::from("r")));
            assert_eq!(items[1], Expr::Var(VarId::from("x")));
        }
        other => panic!("unexpected: {:?}", other),
    }
}

#[test]
fn return_inside_if_at_function_tail_position() {
    // fn f(x: &mut T): u64 {
    //   if (c) { return 5 } else { 7 }
    // }
    // The function's top-level tail IS the if-expression. The
    // then-arm has Return(5); the else-arm has Value(7). body_tail
    // must augment BOTH paths.
    let then_arm = block(vec![], tail_return(lit_u64(5)));
    let else_arm = block(vec![], tail_value(lit_u64(7)));
    let if_expr = Expr::If {
        cond: Box::new(Expr::Const(crate::ir::Const::Bool(true))),
        then_branch: Box::new(then_arm),
        else_branch: Box::new(else_arm),
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
    run(&mut program).unwrap();

    // The If is evaluated into a fresh result binder. Keeping it in
    // statement position lets Stage 5 join mutable state changed by either
    // arm before the function returns `(result, x)`.
    let body = &program.functions[&0].body;
    let Stmt::Let { pattern, value } = &body.stmts[0] else {
        panic!("expected statementized tail If")
    };
    let [Some(result)] = &pattern[..] else {
        panic!("scalar tail If must bind exactly one result: {pattern:?}")
    };
    assert_eq!(result, &VarId::from("__mut_tail_result_0"));
    assert_eq!(
        body.tail,
        BlockTail::Value(Expr::Tuple(vec![
            Expr::Var(result.clone()),
            Expr::Var(VarId::from("x")),
        ]))
    );

    // The If's then-arm Return MUST also be augmented to Tuple([5, Var(x)]).
    match value {
        Expr::If {
            then_branch,
            else_branch,
            ..
        } => {
            match &then_branch.tail {
                BlockTail::Return(value) => match value.as_ref() {
                    Expr::Tuple(items) => {
                        assert_eq!(items.len(), 2, "Return inside arm must be augmented");
                        assert_eq!(items[0], lit_u64(5));
                        assert_eq!(items[1], Expr::Var(VarId::from("x")));
                    }
                    other => panic!("then-arm Return must be augmented Tuple, got {:?}", other),
                },
                other => panic!("then-arm tail must be Return, got {:?}", other),
            }
            // else-arm tail is Value(7) -- NOT augmented (inner non-Return tail).
            match &else_branch.tail {
                BlockTail::Value(v) => assert_eq!(v, &lit_u64(7)),
                other => panic!("else-arm tail mismatch: {:?}", other),
            }
        }
        other => panic!("expected statementized If, got {:?}", other),
    }
}

#[test]
fn stage_five_joins_mutable_state_rebound_in_one_statementized_tail_arm() {
    let then_arm = block(
        vec![Stmt::Eval(Expr::WriteRef {
            reference: Box::new(Expr::Var(VarId::from("x"))),
            value: Box::new(lit_u64(42)),
        })],
        tail_value(lit_u64(1)),
    );
    let else_arm = block(Vec::new(), tail_value(lit_u64(2)));
    let tail_if = Expr::If {
        cond: Box::new(Expr::Var(VarId::from("choose"))),
        then_branch: Box::new(then_arm),
        else_branch: Box::new(else_arm),
    };
    let f = func(
        "f",
        sig(
            vec![
                param("choose", Type::Bool),
                param("x", mut_ref(Type::UInt(64), Type::UInt(64))),
            ],
            Type::UInt(64),
        ),
        body(Vec::new(), tail_if),
        FuncOpts::default(),
    );
    let mut program = program_with(vec![(0, f)]);

    run(&mut program).unwrap();
    crate::stage_05_ssa::run(&mut program).unwrap();
    crate::ir::validate::validate_program(&program).unwrap();

    let body = &program.functions[&0].body;
    let Stmt::Let { pattern, value } = &body.stmts[0] else {
        panic!("Stage 5 must bind the tail If result and joined mutable state")
    };
    let [Some(result), Some(joined_state)] = &pattern[..] else {
        panic!("tail If must return its scalar result and one mutable-state phi: {pattern:?}")
    };
    assert!(result.as_ref().starts_with("__mut_tail_result_0_"));
    assert!(joined_state.as_ref().starts_with("x_"));

    let Expr::If {
        then_branch,
        else_branch,
        ..
    } = value
    else {
        panic!("expected statementized If, got {value:?}")
    };
    let BlockTail::Value(Expr::Tuple(then_values)) = &then_branch.tail else {
        panic!("mutating arm must return result plus updated state")
    };
    let BlockTail::Value(Expr::Tuple(else_values)) = &else_branch.tail else {
        panic!("pass-through arm must return result plus incoming state")
    };
    assert_eq!(then_values.len(), 2);
    assert_eq!(else_values.len(), 2);
    assert_eq!(then_values[0], lit_u64(1));
    assert_eq!(else_values[0], lit_u64(2));
    assert!(matches!(&then_values[1], Expr::Var(var) if var.as_ref().starts_with("x_")));
    assert!(matches!(&else_values[1], Expr::Var(var) if var.as_ref().starts_with("x_")));
    assert_ne!(then_values[1], else_values[1]);
    assert_eq!(
        body.tail,
        BlockTail::Value(Expr::Tuple(vec![
            Expr::Var(result.clone()),
            Expr::Var(joined_state.clone()),
        ]))
    );
}

#[test]
fn stage_five_propagates_mutable_state_from_nested_value_tail_if() {
    // The inner If is initially buried in an outer arm's Value tail. Stage 3
    // must put it in statement position before Stage 5 processes the outer If;
    // otherwise the inner x rebind is restored with the subexpression scope
    // and never reaches the outer join.
    let inner_if = Expr::If {
        cond: Box::new(Expr::Var(VarId::from("inner"))),
        then_branch: Box::new(block(
            vec![Stmt::Eval(Expr::WriteRef {
                reference: Box::new(Expr::Var(VarId::from("x"))),
                value: Box::new(lit_u64(42)),
            })],
            tail_value(lit_u64(1)),
        )),
        else_branch: Box::new(block(Vec::new(), tail_value(lit_u64(2)))),
    };
    let outer_if = Expr::If {
        cond: Box::new(Expr::Var(VarId::from("outer"))),
        then_branch: Box::new(block(Vec::new(), tail_value(inner_if))),
        else_branch: Box::new(block(Vec::new(), tail_value(lit_u64(3)))),
    };
    let f = func(
        "f",
        sig(
            vec![
                param("outer", Type::Bool),
                param("inner", Type::Bool),
                param("x", mut_ref(Type::UInt(64), Type::UInt(64))),
            ],
            Type::UInt(64),
        ),
        body(
            vec![Stmt::Let {
                pattern: vec![Some(VarId::from("result"))],
                value: outer_if,
            }],
            Expr::Var(VarId::from("result")),
        ),
        FuncOpts::default(),
    );
    let mut program = program_with(vec![(0, f)]);

    run(&mut program).unwrap();

    // Bottom-up ANF: the nested control is now a statement in the outer arm,
    // and that statement's binder is the outer arm's value.
    let body = &program.functions[&0].body;
    let Stmt::Let {
        value: Expr::If {
            then_branch: outer_then,
            ..
        },
        ..
    } = &body.stmts[0]
    else {
        panic!("expected the original outer scalar Let")
    };
    let Stmt::Let {
        pattern: inner_pattern,
        value: Expr::If { .. },
    } = outer_then.stmts.last().expect("statementized nested If")
    else {
        panic!("nested tail If must be moved to statement position")
    };
    let [Some(inner_result)] = &inner_pattern[..] else {
        panic!("nested scalar If must have one result binder: {inner_pattern:?}")
    };
    assert_eq!(
        outer_then.tail,
        BlockTail::Value(Expr::Var(inner_result.clone()))
    );

    crate::stage_05_ssa::run(&mut program).unwrap();
    crate::ir::validate::validate_program(&program).unwrap();

    let body = &program.functions[&0].body;
    let Stmt::Let {
        pattern: outer_pattern,
        value:
            Expr::If {
                then_branch: outer_then,
                else_branch: outer_else,
                ..
            },
    } = &body.stmts[0]
    else {
        panic!("expected outer If with a result and mutable-state join")
    };
    let [Some(outer_result), Some(outer_state)] = &outer_pattern[..] else {
        panic!("outer If must join its scalar result and x: {outer_pattern:?}")
    };

    let Stmt::Let {
        pattern: inner_pattern,
        value:
            Expr::If {
                then_branch: inner_then,
                else_branch: inner_else,
                ..
            },
    } = outer_then.stmts.last().expect("nested If join")
    else {
        panic!("expected nested If with its own mutable-state join")
    };
    let [Some(inner_result), Some(inner_state)] = &inner_pattern[..] else {
        panic!("nested If must join its scalar result and x: {inner_pattern:?}")
    };

    let BlockTail::Value(Expr::Tuple(inner_then_values)) = &inner_then.tail else {
        panic!("mutating inner arm must return its result and updated x")
    };
    let BlockTail::Value(Expr::Tuple(inner_else_values)) = &inner_else.tail else {
        panic!("pass-through inner arm must return its result and incoming x")
    };
    assert_eq!(inner_then_values.len(), 2);
    assert_eq!(inner_else_values.len(), 2);
    assert_eq!(inner_then_values[0], lit_u64(1));
    assert_eq!(inner_else_values[0], lit_u64(2));
    assert_ne!(inner_then_values[1], inner_else_values[1]);

    let BlockTail::Value(Expr::Tuple(outer_then_values)) = &outer_then.tail else {
        panic!("outer mutating arm must publish the nested result and state")
    };
    let BlockTail::Value(Expr::Tuple(outer_else_values)) = &outer_else.tail else {
        panic!("outer pass-through arm must publish its result and state")
    };
    assert_eq!(
        outer_then_values,
        &vec![
            Expr::Var(inner_result.clone()),
            Expr::Var(inner_state.clone()),
        ]
    );
    assert_eq!(outer_else_values.len(), 2);
    assert_eq!(outer_else_values[0], lit_u64(3));
    assert_ne!(outer_then_values[1], outer_else_values[1]);

    assert_eq!(
        body.tail,
        BlockTail::Value(Expr::Tuple(vec![
            Expr::Var(outer_result.clone()),
            Expr::Var(outer_state.clone()),
        ]))
    );
}

#[test]
fn return_inside_if_inside_stmt_let_value() {
    // fn f(x: &mut T): u64 { let v = if (c) { return 5 } else { 7 }; v }
    let then_arm = block(vec![], tail_return(lit_u64(5)));
    let else_arm = block(vec![], tail_value(lit_u64(7)));
    let if_expr = Expr::If {
        cond: Box::new(Expr::Const(crate::ir::Const::Bool(true))),
        then_branch: Box::new(then_arm),
        else_branch: Box::new(else_arm),
    };
    let f_body = vec![Stmt::Let {
        pattern: vec![Some(VarId::from("v"))],
        value: if_expr,
    }];
    let f = func(
        "f",
        sig(
            vec![param("x", mut_ref(Type::UInt(64), Type::UInt(64)))],
            Type::UInt(64),
        ),
        body(f_body, Expr::Var(VarId::from("v"))),
        FuncOpts::default(),
    );
    let mut program = program_with(vec![(0, f)]);
    run(&mut program).unwrap();

    // The Stmt::Let's value If's then-arm Return MUST be augmented.
    match &program.functions[&0].body.stmts[0] {
        Stmt::Let { pattern, value } => {
            assert_eq!(pattern, &vec![Some(VarId::from("v"))]);
            match value {
                Expr::If { then_branch, .. } => match &then_branch.tail {
                    BlockTail::Return(rv) => match rv.as_ref() {
                        Expr::Tuple(items) => {
                            assert_eq!(items.len(), 2);
                            assert_eq!(items[0], lit_u64(5));
                            assert_eq!(items[1], Expr::Var(VarId::from("x")));
                        }
                        other => panic!("Return must be augmented Tuple, got {:?}", other),
                    },
                    other => panic!("expected Return tail, got {:?}", other),
                },
                other => panic!("expected If, got {:?}", other),
            }
        }
        other => panic!("expected Stmt::Let, got {:?}", other),
    }
}
