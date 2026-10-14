//! Phase 2 fixtures for Rewrite 2 (drop dead BorrowLoc / BorrowField).
//!
//! Each fixture builds a small body, runs `rewrite_read_refs` then
//! `drop_dead_borrows`, and asserts the dead `Stmt::Let`s are gone
//! while pattern-4b tail chains survive.

use crate::ir::{BlockTail, Expr, Stmt, Type, VarId};
use crate::stage_04_erase_mut::{drop_dead_borrows, rewrite_read_refs};

use super::fixtures::*;

const STRUCT_S: usize = 7;

fn one_fn_program(stmts: Vec<Stmt>, tail: Expr, ret: Type) -> crate::ir::Program {
    let p = param("x", Type::UInt(64));
    let f = func(
        "f",
        sig(vec![p], ret),
        body(stmts, tail),
        FuncOpts::default(),
    );
    program_with(vec![(0, f)])
}

fn body_stmts(program: &crate::ir::Program) -> &Vec<Stmt> {
    &program.functions[&0].body.stmts
}

#[test]
fn after_read_ref_substitution_borrow_chain_is_dead() {
    // let r0 = &x; let r1 = &r0.f0; let v = *r1; v
    // After Rewrite 1: ReadRef substituted. After Rewrite 2: r0, r1
    // bindings dropped.
    let stmts = vec![
        let_borrow_loc("r0", "x"),
        let_borrow_field("r1", STRUCT_S, 0, Expr::Var(VarId::from("r0"))),
        let_read_ref("v", "r1"),
    ];
    let tail = Expr::Var(VarId::from("v"));
    let mut program = one_fn_program(stmts, tail, Type::UInt(64));
    rewrite_read_refs(&mut program);
    drop_dead_borrows(&mut program);

    // Only `let v = ...` should remain.
    let stmts = body_stmts(&program);
    assert_eq!(stmts.len(), 1, "expected only `let v`, got {:#?}", stmts);
    match &stmts[0] {
        Stmt::Let { pattern, .. } => {
            assert_eq!(pattern, &vec![Some(VarId::from("v"))]);
        }
        other => panic!("expected Stmt::Let for v, got {:?}", other),
    }
}

#[test]
fn unused_borrow_loc_is_dropped() {
    // let r = &x; <no readers>; 0
    let stmts = vec![let_borrow_loc("r", "x")];
    let tail = Expr::Const(crate::ir::Const::UInt {
        bits: 64,
        value: ethnum::U256::from(0u64),
    });
    let mut program = one_fn_program(stmts, tail, Type::UInt(64));
    rewrite_read_refs(&mut program);
    drop_dead_borrows(&mut program);
    assert!(body_stmts(&program).is_empty());
}

#[test]
fn pattern_4b_tail_keeps_chain_alive() {
    // Pattern 4b: `borrow_field(x: T): &mut U` where the tail is a
    // BorrowField off a chain. Stage 4 must preserve the chain.
    // body:
    //   let r0 = &x;
    //   tail: BorrowField(r0, S, 0)   (the function's mutref return)
    let stmts = vec![let_borrow_loc("r0", "x")];
    let tail = Expr::Borrow {
        step: crate::ir::path::PathStep::Field {
            struct_id: STRUCT_S,
            field_index: 0,
        },
        base: Box::new(Expr::Var(VarId::from("r0"))),
    };
    let mut program = one_fn_program(stmts, tail, mut_ref(Type::UInt(64), Type::UInt(64)));
    rewrite_read_refs(&mut program);
    drop_dead_borrows(&mut program);

    // r0 must survive -- the tail's BorrowField references it.
    let stmts = body_stmts(&program);
    assert_eq!(stmts.len(), 1);
    match &stmts[0] {
        Stmt::Let { value, .. } => {
            assert_eq!(value, &Expr::BorrowLoc(VarId::from("x")));
        }
        other => panic!("expected BorrowLoc binding to survive, got {:?}", other),
    }
}

#[test]
fn nested_chain_dies_only_when_top_dies() {
    // let r0 = &x; let r1 = &r0.f0;  <only r1 read>
    // After Rewrite 1: ReadRef(r1) -> Field(STRUCT_S, 0, Var(x))
    // Both r0 and r1 should drop.
    let stmts = vec![
        let_borrow_loc("r0", "x"),
        let_borrow_field("r1", STRUCT_S, 0, Expr::Var(VarId::from("r0"))),
        let_read_ref("v", "r1"),
    ];
    let tail = Expr::Var(VarId::from("v"));
    let mut program = one_fn_program(stmts, tail, Type::UInt(64));
    rewrite_read_refs(&mut program);
    drop_dead_borrows(&mut program);
    let stmts = body_stmts(&program);
    assert_eq!(stmts.len(), 1, "expected only `let v`");
}

#[test]
fn drop_dead_inside_if_arm() {
    // if (cond) { let r0 = &x; let r1 = &r0.f0; *r1 } else { 0 }
    use crate::ir::builder::{block, just, tail_value};
    let stmts = vec![
        let_borrow_loc("r0", "x"),
        let_borrow_field("r1", STRUCT_S, 0, Expr::Var(VarId::from("r0"))),
    ];
    let then_branch = block(
        stmts,
        tail_value(Expr::ReadRef(Box::new(Expr::Var(VarId::from("r1"))))),
    );
    let else_branch = just(Expr::Const(crate::ir::Const::UInt {
        bits: 64,
        value: ethnum::U256::from(0u64),
    }));
    let if_expr = Expr::If {
        cond: Box::new(Expr::Const(crate::ir::Const::Bool(true))),
        then_branch: Box::new(then_branch),
        else_branch: Box::new(else_branch),
    };
    let mut program = one_fn_program(vec![], if_expr, Type::UInt(64));
    rewrite_read_refs(&mut program);
    drop_dead_borrows(&mut program);

    if let BlockTail::Value(Expr::If { then_branch, .. }) = &program.functions[&0].body.tail {
        assert!(
            then_branch.stmts.is_empty(),
            "expected then-arm stmts cleared"
        );
    } else {
        panic!("expected If at tail");
    }
}

#[test]
fn unrelated_let_is_preserved() {
    // let r = &x;  <r unused>
    // let y = 5;   <y in tail>
    // y
    let stmts = vec![
        let_borrow_loc("r", "x"),
        Stmt::Let {
            pattern: vec![Some(VarId::from("y"))],
            value: Expr::Const(crate::ir::Const::UInt {
                bits: 64,
                value: ethnum::U256::from(5u64),
            }),
        },
    ];
    let tail = Expr::Var(VarId::from("y"));
    let mut program = one_fn_program(stmts, tail, Type::UInt(64));
    rewrite_read_refs(&mut program);
    drop_dead_borrows(&mut program);

    let stmts = body_stmts(&program);
    assert_eq!(stmts.len(), 1, "expected only `let y` to survive");
    match &stmts[0] {
        Stmt::Let { pattern, .. } => {
            assert_eq!(pattern, &vec![Some(VarId::from("y"))]);
        }
        _ => panic!("expected Stmt::Let for y"),
    }
}

#[test]
fn drop_dead_idempotent() {
    let stmts = vec![
        let_borrow_loc("r0", "x"),
        let_borrow_field("r1", STRUCT_S, 0, Expr::Var(VarId::from("r0"))),
        let_read_ref("v", "r1"),
    ];
    let tail = Expr::Var(VarId::from("v"));
    let mut program = one_fn_program(stmts, tail, Type::UInt(64));
    rewrite_read_refs(&mut program);
    drop_dead_borrows(&mut program);
    let after_once = program.clone();
    drop_dead_borrows(&mut program);
    assert_eq!(program, after_once, "second run must be a no-op");
}

#[test]
fn drop_dead_skips_native_function() {
    let stmts = vec![let_borrow_loc("r", "x")];
    let tail = Expr::Var(VarId::from("r"));
    let p = param("x", Type::UInt(64));
    let f = func(
        "f",
        sig(vec![p], Type::UInt(64)),
        body(stmts, tail),
        FuncOpts {
            native: true,
            module: 0,
        },
    );
    let mut program = program_with(vec![(0, f)]);
    let before = program.clone();
    drop_dead_borrows(&mut program);
    assert_eq!(program, before, "native function body must be untouched");
}
