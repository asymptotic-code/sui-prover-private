//! Phase 2 fixtures for pattern 4b survival.
//!
//! A pattern-4b function returns `&mut U` and its body's tail is a
//! `BorrowField` chain (NOT a `Var(p)` -- pattern 4a was demoted to
//! plain `T` by stage 3). Stage 4 must:
//!
//! - Preserve the `Expr::BorrowField` / `Expr::BorrowLoc` at the
//!   function's tail.
//! - Preserve the intermediate `Stmt::Let { value: BorrowLoc }` /
//!   `Stmt::Let { value: BorrowField }` bindings the tail references.
//! - Keep `Type::MutableRef` in the signature's return type.

use crate::ir::{
    builder::{block, tail_value},
    BlockTail, Expr, Stmt, Type, VarId,
};
use crate::stage_04_erase_mut::run;

use super::fixtures::*;

const STRUCT_S: usize = 7;

#[test]
fn pattern_4b_function_survives_full_pipeline() {
    // borrow_field(x: T): &mut U {
    //     let r0 = &x;
    //     &r0.f0   // tail BorrowField
    // }
    let body_block = block(
        vec![let_borrow_loc("r0", "x")],
        tail_value(Expr::Borrow {
            step: crate::ir::path::PathStep::Field {
                struct_id: STRUCT_S,
                field_index: 0,
            },
            base: Box::new(Expr::Var(VarId::from("r0"))),
        }),
    );
    let ret = mut_ref(Type::UInt(64), Type::UInt(64));
    let p = param("x", Type::UInt(64));
    let f = func(
        "borrow_field",
        sig(vec![p], ret.clone()),
        body_block,
        FuncOpts::default(),
    );
    let mut program = program_with(vec![(0, f)]);

    // Drive the full stage-4 pipeline.
    run(&mut program).expect("stage 4 should not fail");

    let func = &program.functions[&0];

    // 1. Return type still has MutableRef.
    assert_eq!(func.signature.return_type, ret);

    // 2. r0 binding survives.
    assert_eq!(func.body.stmts.len(), 1);
    match &func.body.stmts[0] {
        Stmt::Let { pattern, value } => {
            assert_eq!(pattern, &vec![Some(VarId::from("r0"))]);
            assert_eq!(value, &Expr::BorrowLoc(VarId::from("x")));
        }
        other => panic!("expected `let r0 = BorrowLoc(x)`, got {:?}", other),
    }

    // 3. Tail still has BorrowField.
    match &func.body.tail {
        BlockTail::Value(Expr::Borrow {
            step: crate::ir::path::PathStep::Field { .. },
            ..
        }) => {}
        other => panic!("expected tail BorrowField, got {:?}", other),
    }
}

#[test]
fn pattern_4b_with_borrow_loc_only_tail() {
    // borrow_self(x: T): &mut T { &x }
    let body_block = block(vec![], tail_value(Expr::BorrowLoc(VarId::from("x"))));
    let ret = mut_ref(Type::UInt(64), Type::UInt(64));
    let p = param("x", Type::UInt(64));
    let f = func(
        "borrow_self",
        sig(vec![p], ret.clone()),
        body_block,
        FuncOpts::default(),
    );
    let mut program = program_with(vec![(0, f)]);
    run(&mut program).expect("stage 4 should not fail");

    let func = &program.functions[&0];
    assert_eq!(func.signature.return_type, ret);
    assert!(func.body.stmts.is_empty());
    match &func.body.tail {
        BlockTail::Value(Expr::BorrowLoc(_)) => {}
        other => panic!("expected tail BorrowLoc, got {:?}", other),
    }
}

#[test]
fn non_pattern_4b_return_stripped() {
    // f(x: u64): &mut u64 { let v = 7; v }
    // Tail is Var(v), not a BorrowLoc/BorrowField -- so NOT pattern 4b.
    // Stage 4 strips MutableRef from the return type.
    let body_block = block(
        vec![Stmt::Let {
            pattern: vec![Some(VarId::from("v"))],
            value: Expr::Const(crate::ir::Const::UInt {
                bits: 64,
                value: ethnum::U256::from(7u64),
            }),
        }],
        tail_value(Expr::Var(VarId::from("v"))),
    );
    let ret = mut_ref(Type::UInt(64), Type::UInt(64));
    let p = param("x", Type::UInt(64));
    let f = func("f", sig(vec![p], ret), body_block, FuncOpts::default());
    let mut program = program_with(vec![(0, f)]);
    run(&mut program).expect("stage 4 should not fail");

    let func = &program.functions[&0];
    assert_eq!(func.signature.return_type, Type::UInt(64));
}
