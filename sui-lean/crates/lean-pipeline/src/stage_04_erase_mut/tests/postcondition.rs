//! Phase 2 fixtures for the stage-4 postcondition validator.
//!
//! One positive test (well-formed stage-4 output passes) and one
//! negative test per [`PostconditionError`] variant so future regressions
//! pin to the right error.

use crate::ir::{
    builder::{block, just, tail_value},
    Expr, QuantDomain, QuantifierKind, Stmt, Type, VarId,
};
use crate::stage_04_erase_mut::postcondition::{check, PostconditionError};
use crate::stage_04_erase_mut::run;

use super::fixtures::*;

const STRUCT_S: usize = 7;

// ---------------------------------------------------------------------------
// Positive: well-formed stage-4 output passes
// ---------------------------------------------------------------------------

#[test]
fn well_formed_stage_4_output_passes() {
    // f(x: T): T { x }
    let body_block = just(Expr::Var(VarId::from("x")));
    let p = param("x", Type::UInt(64));
    let f = func(
        "f",
        sig(vec![p], Type::UInt(64)),
        body_block,
        FuncOpts::default(),
    );
    let program = program_with(vec![(0, f)]);
    assert_eq!(check(&program), Ok(()));
}

#[test]
fn pattern_4b_well_formed_passes() {
    // borrow_field(x: T): &mut U { let r0 = &x; &r0.f0 }
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
        sig(vec![p], ret),
        body_block,
        FuncOpts::default(),
    );
    let program = program_with(vec![(0, f)]);
    assert_eq!(check(&program), Ok(()));
}

#[test]
fn native_function_skipped_even_with_mutref_signature() {
    // Obsolete: natives now live in program.natives.decls, not
    // program.functions; stages walk only functions, so this
    // behavior is structurally guaranteed.
}

// ---------------------------------------------------------------------------
// Negative cases -- one per error variant
// ---------------------------------------------------------------------------

#[test]
fn lingering_read_ref_rejects() {
    let stmts = vec![
        let_borrow_loc("r", "x"),
        Stmt::Let {
            pattern: vec![Some(VarId::from("v"))],
            value: Expr::ReadRef(Box::new(Expr::Var(VarId::from("r")))),
        },
    ];
    let tail = Expr::Var(VarId::from("v"));
    let p = param("x", Type::UInt(64));
    let f = func(
        "f",
        sig(vec![p], Type::UInt(64)),
        body(stmts, tail),
        FuncOpts::default(),
    );
    let program = program_with(vec![(0, f)]);
    assert_eq!(
        check(&program),
        Err(PostconditionError::LingeringReadRef { function: 0 })
    );
}

#[test]
fn rogue_borrow_loc_rejects() {
    // Non-pattern-4b function with a stray BorrowLoc binding.
    let stmts = vec![let_borrow_loc("r", "x")];
    let tail = Expr::Const(crate::ir::Const::UInt {
        bits: 64,
        value: ethnum::U256::from(0u64),
    });
    let p = param("x", Type::UInt(64));
    let f = func(
        "f",
        sig(vec![p], Type::UInt(64)),
        body(stmts, tail),
        FuncOpts::default(),
    );
    let program = program_with(vec![(0, f)]);
    assert_eq!(
        check(&program),
        Err(PostconditionError::RogueMutBorrow { function: 0 })
    );
}

#[test]
fn rogue_borrow_field_inside_if_rejects() {
    // BorrowField inside an If arm -- rogue.
    use crate::ir::builder::{block as mk_block, just as mk_just, tail_value as mk_tail_value};
    let then_branch = mk_block(
        vec![let_borrow_field(
            "r",
            STRUCT_S,
            0,
            Expr::Var(VarId::from("x")),
        )],
        mk_tail_value(Expr::Const(crate::ir::Const::UInt {
            bits: 64,
            value: ethnum::U256::from(0u64),
        })),
    );
    let else_branch = mk_just(Expr::Const(crate::ir::Const::UInt {
        bits: 64,
        value: ethnum::U256::from(0u64),
    }));
    let if_expr = Expr::If {
        cond: Box::new(Expr::Const(crate::ir::Const::Bool(true))),
        then_branch: Box::new(then_branch),
        else_branch: Box::new(else_branch),
    };
    let p = param("x", Type::UInt(64));
    let f = func(
        "f",
        sig(vec![p], Type::UInt(64)),
        mk_just(if_expr),
        FuncOpts::default(),
    );
    let program = program_with(vec![(0, f)]);
    assert_eq!(
        check(&program),
        Err(PostconditionError::RogueMutBorrow { function: 0 })
    );
}

#[test]
fn residual_mutable_ref_in_call_type_args_rejects() {
    let body_block = just(Expr::Call {
        fun: 99,
        type_args: vec![mut_ref(Type::UInt(64), Type::UInt(64))],
        args: vec![],
    });
    let f = func(
        "f",
        sig(vec![], Type::Unit),
        body_block,
        FuncOpts::default(),
    );
    let program = program_with(vec![(0, f)]);
    assert_eq!(
        check(&program),
        Err(PostconditionError::ResidualMutableRefInBody { function: 0 })
    );
}

#[test]
fn residual_mutable_ref_in_quantifier_binder_rejects() {
    let q = Expr::Quantifier {
        kind: QuantifierKind::Forall,
        binder: VarId::from("i"),
        binder_type: mut_ref(Type::UInt(64), Type::UInt(64)),
        domain: QuantDomain::Unbounded,
        body: Box::new(just(Expr::Const(crate::ir::Const::Bool(true)))),
    };
    let body_block = just(q);
    let f = func(
        "f",
        sig(vec![], Type::Bool),
        body_block,
        FuncOpts::default(),
    );
    let program = program_with(vec![(0, f)]);
    assert_eq!(
        check(&program),
        Err(PostconditionError::ResidualMutableRefInBody { function: 0 })
    );
}

#[test]
fn mutable_ref_in_non_pattern_4b_return_rejects() {
    // Tail is Var(p), not a BorrowLoc/BorrowField -- so NOT 4b.
    // Yet the signature still has MutableRef in the return slot.
    let body_block = just(Expr::Var(VarId::from("x")));
    let p = param("x", Type::UInt(64));
    let f = func(
        "f",
        sig(vec![p], mut_ref(Type::UInt(64), Type::UInt(64))),
        body_block,
        FuncOpts::default(),
    );
    let program = program_with(vec![(0, f)]);
    assert_eq!(
        check(&program),
        Err(PostconditionError::MutableRefInNonPattern4bReturn { function: 0 })
    );
}

#[test]
fn mutable_ref_in_param_rejects_even_if_pattern_4b() {
    // Pattern 4b is exempt only from the return-type check, not the
    // params check.  Stage 3 was supposed to strip mutref from
    // params; if it survives, stage 4 must reject.
    let body_block = just(Expr::BorrowLoc(VarId::from("x")));
    let p = param("x", mut_ref(Type::UInt(64), Type::UInt(64)));
    let ret = mut_ref(Type::UInt(64), Type::UInt(64));
    let f = func(
        "borrow_self",
        sig(vec![p], ret),
        body_block,
        FuncOpts::default(),
    );
    let program = program_with(vec![(0, f)]);
    assert_eq!(
        check(&program),
        Err(PostconditionError::MutableRefInNonPattern4bReturn { function: 0 })
    );
}

// ---------------------------------------------------------------------------
// End-to-end: run() + check() must agree
// ---------------------------------------------------------------------------

#[test]
fn full_run_then_check_passes_on_simple_function() {
    // f(x: u64): u64 { let r = &x; let v = *r; v }
    // stage 4's run() should leave: tail Var(v) wherev got the
    // Field-projection value.
    let stmts = vec![
        let_borrow_loc("r0", "x"),
        let_borrow_field("r1", STRUCT_S, 0, Expr::Var(VarId::from("r0"))),
        let_read_ref("v", "r1"),
    ];
    let tail = Expr::Var(VarId::from("v"));
    let p = param("x", Type::UInt(64));
    let f = func(
        "f",
        sig(vec![p], Type::UInt(64)),
        body(stmts, tail),
        FuncOpts::default(),
    );
    let mut program = program_with(vec![(0, f)]);
    run(&mut program).unwrap();
    assert_eq!(check(&program), Ok(()));
}
