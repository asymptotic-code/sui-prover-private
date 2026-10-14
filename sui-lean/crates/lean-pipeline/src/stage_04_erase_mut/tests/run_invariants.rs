//! Phase 2 fixtures for stage-4 run-level invariants:
//! idempotency, determinism, and the (stubbed) cross-stage
//! precondition handoff to stage 5.

use crate::ir::{Expr, Type, VarId};
use crate::stage_04_erase_mut::postcondition::check;
use crate::stage_04_erase_mut::run;

use super::fixtures::*;

const STRUCT_S: usize = 7;

/// Build a representative stage-3-output fixture: a function with
/// nested borrow chains and ReadRefs.
fn representative_fixture() -> crate::ir::Program {
    let stmts = vec![
        let_borrow_loc("r0", "x"),
        let_borrow_field("r1", STRUCT_S, 0, Expr::Var(VarId::from("r0"))),
        let_borrow_field("r2", STRUCT_S, 1, Expr::Var(VarId::from("r1"))),
        let_read_ref("v", "r2"),
    ];
    let tail = Expr::Var(VarId::from("v"));
    let p = param("x", Type::UInt(64));
    let f = func(
        "f",
        sig(vec![p], Type::UInt(64)),
        body(stmts, tail),
        FuncOpts::default(),
    );
    program_with(vec![(0, f)])
}

#[test]
fn idempotent_run_twice_is_noop_on_second_call() {
    let mut p = representative_fixture();
    run(&mut p).unwrap();
    let after_once = p.clone();
    run(&mut p).unwrap();
    assert_eq!(p, after_once, "second run must be a no-op");
}

#[test]
fn deterministic_byte_identical_output() {
    let mut a = representative_fixture();
    let mut b = representative_fixture();
    run(&mut a).unwrap();
    run(&mut b).unwrap();
    assert_eq!(a, b);
}

#[test]
fn postcondition_holds_after_run() {
    let mut p = representative_fixture();
    run(&mut p).unwrap();
    assert_eq!(check(&p), Ok(()));
}

/// Cross-stage handoff stub: stage 5 (SSA) doesn't exist as a
/// module yet. When it lands, `stage_05_ssa::preconditions::check`
/// will read from the post-stage-4 Program. For now, we assert that
/// stage 4's own postcondition acts as the implicit precondition.
/// When stage 5 starts, this test gets pointed at the real check.
#[test]
fn stage_05_preconditions_passes_after_stage_4() {
    let mut p = representative_fixture();
    run(&mut p).unwrap();

    // Stage 5 precondition stub: stage-4-clean output is a valid
    // input. The real check lands when stage 5 starts.
    let stage_5_precondition = check;
    assert_eq!(stage_5_precondition(&p), Ok(()));
}
