//! Stage-3 (mut-to-let) run-level invariants: idempotency, determinism,
//! and the (stubbed) handoff to stage 5.

use crate::ir::{BorrowEdge, BorrowNode, Expr, Type, VarId};
use crate::stage_03_mut_to_let::postcondition::check;
use crate::stage_03_mut_to_let::run;

use super::fixtures::*;

const STRUCT_S: usize = 7;

fn representative_fixture() -> crate::ir::Program {
    // let r0 = &x; let r1 = &r0.f0; *r1 = 5; <writeback chain at r1, r0>
    let stmts = vec![
        let_borrow_loc("r0", "x"),
        let_borrow_field("r1", STRUCT_S, 0, Expr::Var(VarId::from("r0"))),
        eval_write_ref("r1", lit_u64(5)),
        eval_write_back(
            BorrowNode::Reference(VarId::from("r0")),
            BorrowEdge::StructField {
                struct_id: STRUCT_S,
                field_index: 0,
            },
            "r1",
        ),
        eval_write_back(
            BorrowNode::LocalRoot(VarId::from("x")),
            BorrowEdge::Direct,
            "r0",
        ),
    ];
    one_fn_program(
        stmts,
        Expr::Unit,
        vec![param("x", Type::UInt(64))],
        Type::Unit,
    )
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

#[test]
fn stage_05_preconditions_passes_after_stage_3() {
    // Stub: stage 5 (SSA) doesn't have a real precondition check
    // yet; stage 3's own postcondition is the implicit precondition.
    // When stage 5 lands, re-point this test at the real check.
    let mut p = representative_fixture();
    run(&mut p).unwrap();
    let stage_5_precondition = check;
    assert_eq!(stage_5_precondition(&p), Ok(()));
}
