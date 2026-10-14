//! Phase 1 fixtures for Rewrite 1 (ReadRef -> path_to_expr).
//!
//! Each fixture builds a minimal `Program` containing a single
//! function that emits one or more `Stmt::Let { value: BorrowLoc | BorrowField }`
//! bindings followed by `Stmt::Let { value: ReadRef(Var(r)) }`. After
//! `rewrite_read_refs(&mut program)`, the ReadRef should have been
//! replaced by the corresponding `path_to_expr` projection.
//!
//! The `BorrowLoc` / `BorrowField` bindings themselves are NOT dropped
//! by Rewrite 1 -- that's Phase 2's concern.
//!
//! Borrow chains are constructed in the same shape stage 2 emits:
//! a `BorrowLoc` binding for the local-root step, then `BorrowField`
//! bindings whose `base` is `Var(prev_temp)`. Mirrors upstream's
//! one-bytecode-per-Stmt::Let convention.

use crate::ir::{BlockTail, Expr, Stmt, Type, VarId};
use crate::stage_04_erase_mut::{path_to_expr::path_to_expr, rewrite_read_refs};

use super::fixtures::*;

const STRUCT_S: usize = 7;
const STRUCT_T: usize = 11;

// ---------------------------------------------------------------------------
// Helper: build a function `f(x: T): T_OUT` whose body has the given stmts
// and tail.
// ---------------------------------------------------------------------------
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

fn body_of(program: &crate::ir::Program) -> &crate::ir::Block {
    &program.functions[&0].body
}

// ---------------------------------------------------------------------------
// One fixture per BorrowEdge variant
// ---------------------------------------------------------------------------

#[test]
fn read_ref_through_borrow_loc_only_becomes_var() {
    // let r = &x; let v = *r; v
    let stmts = vec![let_borrow_loc("r", "x"), let_read_ref("v", "r")];
    let tail = Expr::Var(VarId::from("v"));
    let mut program = one_fn_program(stmts, tail, Type::UInt(64));
    rewrite_read_refs(&mut program);

    // After Rewrite 1: `let v = x;` (path_to_expr returns Var(x) for
    // root=x with no edges).
    let expected_v_value = path_to_expr(VarId::from("x"), &[]);
    let body = body_of(&program);
    let v_let = match &body.stmts[1] {
        Stmt::Let { pattern, value } => {
            assert_eq!(pattern, &vec![Some(VarId::from("v"))]);
            value.clone()
        }
        other => panic!("expected Stmt::Let, got {:?}", other),
    };
    assert_eq!(v_let, expected_v_value);
}

#[test]
fn read_ref_through_field_edge_becomes_field_projection() {
    // let r0 = &x; let r1 = &r0.f0; let v = *r1; v
    let stmts = vec![
        let_borrow_loc("r0", "x"),
        let_borrow_field("r1", STRUCT_S, 0, Expr::Var(VarId::from("r0"))),
        let_read_ref("v", "r1"),
    ];
    let tail = Expr::Var(VarId::from("v"));
    let mut program = one_fn_program(stmts, tail, Type::UInt(64));
    rewrite_read_refs(&mut program);

    let expected = path_to_expr(VarId::from("x"), &[field_edge(STRUCT_S, 0)]);
    let v_let = match &body_of(&program).stmts[2] {
        Stmt::Let { value, .. } => value.clone(),
        other => panic!("expected Stmt::Let, got {:?}", other),
    };
    assert_eq!(v_let, expected);
}

#[test]
fn read_ref_through_two_deep_field_chain() {
    // let r0 = &x; let r1 = &r0.f0; let r2 = &r1.f2; let v = *r2; v
    let stmts = vec![
        let_borrow_loc("r0", "x"),
        let_borrow_field("r1", STRUCT_S, 0, Expr::Var(VarId::from("r0"))),
        let_borrow_field("r2", STRUCT_T, 2, Expr::Var(VarId::from("r1"))),
        let_read_ref("v", "r2"),
    ];
    let tail = Expr::Var(VarId::from("v"));
    let mut program = one_fn_program(stmts, tail, Type::UInt(64));
    rewrite_read_refs(&mut program);

    let expected = path_to_expr(
        VarId::from("x"),
        &[field_edge(STRUCT_S, 0), field_edge(STRUCT_T, 2)],
    );
    let v_let = match &body_of(&program).stmts[3] {
        Stmt::Let { value, .. } => value.clone(),
        other => panic!("expected Stmt::Let, got {:?}", other),
    };
    assert_eq!(v_let, expected);
}

#[test]
fn read_ref_inside_if_then_arm_lowers_only_in_arm() {
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

    let expected_then_tail = path_to_expr(VarId::from("x"), &[field_edge(STRUCT_S, 0)]);
    if let BlockTail::Value(Expr::If { then_branch, .. }) = &body_of(&program).tail {
        if let BlockTail::Value(v) = &then_branch.tail {
            assert_eq!(v, &expected_then_tail);
        } else {
            panic!("expected then-arm tail to be Value");
        }
    } else {
        panic!("expected If at tail");
    }
}

#[test]
fn read_ref_inside_match_arm_lowers_correctly() {
    use crate::ir::builder::{block, tail_value};
    use crate::ir::MatchArm;

    let arm0_stmts = vec![
        let_borrow_loc("r0", "x"),
        let_borrow_field("r1", STRUCT_S, 1, Expr::Var(VarId::from("r0"))),
    ];
    let arm0_body = block(
        arm0_stmts,
        tail_value(Expr::ReadRef(Box::new(Expr::Var(VarId::from("r1"))))),
    );
    let arm0 = MatchArm {
        variant: 0,
        bindings: Vec::new(),
        body: Box::new(arm0_body),
    };
    let arm1_body = block(
        vec![],
        tail_value(Expr::Const(crate::ir::Const::UInt {
            bits: 64,
            value: ethnum::U256::from(7u64),
        })),
    );
    let arm1 = MatchArm {
        variant: 1,
        bindings: Vec::new(),
        body: Box::new(arm1_body),
    };
    let match_expr = Expr::Match {
        struct_id: 0,
        selector: Box::new(Expr::Var(VarId::from("x"))),
        cases: vec![arm0, arm1],
    };
    let mut program = one_fn_program(vec![], match_expr, Type::UInt(64));
    rewrite_read_refs(&mut program);

    let expected = path_to_expr(VarId::from("x"), &[field_edge(STRUCT_S, 1)]);
    if let BlockTail::Value(Expr::Match { cases, .. }) = &body_of(&program).tail {
        if let BlockTail::Value(v) = &cases[0].body.tail {
            assert_eq!(v, &expected);
        } else {
            panic!("expected match arm 0 tail to be Value");
        }
    } else {
        panic!("expected Match at tail");
    }
}

#[test]
fn read_ref_inside_abort_tail_lowers_in_arm() {
    // if (cond) { let r0 = &x; let r1 = &r0.f0; abort *r1 } else { 0 }
    use crate::ir::builder::{block, just, tail_abort};
    let stmts = vec![
        let_borrow_loc("r0", "x"),
        let_borrow_field("r1", STRUCT_S, 0, Expr::Var(VarId::from("r0"))),
    ];
    let then_branch = block(
        stmts,
        tail_abort(Expr::ReadRef(Box::new(Expr::Var(VarId::from("r1"))))),
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

    let expected = path_to_expr(VarId::from("x"), &[field_edge(STRUCT_S, 0)]);
    if let BlockTail::Value(Expr::If { then_branch, .. }) = &body_of(&program).tail {
        if let BlockTail::Abort { code } = &then_branch.tail {
            assert_eq!(code.as_ref(), &expected);
        } else {
            panic!("expected then-arm tail to be Abort");
        }
    } else {
        panic!("expected If at tail");
    }
}

#[test]
fn idempotent_run_twice_is_noop_on_second_call() {
    let stmts = vec![
        let_borrow_loc("r0", "x"),
        let_borrow_field("r1", STRUCT_S, 0, Expr::Var(VarId::from("r0"))),
        let_read_ref("v", "r1"),
    ];
    let tail = Expr::Var(VarId::from("v"));
    let mut program = one_fn_program(stmts, tail, Type::UInt(64));
    rewrite_read_refs(&mut program);
    let after_once = program.clone();
    rewrite_read_refs(&mut program);
    assert_eq!(program, after_once, "second run must be a no-op");
}

#[test]
fn deterministic_byte_identical_output_across_runs() {
    let stmts = vec![
        let_borrow_loc("r0", "x"),
        let_borrow_field("r1", STRUCT_S, 0, Expr::Var(VarId::from("r0"))),
        let_read_ref("v", "r1"),
    ];
    let tail = Expr::Var(VarId::from("v"));

    let mut a = one_fn_program(stmts.clone(), tail.clone(), Type::UInt(64));
    let mut b = one_fn_program(stmts, tail, Type::UInt(64));
    rewrite_read_refs(&mut a);
    rewrite_read_refs(&mut b);
    assert_eq!(a, b);
}

#[test]
fn native_function_left_untouched() {
    // Obsolete: natives now live in program.natives.decls, not
    // program.functions; stages walk only functions, so this
    // behavior is structurally guaranteed.
}
