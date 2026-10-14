//! Render-side smoke tests for stage 10 + the BoundedNat name mapping.
//!
//! These exercise the full IR -> Lean path: build a program with raw
//! `BinOp` / `UnOp::Cast`, run stage 10 to lower into `BoundedU{N}_<op>`
//! Calls, render, and assert the output contains the expected
//! width-agnostic `BoundedNat.<op>` text.

use crate::ir::expr::{Block, BlockTail, Expr};
use crate::ir::ops::BinOp;
use crate::ir::ty::Type;
use crate::render::render_program;
use crate::stage_10_bounded_nat::run;

use super::fixtures::{fn_add_u64, fn_cast_u64_to_u8, func, param, program_with, vid};

#[test]
fn add_u64_renders_as_bounded_nat_add() {
    let mut p = program_with(vec![(0, fn_add_u64())]);
    run(&mut p).unwrap();
    let out = render_program(&p).expect("render");
    assert!(
        out.contains("BoundedNat.add a b"),
        "expected BoundedNat.add in output, got:\n{out}"
    );
    // Confirm we did NOT leak the IR-side per-width name.
    assert!(
        !out.contains("BoundedU64_add"),
        "renderer leaked IR-side name BoundedU64_add:\n{out}"
    );
}

#[test]
fn cast_renders_with_type_ascription() {
    let mut p = program_with(vec![(0, fn_cast_u64_to_u8())]);
    run(&mut p).unwrap();
    let out = render_program(&p).expect("render");
    assert!(
        out.contains("(BoundedNat.convert"),
        "expected BoundedNat.convert in output:\n{out}"
    );
    assert!(
        out.contains(": BoundedU8)"),
        "expected type ascription `: BoundedU8)`:\n{out}"
    );
}

#[test]
fn shl_renders_as_operator() {
    let f = func(
        "shf",
        vec![param("a", Type::UInt(64)), param("k", Type::UInt(8))],
        Type::UInt(64),
        Block {
            stmts: vec![],
            tail: BlockTail::Value(Expr::BinOp {
                op: BinOp::Shl,
                lhs: Box::new(Expr::Var(vid("a"))),
                rhs: Box::new(Expr::Var(vid("k"))),
            }),
        },
    );
    let mut p = program_with(vec![(0, f)]);
    run(&mut p).unwrap();
    let out = render_program(&p).expect("render");
    assert!(
        out.contains("a <<< k") || out.contains("(a <<< k)"),
        "expected `a <<< k` in output, got:\n{out}"
    );
}

#[test]
fn lt_renders_as_bounded_nat_lt() {
    let f = func(
        "less",
        vec![param("a", Type::UInt(64)), param("b", Type::UInt(64))],
        Type::Bool,
        Block {
            stmts: vec![],
            tail: BlockTail::Value(Expr::BinOp {
                op: BinOp::Lt,
                lhs: Box::new(Expr::Var(vid("a"))),
                rhs: Box::new(Expr::Var(vid("b"))),
            }),
        },
    );
    let mut p = program_with(vec![(0, f)]);
    run(&mut p).unwrap();
    let out = render_program(&p).expect("render");
    assert!(
        out.contains("BoundedNat.lt a b"),
        "expected BoundedNat.lt in output:\n{out}"
    );
}

#[test]
fn bitwise_band_renders_as_bounded_nat_land() {
    let f = func(
        "ba",
        vec![param("a", Type::UInt(64)), param("b", Type::UInt(64))],
        Type::UInt(64),
        Block {
            stmts: vec![],
            tail: BlockTail::Value(Expr::BinOp {
                op: BinOp::BitAnd,
                lhs: Box::new(Expr::Var(vid("a"))),
                rhs: Box::new(Expr::Var(vid("b"))),
            }),
        },
    );
    let mut p = program_with(vec![(0, f)]);
    run(&mut p).unwrap();
    let out = render_program(&p).expect("render");
    assert!(
        out.contains("BoundedNat.land a b"),
        "BitAnd should render as BoundedNat.land (prelude name):\n{out}"
    );
}

#[test]
fn narrowing_cast_aborts_renders_with_bound_to() {
    // Wrap the narrowing cast inside a body that uses both the value
    // and (in spec land, eventually) its aborts predicate. Here we
    // just verify the main path: cast renders cleanly.
    let mut p = program_with(vec![(0, fn_cast_u64_to_u8())]);
    run(&mut p).unwrap();
    // We do not run stage 7 here, so .aborts companions are never
    // referenced from the rendered output -- they just exist as
    // registered FunIds. Render still succeeds (their bodies are
    // native stubs).
    let _out = render_program(&p).expect("render");
}

#[test]
fn llvm_wrapping_signed_and_shift_ops_render_to_explicit_helpers() {
    let cases = [
        (BinOp::WrappingSub, "BoundedNat.wrapping_sub"),
        (BinOp::SAdd, "BoundedNat.sadd"),
        (BinOp::SDiv, "BoundedNat.sdiv"),
        (BinOp::SLt, "BoundedNat.slt"),
        (BinOp::AShr, "BoundedNat.ashr"),
    ];
    for (op, expected) in cases {
        let return_type = if op == BinOp::SLt {
            Type::Bool
        } else {
            Type::UInt(64)
        };
        let f = func(
            "llvm_op",
            vec![param("a", Type::UInt(64)), param("b", Type::UInt(64))],
            return_type,
            Block {
                stmts: vec![],
                tail: BlockTail::Value(Expr::BinOp {
                    op,
                    lhs: Box::new(Expr::Var(vid("a"))),
                    rhs: Box::new(Expr::Var(vid("b"))),
                }),
            },
        );
        let mut p = program_with(vec![(0, f)]);
        run(&mut p).unwrap();
        let out = render_program(&p).expect("render");
        assert!(out.contains(expected), "expected {expected} in:\n{out}");
    }
}
