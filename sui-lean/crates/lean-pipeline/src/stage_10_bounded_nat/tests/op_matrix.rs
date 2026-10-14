//! Op-and-width matrix tests: confirm every supported op + every
//! Move width registers a distinct FunId.

use crate::ir::expr::{Block, BlockTail, Expr};
use crate::ir::ops::{BinOp, UnOp};
use crate::ir::ty::Type;
use crate::stage_10_bounded_nat::prelude_fids::{aborts_name, main_name, Op};
use crate::stage_10_bounded_nat::run;

use super::fixtures::{func, param, program_with, vid};

const WIDTHS: [u32; 6] = [8, 16, 32, 64, 128, 256];

fn find_native(p: &crate::ir::Program, name: &str) -> Option<crate::ir::FunId> {
    p.natives
        .decls
        .iter()
        .find(|(_, d)| d.name == name)
        .map(|(id, _)| *id)
}

fn binop_fn(name: &str, op: BinOp, width: u32) -> crate::ir::Function {
    let ret = match op {
        BinOp::Eq
        | BinOp::Neq
        | BinOp::Lt
        | BinOp::Le
        | BinOp::Gt
        | BinOp::Ge
        | BinOp::SLt
        | BinOp::SLe
        | BinOp::SGt
        | BinOp::SGe => Type::Bool,
        _ => Type::UInt(width),
    };
    func(
        name,
        vec![param("a", Type::UInt(width)), param("b", Type::UInt(width))],
        ret,
        Block {
            stmts: vec![],
            tail: BlockTail::Value(Expr::BinOp {
                op,
                lhs: Box::new(Expr::Var(vid("a"))),
                rhs: Box::new(Expr::Var(vid("b"))),
            }),
        },
    )
}

#[test]
fn every_arithmetic_op_registers_main_and_aborts_for_every_width() {
    let ops = [
        (BinOp::Add, Op::Add),
        (BinOp::Sub, Op::Sub),
        (BinOp::Mul, Op::Mul),
        (BinOp::Div, Op::Div),
        (BinOp::Mod, Op::Mod),
    ];
    for (binop, op) in ops {
        for &w in &WIDTHS {
            let mut p = program_with(vec![(0, binop_fn("f", binop, w))]);
            run(&mut p).unwrap();
            assert!(
                find_native(&p, &main_name(op, w)).is_some(),
                "{} at width {w} should register main",
                main_name(op, w)
            );
            assert!(
                find_native(&p, &aborts_name(op, w)).is_some(),
                "{} should register aborts companion",
                main_name(op, w)
            );
        }
    }
}

#[test]
fn bitwise_and_comparison_ops_register_main_only() {
    let cases: &[(BinOp, Op)] = &[
        (BinOp::BitAnd, Op::BitAnd),
        (BinOp::BitOr, Op::BitOr),
        (BinOp::BitXor, Op::BitXor),
        (BinOp::Eq, Op::Eq),
        (BinOp::Neq, Op::Neq),
        (BinOp::Lt, Op::Lt),
        (BinOp::Le, Op::Le),
        (BinOp::Gt, Op::Gt),
        (BinOp::Ge, Op::Ge),
    ];
    for &(binop, op) in cases {
        let mut p = program_with(vec![(0, binop_fn("f", binop, 64))]);
        run(&mut p).unwrap();
        assert!(
            find_native(&p, &main_name(op, 64)).is_some(),
            "{} should register main",
            main_name(op, 64)
        );
        assert!(
            find_native(&p, &aborts_name(op, 64)).is_none(),
            "{} should NOT register aborts (never aborts)",
            main_name(op, 64)
        );
    }
}

#[test]
fn llvm_wrapping_arithmetic_registers_no_aborts_companion() {
    let cases = [
        (BinOp::WrappingAdd, Op::WrappingAdd),
        (BinOp::WrappingSub, Op::WrappingSub),
        (BinOp::WrappingMul, Op::WrappingMul),
    ];
    for (binop, op) in cases {
        let mut p = program_with(vec![(0, binop_fn("f", binop, 32))]);
        run(&mut p).unwrap();
        assert!(find_native(&p, &main_name(op, 32)).is_some());
        assert!(find_native(&p, &aborts_name(op, 32)).is_none());
    }
}

#[test]
fn signed_checked_arithmetic_and_division_register_aborts_companions() {
    let cases = [
        (BinOp::SAdd, Op::SAdd),
        (BinOp::SSub, Op::SSub),
        (BinOp::SMul, Op::SMul),
        (BinOp::SDiv, Op::SDiv),
        (BinOp::SMod, Op::SMod),
    ];
    for (binop, op) in cases {
        let mut p = program_with(vec![(0, binop_fn("f", binop, 32))]);
        run(&mut p).unwrap();
        assert!(find_native(&p, &main_name(op, 32)).is_some());
        let main = find_native(&p, &main_name(op, 32)).unwrap();
        let aborts = find_native(&p, &aborts_name(op, 32)).unwrap();
        assert!(
            crate::stage_10_bounded_nat::prelude_fids::is_aborting_native_pair(
                &p.natives.decls[&main],
                &p.natives.decls[&aborts],
            )
        );
    }
}

#[test]
fn signed_comparisons_register_main_only() {
    for (binop, op) in [
        (BinOp::SLt, Op::SLt),
        (BinOp::SLe, Op::SLe),
        (BinOp::SGt, Op::SGt),
        (BinOp::SGe, Op::SGe),
    ] {
        let mut p = program_with(vec![(0, binop_fn("f", binop, 64))]);
        run(&mut p).unwrap();
        assert!(find_native(&p, &main_name(op, 64)).is_some());
        assert!(find_native(&p, &aborts_name(op, 64)).is_none());
    }
}

#[test]
fn shift_registers_rhs_width_in_main_name() {
    // Shift by u8 amount, lhs u64.
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
    let op = Op::Shl { rhs_width: 8 };
    assert!(find_native(&p, &main_name(op, 64)).is_some());
    assert!(find_native(&p, &aborts_name(op, 64)).is_some());
}

#[test]
fn shr_registers_rhs_width_and_aborts() {
    // Right shift mirrors Shl: a width-tagged native plus an aborts
    // companion (the shift-amount bound). Shl was tested; Shr was not.
    let f = func(
        "shr",
        vec![param("a", Type::UInt(64)), param("k", Type::UInt(8))],
        Type::UInt(64),
        Block {
            stmts: vec![],
            tail: BlockTail::Value(Expr::BinOp {
                op: BinOp::Shr,
                lhs: Box::new(Expr::Var(vid("a"))),
                rhs: Box::new(Expr::Var(vid("k"))),
            }),
        },
    );
    let mut p = program_with(vec![(0, f)]);
    run(&mut p).unwrap();
    let op = Op::Shr { rhs_width: 8 };
    assert!(find_native(&p, &main_name(op, 64)).is_some());
    assert!(find_native(&p, &aborts_name(op, 64)).is_some());
}

#[test]
fn llvm_right_shifts_are_distinct_and_register_amount_guards() {
    for (binop, op) in [
        (BinOp::LShr, Op::LShr { rhs_width: 8 }),
        (BinOp::AShr, Op::AShr { rhs_width: 8 }),
    ] {
        let f = func(
            "shr",
            vec![param("a", Type::UInt(64)), param("k", Type::UInt(8))],
            Type::UInt(64),
            Block {
                stmts: vec![],
                tail: BlockTail::Value(Expr::BinOp {
                    op: binop,
                    lhs: Box::new(Expr::Var(vid("a"))),
                    rhs: Box::new(Expr::Var(vid("k"))),
                }),
            },
        );
        let mut p = program_with(vec![(0, f)]);
        run(&mut p).unwrap();
        assert!(find_native(&p, &main_name(op, 64)).is_some());
        assert!(find_native(&p, &aborts_name(op, 64)).is_some());
    }
}

#[test]
fn bnot_registers_main_only() {
    let f = func(
        "bn",
        vec![param("x", Type::UInt(32))],
        Type::UInt(32),
        Block {
            stmts: vec![],
            tail: BlockTail::Value(Expr::UnOp {
                op: UnOp::BitNot,
                operand: Box::new(Expr::Var(vid("x"))),
            }),
        },
    );
    let mut p = program_with(vec![(0, f)]);
    run(&mut p).unwrap();
    assert!(find_native(&p, &main_name(Op::BitNot, 32)).is_some());
    assert!(find_native(&p, &aborts_name(Op::BitNot, 32)).is_none());
}

#[test]
fn same_width_adds_register_distinct_fids_at_different_widths() {
    // Two functions, same op, different widths -> separate FunIds.
    let f8 = binop_fn("f8", BinOp::Add, 8);
    let f64 = binop_fn("f64", BinOp::Add, 64);
    let mut p = program_with(vec![(0, f8), (1, f64)]);
    run(&mut p).unwrap();
    let fid8 = find_native(&p, &main_name(Op::Add, 8)).unwrap();
    let fid64 = find_native(&p, &main_name(Op::Add, 64)).unwrap();
    assert_ne!(fid8, fid64, "different widths must get different FunIds");
}

#[test]
fn nested_binops_rewrite_inside_out() {
    // `(a + b) * c` -- the outer mul should call BoundedU64_mul with
    // a nested BoundedU64_add Call as its first arg.
    let f = func(
        "nested",
        vec![
            param("a", Type::UInt(64)),
            param("b", Type::UInt(64)),
            param("c", Type::UInt(64)),
        ],
        Type::UInt(64),
        Block {
            stmts: vec![],
            tail: BlockTail::Value(Expr::BinOp {
                op: BinOp::Mul,
                lhs: Box::new(Expr::BinOp {
                    op: BinOp::Add,
                    lhs: Box::new(Expr::Var(vid("a"))),
                    rhs: Box::new(Expr::Var(vid("b"))),
                }),
                rhs: Box::new(Expr::Var(vid("c"))),
            }),
        },
    );
    let mut p = program_with(vec![(0, f)]);
    run(&mut p).unwrap();

    let mul_fid = find_native(&p, &main_name(Op::Mul, 64)).unwrap();
    let add_fid = find_native(&p, &main_name(Op::Add, 64)).unwrap();

    let body = &p.functions[&0].body;
    let outer = match &body.tail {
        BlockTail::Value(e) => e,
        other => panic!("expected Value tail, got {other:?}"),
    };
    match outer {
        Expr::Call { fun, args, .. } => {
            assert_eq!(*fun, mul_fid);
            assert_eq!(args.len(), 2);
            // First arg is the nested add Call.
            match &args[0] {
                Expr::Call {
                    fun: inner_fid,
                    args: inner_args,
                    ..
                } => {
                    assert_eq!(*inner_fid, add_fid);
                    assert_eq!(inner_args.len(), 2);
                }
                other => panic!("expected nested Call for (a+b), got {other:?}"),
            }
        }
        other => panic!("expected Call as outer tail, got {other:?}"),
    }
}

#[test]
fn cast_between_every_width_pair_widening_has_no_aborts() {
    for &src in &WIDTHS {
        for &dst in &WIDTHS {
            if src == dst {
                continue; // same-width registers but isn't interesting
            }
            let f = func(
                "cast",
                vec![param("x", Type::UInt(src))],
                Type::UInt(dst),
                Block {
                    stmts: vec![],
                    tail: BlockTail::Value(Expr::UnOp {
                        op: UnOp::Cast(dst),
                        operand: Box::new(Expr::Var(vid("x"))),
                    }),
                },
            );
            let mut p = program_with(vec![(0, f)]);
            run(&mut p).unwrap();
            let op = Op::Cast { dst };
            assert!(find_native(&p, &main_name(op, src)).is_some());
            let aborts_present = find_native(&p, &aborts_name(op, src)).is_some();
            if dst < src {
                assert!(aborts_present, "narrowing u{src}->u{dst} must have aborts");
            } else {
                assert!(
                    !aborts_present,
                    "widening u{src}->u{dst} must not have aborts"
                );
            }
        }
    }
}

#[test]
fn logical_and_or_passes_through_unchanged() {
    // `a && b` on Bool is BinOp::And; should NOT be rewritten.
    let f = func(
        "land",
        vec![param("a", Type::Bool), param("b", Type::Bool)],
        Type::Bool,
        Block {
            stmts: vec![],
            tail: BlockTail::Value(Expr::BinOp {
                op: BinOp::And,
                lhs: Box::new(Expr::Var(vid("a"))),
                rhs: Box::new(Expr::Var(vid("b"))),
            }),
        },
    );
    let mut p = program_with(vec![(0, f)]);
    run(&mut p).unwrap();
    // The body's BinOp::And should survive.
    let body = &p.functions[&0].body;
    match &body.tail {
        BlockTail::Value(Expr::BinOp { op: BinOp::And, .. }) => (),
        other => panic!("expected surviving BinOp::And, got {other:?}"),
    }
}
