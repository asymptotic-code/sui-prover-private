//! Tests for `effects_predicate::is_pure_total` and its block / stmt
//! companions.
//!
//! Each test pins the answer for one or two structural shapes.
//! Call dispatch (PURE / partial / GlobalMut callees) lives in
//! `tests/effects_calls.rs`; this file covers shape-level dispatch
//! only, with a small `Program` carrying just enough callees to
//! exercise the Call arm.

use super::fixtures::*;
use crate::ir::{
    quant::QuantDomain, AbortBit, BinOp, BitOp, BorrowEdge, BorrowNode, DetBit, Effects, Expr,
    MatchArm, MutLevel, QuantifierKind, Type, UnOp,
};
use crate::stage_06_let_inline::effects_predicate::{
    is_pure_total, is_pure_total_block, is_pure_total_stmt,
};

#[test]
fn atoms_are_pure_total() {
    let p = empty_program();
    assert!(is_pure_total(&var("x"), &p));
    assert!(is_pure_total(&u64_const(7), &p));
    assert!(is_pure_total(&Expr::Unit, &p));
    assert!(is_pure_total(&bool_const(true), &p));
}

#[test]
fn arithmetic_aborts_so_partial() {
    let p = empty_program();
    // Add on UInt operands can overflow; not pure-total.
    assert!(!is_pure_total(&add(u64_const(1), u64_const(2)), &p));
    // Sub / Div / Mod / Mul / Shl / Shr same.
    for op in [
        BinOp::Sub,
        BinOp::Mul,
        BinOp::Div,
        BinOp::Mod,
        BinOp::Shl,
        BinOp::Shr,
    ] {
        let e = Expr::BinOp {
            op,
            lhs: Box::new(u64_const(1)),
            rhs: Box::new(u64_const(2)),
        };
        assert!(
            !is_pure_total(&e, &p),
            "op {:?} should NOT be pure-total",
            op
        );
    }
}

#[test]
fn bitwise_and_logical_and_compare_are_pure_total() {
    let p = empty_program();
    for op in [
        BinOp::BitAnd,
        BinOp::BitOr,
        BinOp::BitXor,
        BinOp::And,
        BinOp::Or,
        BinOp::Eq,
        BinOp::Neq,
        BinOp::Lt,
        BinOp::Le,
        BinOp::Gt,
        BinOp::Ge,
    ] {
        let e = Expr::BinOp {
            op,
            lhs: Box::new(u64_const(1)),
            rhs: Box::new(u64_const(2)),
        };
        assert!(is_pure_total(&e, &p), "op {:?} should be pure-total", op);
    }
}

#[test]
fn cast_is_partial() {
    let p = empty_program();
    let e = Expr::UnOp {
        op: UnOp::Cast(8),
        operand: Box::new(u64_const(300)),
    };
    assert!(!is_pure_total(&e, &p));
}

#[test]
fn not_and_bitnot_are_pure_total() {
    let p = empty_program();
    for op in [UnOp::Not, UnOp::BitNot] {
        let e = Expr::UnOp {
            op,
            operand: Box::new(var("x")),
        };
        assert!(is_pure_total(&e, &p));
    }
}

#[test]
fn call_to_pure_total_callee_is_pure_total() {
    let callee = stub_callee("pure", Effects::PURE, Type::UInt(64));
    let p = program_with(vec![(7, callee)]);

    let e = call(7, vec![var("x"), var("y")]);
    assert!(is_pure_total(&e, &p));
}

#[test]
fn call_to_pure_partial_callee_is_not_pure_total() {
    let callee = stub_callee(
        "partial",
        Effects {
            aborts: AbortBit::Partial,
            det: DetBit::Det,
            mutation: MutLevel::NoMut,
            world_writes: false,
        },
        Type::UInt(64),
    );
    let p = program_with(vec![(7, callee)]);

    let e = call(7, vec![var("x")]);
    assert!(!is_pure_total(&e, &p));
}

#[test]
fn call_to_impure_callee_is_not_pure_total() {
    let callee = stub_callee("impure", Effects::CONSERVATIVE, Type::Unit);
    let p = program_with(vec![(7, callee)]);

    let e = call(7, vec![]);
    assert!(!is_pure_total(&e, &p));
}

#[test]
fn call_to_pure_total_with_partial_arg_is_not_pure_total() {
    let callee = stub_callee("pure", Effects::PURE, Type::UInt(64));
    let p = program_with(vec![(7, callee)]);

    // arg is `1 + 2` -- arithmetic, partial.
    let e = call(7, vec![add(u64_const(1), u64_const(2))]);
    assert!(!is_pure_total(&e, &p));
}

#[test]
fn call_to_missing_callee_is_conservatively_not_pure_total() {
    let p = empty_program();
    let e = call(99, vec![]);
    assert!(!is_pure_total(&e, &p));
}

#[test]
fn pack_field_unpack_recurse() {
    let p = empty_program();
    let pack = Expr::Pack {
        struct_id: 0,
        type_args: Vec::new(),
        variant: None,
        fields: vec![var("a"), var("b")],
    };
    assert!(is_pure_total(&pack, &p));

    let field = Expr::Field {
        struct_id: 0,
        field_index: 0,
        base: Box::new(var("s")),
    };
    assert!(is_pure_total(&field, &p));

    let unpack = Expr::Unpack {
        struct_id: 0,
        variant: None,
        value: Box::new(var("s")),
    };
    assert!(is_pure_total(&unpack, &p));
}

#[test]
fn pack_with_partial_field_is_partial() {
    let p = empty_program();
    let pack = Expr::Pack {
        struct_id: 0,
        type_args: Vec::new(),
        variant: None,
        fields: vec![var("a"), add(u64_const(1), u64_const(2))],
    };
    assert!(!is_pure_total(&pack, &p));
}

#[test]
fn update_field_and_update_vec_recurse() {
    let p = empty_program();
    let uf = Expr::Update {
        step: crate::ir::path::PathStep::Field {
            struct_id: 0,
            field_index: 0,
        },
        base: Box::new(var("s")),
        value: Box::new(var("v")),
    };
    assert!(is_pure_total(&uf, &p));

    let uv = Expr::Update {
        step: crate::ir::path::PathStep::VecIndex(Box::new(var("i"))),
        base: Box::new(var("vec")),
        value: Box::new(var("v")),
    };
    assert!(is_pure_total(&uv, &p));
}

#[test]
fn if_with_both_value_arms_pure_is_pure_total() {
    let p = empty_program();
    let e = Expr::If {
        cond: Box::new(var("c")),
        then_branch: Box::new(block_value(vec![], u64_const(1))),
        else_branch: Box::new(block_value(vec![], u64_const(2))),
    };
    assert!(is_pure_total(&e, &p));
}

#[test]
fn if_with_abort_tail_is_not_pure_total() {
    let p = empty_program();
    let e = Expr::If {
        cond: Box::new(var("c")),
        then_branch: Box::new(block_value(vec![], u64_const(1))),
        else_branch: Box::new(block_abort(vec![], u64_const(7))),
    };
    assert!(!is_pure_total(&e, &p));
}

#[test]
fn match_with_all_value_arms_pure_is_pure_total() {
    let p = empty_program();
    let e = Expr::Match {
        struct_id: 0,
        selector: Box::new(var("s")),
        cases: vec![
            MatchArm {
                variant: 0,
                bindings: vec![],
                body: Box::new(block_value(vec![], u64_const(1))),
            },
            MatchArm {
                variant: 1,
                bindings: vec![],
                body: Box::new(block_value(vec![], u64_const(2))),
            },
        ],
    };
    assert!(is_pure_total(&e, &p));
}

#[test]
fn while_is_never_pure_total() {
    let p = empty_program();
    let e = Expr::While {
        header: Box::new(block_value(vec![], Expr::Unit)),
        cond: Box::new(bool_const(false)),
        body: Box::new(block_continue(vec![], 0, Expr::Unit)),
        iter_locals: Vec::new(),
        header_exit_locals: Vec::new(),
        live_out: vec![],
    };
    assert!(!is_pure_total(&e, &p));
}

#[test]
fn mutref_machinery_is_not_pure_total() {
    let p = empty_program();
    assert!(!is_pure_total(&Expr::BorrowLoc(vid("x")), &p));
    assert!(!is_pure_total(
        &Expr::Borrow {
            step: crate::ir::path::PathStep::Field {
                struct_id: 0,
                field_index: 0
            },
            base: Box::new(var("s"))
        },
        &p
    ));
    // ReadRef: now propagates pure-and-total from its inner expression.
    // Var(_) is pure-total, so `ReadRef(Var(r))` is pure-total too --
    // a value read with no side effects. Test with an impure inner
    // (BorrowLoc) to keep the not-pure assertion meaningful.
    assert!(is_pure_total(&Expr::ReadRef(Box::new(var("r"))), &p));
    assert!(!is_pure_total(
        &Expr::ReadRef(Box::new(Expr::BorrowLoc(vid("x")))),
        &p
    ));
    assert!(!is_pure_total(
        &Expr::WriteRef {
            reference: Box::new(var("r")),
            value: Box::new(u64_const(1)),
        },
        &p
    ));
    assert!(!is_pure_total(
        &Expr::WriteBack {
            node: BorrowNode::LocalRoot(vid("parent")),
            edge: BorrowEdge::Direct,
            child: vid("child"),
            world: None,
        },
        &p
    ));
}

#[test]
fn to_prop_and_to_bool_recurse() {
    let p = empty_program();
    assert!(is_pure_total(&Expr::ToProp(Box::new(var("x"))), &p));
    assert!(is_pure_total(&Expr::ToBool(Box::new(var("x"))), &p));
    assert!(!is_pure_total(
        &Expr::ToProp(Box::new(add(u64_const(1), u64_const(2)))),
        &p
    ));
}

#[test]
fn quantifier_with_pure_body_is_pure_total() {
    let p = empty_program();
    let e = Expr::Quantifier {
        kind: QuantifierKind::Forall,
        binder: vid("i"),
        binder_type: Type::UInt(64),
        domain: QuantDomain::Range {
            start: Box::new(u64_const(0)),
            end: Box::new(var("n")),
        },
        body: Box::new(block_value(vec![], lt(var("i"), var("n")))),
    };
    assert!(is_pure_total(&e, &p));
}

#[test]
fn quantifier_with_partial_body_is_partial() {
    let p = empty_program();
    // body: `i + 1`. Partial.
    let e = Expr::Quantifier {
        kind: QuantifierKind::Forall,
        binder: vid("i"),
        binder_type: Type::UInt(64),
        domain: QuantDomain::Unbounded,
        body: Box::new(block_value(vec![], add(var("i"), u64_const(1)))),
    };
    assert!(!is_pure_total(&e, &p));
}

#[test]
fn bitop_recurses() {
    let p = empty_program();
    let pure_extract = Expr::BitOp(BitOp::Extract {
        high: 8,
        low: 0,
        operand: Box::new(var("x")),
    });
    assert!(is_pure_total(&pure_extract, &p));

    let partial_extract = Expr::BitOp(BitOp::Extract {
        high: 8,
        low: 0,
        operand: Box::new(add(u64_const(1), u64_const(2))),
    });
    assert!(!is_pure_total(&partial_extract, &p));
}

#[test]
fn block_with_non_value_tail_is_never_pure_total() {
    let p = empty_program();
    assert!(!is_pure_total_block(
        &block_break(vec![], 0, Expr::Unit),
        &p
    ));
    assert!(!is_pure_total_block(
        &block_continue(vec![], 0, Expr::Unit),
        &p
    ));
    assert!(!is_pure_total_block(&block_return(vec![], Expr::Unit), &p));
    assert!(!is_pure_total_block(&block_abort(vec![], u64_const(7)), &p));
}

#[test]
fn block_with_value_tail_and_all_pure_stmts_is_pure_total() {
    let p = empty_program();
    let b = block_value(
        vec![let_stmt("a", var("x")), let_stmt("b", u64_const(1))],
        var("b"),
    );
    assert!(is_pure_total_block(&b, &p));
}

#[test]
fn block_with_partial_stmt_is_not_pure_total() {
    let p = empty_program();
    // `let a = 1 + 2; a`. Partial Let value.
    let b = block_value(
        vec![let_stmt("a", add(u64_const(1), u64_const(2)))],
        var("a"),
    );
    assert!(!is_pure_total_block(&b, &p));
}

#[test]
fn stmt_let_pure_value_is_pure_total() {
    let p = empty_program();
    let s = let_stmt("a", var("x"));
    assert!(is_pure_total_stmt(&s, &p));
}

#[test]
fn stmt_eval_pure_value_is_pure_total() {
    let p = empty_program();
    let s = eval_stmt(u64_const(7));
    assert!(is_pure_total_stmt(&s, &p));
}

#[test]
fn stmt_let_partial_value_is_not_pure_total() {
    let p = empty_program();
    let s = let_stmt("a", add(u64_const(1), u64_const(2)));
    assert!(!is_pure_total_stmt(&s, &p));
}
