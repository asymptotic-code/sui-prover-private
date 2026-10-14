//! Tests for `use_count::count_uses`.
//!
//! Covers:
//! - Atom counting.
//! - `BlockTail::Break / Continue / Return / Abort` payload counting.
//! - Shadowing rules for `Quantifier::binder` (body only, not domain)
//!   and `MatchArm::bindings` (arm body only).

use super::fixtures::*;
use crate::ir::{quant::QuantDomain, Expr, MatchArm, QuantifierKind, Stmt, Type};
use crate::stage_06_let_inline::use_count::count_uses;

#[test]
fn empty_body_zero_uses() {
    let body = block_value(vec![], Expr::Unit);
    let uc = count_uses(&body);
    assert_eq!(uc.distinct_referenced(), 0);
    assert_eq!(uc.get(&vid("anything")), 0);
}

#[test]
fn single_var_one_use() {
    // Body: `x`
    let body = block_value(vec![], var("x"));
    let uc = count_uses(&body);
    assert_eq!(uc.get(&vid("x")), 1);
    assert_eq!(uc.distinct_referenced(), 1);
}

#[test]
fn var_used_three_times() {
    // Body: `(x, x, x)`
    let body = block_value(vec![], tuple(vec![var("x"), var("x"), var("x")]));
    let uc = count_uses(&body);
    assert_eq!(uc.get(&vid("x")), 3);
}

#[test]
fn let_pattern_position_does_not_count() {
    // `let x = y; x`
    //
    // `x` is a def position in the Let, NOT a use. `y` has one use.
    // The tail `x` is a use of the freshly-bound `x` -- count 1.
    let body = block_value(vec![let_stmt("x", var("y"))], var("x"));
    let uc = count_uses(&body);
    assert_eq!(uc.get(&vid("x")), 1);
    assert_eq!(uc.get(&vid("y")), 1);
}

#[test]
fn block_tail_break_counts_payload() {
    // Tail-only block: `break 0 carrying (x, y)`.
    let body = block_break(vec![], 0, tuple(vec![var("x"), var("y")]));
    let uc = count_uses(&body);
    assert_eq!(uc.get(&vid("x")), 1);
    assert_eq!(uc.get(&vid("y")), 1);
}

#[test]
fn block_tail_continue_counts_payload() {
    let body = block_continue(vec![], 0, tuple(vec![var("i_next")]));
    let uc = count_uses(&body);
    assert_eq!(uc.get(&vid("i_next")), 1);
}

#[test]
fn block_tail_return_counts_payload() {
    let body = block_return(vec![], var("result"));
    let uc = count_uses(&body);
    assert_eq!(uc.get(&vid("result")), 1);
}

#[test]
fn block_tail_abort_counts_payload() {
    let body = block_abort(vec![], var("code"));
    let uc = count_uses(&body);
    assert_eq!(uc.get(&vid("code")), 1);
}

#[test]
fn quantifier_binder_shadows_outer_var_in_body() {
    // Body: `forall x in 0..n, x > 0`.
    //
    // `n` is in the domain (outer scope) -- counted.
    // `x` inside the body refers to the binder -- NOT counted as
    // the outer `x`.
    let predicate = Expr::BinOp {
        op: crate::ir::BinOp::Gt,
        lhs: Box::new(var("x")),
        rhs: Box::new(u64_const(0)),
    };
    let body = block_value(
        vec![],
        Expr::Quantifier {
            kind: QuantifierKind::Forall,
            binder: vid("x"),
            binder_type: Type::UInt(64),
            domain: QuantDomain::Range {
                start: Box::new(u64_const(0)),
                end: Box::new(var("n")),
            },
            body: Box::new(block_value(vec![], predicate)),
        },
    );

    let uc = count_uses(&body);
    // Outer `x` has zero references (the only `x` inside is bound).
    assert_eq!(uc.get(&vid("x")), 0);
    // `n` (in domain, outer scope) counts.
    assert_eq!(uc.get(&vid("n")), 1);
}

#[test]
fn quantifier_binder_does_not_shadow_in_domain() {
    // Body: `forall i in 0..i, i`.
    //
    // The `i` in `end` is the OUTER `i` (the binder isn't in scope
    // for the domain). The `i` in the body refers to the binder
    // and does NOT count as a use of outer `i`.
    let body = block_value(
        vec![],
        Expr::Quantifier {
            kind: QuantifierKind::Forall,
            binder: vid("i"),
            binder_type: Type::UInt(64),
            domain: QuantDomain::Range {
                start: Box::new(u64_const(0)),
                end: Box::new(var("i")),
            },
            body: Box::new(block_value(vec![], var("i"))),
        },
    );

    let uc = count_uses(&body);
    // Only the domain's `end` counts; the body's `i` is bound.
    assert_eq!(uc.get(&vid("i")), 1);
}

#[test]
fn match_arm_binding_shadows_in_arm_body() {
    // Body: `match selector { V0(x) => x }`.
    //
    // The `x` inside the arm refers to the arm-local binding,
    // NOT any outer `x`.
    let body = block_value(
        vec![],
        Expr::Match {
            struct_id: 0,
            selector: Box::new(var("selector")),
            cases: vec![MatchArm {
                variant: 0,
                bindings: vec![vid("x")],
                body: Box::new(block_value(vec![], var("x"))),
            }],
        },
    );

    let uc = count_uses(&body);
    // `x` is bound by the arm, not a use of an outer `x`.
    assert_eq!(uc.get(&vid("x")), 0);
    assert_eq!(uc.get(&vid("selector")), 1);
}

#[test]
fn match_arm_binding_does_not_shadow_other_arms() {
    // Body: `match selector { V0(x) => x; V1 => x }`.
    //
    // The first arm's `x` is bound (no outer reference).
    // The second arm's `x` IS an outer reference -- counted.
    let body = block_value(
        vec![],
        Expr::Match {
            struct_id: 0,
            selector: Box::new(var("selector")),
            cases: vec![
                MatchArm {
                    variant: 0,
                    bindings: vec![vid("x")],
                    body: Box::new(block_value(vec![], var("x"))),
                },
                MatchArm {
                    variant: 1,
                    bindings: vec![],
                    body: Box::new(block_value(vec![], var("x"))),
                },
            ],
        },
    );

    let uc = count_uses(&body);
    assert_eq!(uc.get(&vid("x")), 1);
    assert_eq!(uc.get(&vid("selector")), 1);
}

#[test]
fn nested_lets_each_used_once() {
    // `let a = x; let b = a; b`.
    // `x` count 1 (in `let a` value).
    // `a` count 1 (in `let b` value).
    // `b` count 1 (in tail).
    let body = block_value(
        vec![let_stmt("a", var("x")), let_stmt("b", var("a"))],
        var("b"),
    );
    let uc = count_uses(&body);
    assert_eq!(uc.get(&vid("x")), 1);
    assert_eq!(uc.get(&vid("a")), 1);
    assert_eq!(uc.get(&vid("b")), 1);
}

#[test]
fn stmt_eval_counts_var_uses() {
    // `eval(f(x, x)); 0`. `x` is used twice in the Eval's call.
    let body = block_value(
        vec![Stmt::Eval(call(7, vec![var("x"), var("x")]))],
        u64_const(0),
    );
    let uc = count_uses(&body);
    assert_eq!(uc.get(&vid("x")), 2);
}
