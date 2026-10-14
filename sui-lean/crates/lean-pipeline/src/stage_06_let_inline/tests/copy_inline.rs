//! Tests for sub-pass 2a (`copy_inline`).
//!
//! Each test pins one structural rewrite. Multi-pass behaviour
//! (long copy chains collapsing fully) is exercised by an explicit
//! loop in `chain_collapses_one_level_per_call`.

use super::fixtures::*;
use crate::ir::{quant::QuantDomain, BlockTail, Expr, MatchArm, QuantifierKind, Stmt, Type};
use crate::stage_06_let_inline::copy_inline::copy_inline_once;

#[test]
fn simple_var_copy_inlines() {
    // `let a = x; a`  ->  `x`
    let mut body = block_value(vec![let_stmt("a", var("x"))], var("a"));
    let changed = copy_inline_once(&mut body);
    assert!(changed);
    assert_eq!(body.stmts.len(), 0);
    assert!(matches!(&body.tail, BlockTail::Value(Expr::Var(v)) if v.as_ref() == "x"));
}

#[test]
fn simple_const_copy_inlines() {
    // `let a = 7u64; a`  ->  `7u64`
    let mut body = block_value(vec![let_stmt("a", u64_const(7))], var("a"));
    let changed = copy_inline_once(&mut body);
    assert!(changed);
    assert_eq!(body.stmts.len(), 0);
    assert!(matches!(&body.tail, BlockTail::Value(Expr::Const(_))));
}

#[test]
fn chain_collapses_one_level_per_call() {
    // `let a = x; let b = a; let c = b; c`
    // -> after one call: `let b = x; let c = b; c`  (or equivalent
    //    flatten depending on order, but exactly 2 surviving lets).
    // -> fully collapses after enough calls.
    let mut body = block_value(
        vec![
            let_stmt("a", var("x")),
            let_stmt("b", var("a")),
            let_stmt("c", var("b")),
        ],
        var("c"),
    );
    let changed = copy_inline_once(&mut body);
    assert!(changed);
    // One call from the design contract collapses every trivial-copy
    // it can: pass 1 walks top-down and substitutes each `let v = Var(_)`
    // into the rest of the block. So after a single call, all three
    // lets are gone and the tail references `x`.
    assert_eq!(body.stmts.len(), 0);
    assert!(matches!(&body.tail, BlockTail::Value(Expr::Var(v)) if v.as_ref() == "x"));
}

#[test]
fn multi_use_copy_still_inlines() {
    // `let a = x; (a, a, a)`  ->  `(x, x, x)`
    // Multi-use is OK for Var copies (zero-cost).
    let mut body = block_value(
        vec![let_stmt("a", var("x"))],
        tuple(vec![var("a"), var("a"), var("a")]),
    );
    let changed = copy_inline_once(&mut body);
    assert!(changed);
    assert_eq!(body.stmts.len(), 0);
    if let BlockTail::Value(Expr::Tuple(elems)) = &body.tail {
        assert_eq!(elems.len(), 3);
        for e in elems {
            assert!(matches!(e, Expr::Var(v) if v.as_ref() == "x"));
        }
    } else {
        panic!("expected Tuple tail");
    }
}

#[test]
fn no_candidate_returns_false() {
    // `let a = b + c; a + 1`  -- BinOp is NOT a trivial-copy candidate.
    let mut body = block_value(
        vec![let_stmt("a", add(var("b"), var("c")))],
        add(var("a"), u64_const(1)),
    );
    let changed = copy_inline_once(&mut body);
    assert!(!changed);
    assert_eq!(body.stmts.len(), 1);
}

#[test]
fn descends_into_if_arm() {
    // body:
    //   if c { let a = x; a } else { 0 }
    let then_b = block_value(vec![let_stmt("a", var("x"))], var("a"));
    let else_b = block_value(vec![], u64_const(0));
    let mut body = block_value(vec![], if_expr(var("c"), then_b, else_b));
    let changed = copy_inline_once(&mut body);
    assert!(changed);
    // Then-arm collapsed; the let inside it is gone.
    if let BlockTail::Value(Expr::If { then_branch, .. }) = &body.tail {
        assert_eq!(then_branch.stmts.len(), 0);
        assert!(matches!(&then_branch.tail, BlockTail::Value(Expr::Var(v)) if v.as_ref() == "x"));
    } else {
        panic!("expected If tail");
    }
}

#[test]
fn descends_into_match_arm() {
    // match s { V0 => { let a = x; a } }
    let arm_body = block_value(vec![let_stmt("a", var("x"))], var("a"));
    let mut body = block_value(
        vec![],
        Expr::Match {
            struct_id: 0,
            selector: Box::new(var("s")),
            cases: vec![MatchArm {
                variant: 0,
                bindings: vec![],
                body: Box::new(arm_body),
            }],
        },
    );
    let changed = copy_inline_once(&mut body);
    assert!(changed);
    if let BlockTail::Value(Expr::Match { cases, .. }) = &body.tail {
        assert_eq!(cases[0].body.stmts.len(), 0);
        assert!(matches!(&cases[0].body.tail, BlockTail::Value(Expr::Var(v)) if v.as_ref() == "x"));
    } else {
        panic!("expected Match tail");
    }
}

#[test]
fn does_not_substitute_into_capturing_quantifier_body() {
    // `let v = Var(y); forall y in 0..n, P(v)`.
    //
    // The quantifier's binder `y` shadows `y` (the replacement).
    // copy_inline's substitution should NOT enter the quantifier
    // body because `y` is captured. The Let is still dropped --
    // copy_inline is committed to inlining at the use site -- but
    // the use site inside the Quantifier body is preserved as
    // `Var(v)`, leaving the body referencing an undefined `v`.
    //
    // SSA-form input shouldn't produce this collision; we test the
    // defensive behaviour: the Quantifier body is left untouched
    // (no `Var(y)` placed inside).
    let predicate = call(7, vec![var("v")]);
    let body_block = block_value(vec![], predicate);
    let quantifier = Expr::Quantifier {
        kind: QuantifierKind::Forall,
        binder: vid("y"),
        binder_type: Type::UInt(64),
        domain: QuantDomain::Range {
            start: Box::new(u64_const(0)),
            end: Box::new(var("n")),
        },
        body: Box::new(body_block),
    };
    let mut body = block_value(vec![let_stmt("v", var("y"))], quantifier);

    let _ = copy_inline_once(&mut body);
    // The let dropped (i.e., `v` is no longer bound at outer scope).
    assert_eq!(body.stmts.len(), 0);
    // The Quantifier body still references `Var(v)` -- substitution
    // was correctly skipped because the binder shadows `y`.
    if let BlockTail::Value(Expr::Quantifier { body: qbody, .. }) = &body.tail {
        if let BlockTail::Value(Expr::Call { args, .. }) = &qbody.tail {
            assert!(matches!(&args[0], Expr::Var(name) if name.as_ref() == "v"));
        } else {
            panic!("expected Call tail in quantifier body");
        }
    } else {
        panic!("expected Quantifier tail");
    }
}

#[test]
fn substitutes_into_non_capturing_quantifier_body() {
    // `let v = Var(y); forall i in 0..n, P(v)`.
    //
    // Quantifier binder `i` does NOT shadow `y`. Substitution
    // proceeds into the body: `Var(v)` becomes `Var(y)`.
    let predicate = call(7, vec![var("v")]);
    let body_block = block_value(vec![], predicate);
    let quantifier = Expr::Quantifier {
        kind: QuantifierKind::Forall,
        binder: vid("i"),
        binder_type: Type::UInt(64),
        domain: QuantDomain::Range {
            start: Box::new(u64_const(0)),
            end: Box::new(var("n")),
        },
        body: Box::new(body_block),
    };
    let mut body = block_value(vec![let_stmt("v", var("y"))], quantifier);

    let changed = copy_inline_once(&mut body);
    assert!(changed);
    assert_eq!(body.stmts.len(), 0);
    if let BlockTail::Value(Expr::Quantifier { body: qbody, .. }) = &body.tail {
        if let BlockTail::Value(Expr::Call { args, .. }) = &qbody.tail {
            assert!(matches!(&args[0], Expr::Var(name) if name.as_ref() == "y"));
        } else {
            panic!("expected Call tail in quantifier body");
        }
    } else {
        panic!("expected Quantifier tail");
    }
}

#[test]
fn identity_let_is_not_inlined() {
    // `let v = Var(v); use v`.
    //
    // Identity Let -- copy_inline's candidate test rejects this
    // (`Expr::Var(w)` where w == v). The Let survives this pass;
    // the postcondition validator catches it as `IdentityLet`.
    // (Stage 7's cont_inline now drops these self-rebinds at the
    // source, so they should not reach stage 6 in practice.)
    let mut body = block_value(
        vec![Stmt::Let {
            pattern: vec![Some(vid("v"))],
            value: var("v"),
        }],
        var("v"),
    );
    let changed = copy_inline_once(&mut body);
    assert!(!changed);
    assert_eq!(body.stmts.len(), 1);
}

#[test]
fn multi_pattern_let_is_skipped() {
    // `let (a, b) = (x, y); a`.
    //
    // copy_inline only fires for single-pattern lets. Multi-pattern
    // destructure goes to tuple_split (Phase 3).
    let mut body = block_value(
        vec![Stmt::Let {
            pattern: vec![Some(vid("a")), Some(vid("b"))],
            value: tuple(vec![var("x"), var("y")]),
        }],
        var("a"),
    );
    let changed = copy_inline_once(&mut body);
    assert!(!changed);
    assert_eq!(body.stmts.len(), 1);
}

#[test]
fn substitutes_into_block_tail_break_payload() {
    // body:
    //   while true {
    //     let v = x;
    //     continue 0 carrying (v)
    //   }
    let loop_body = block_continue(vec![let_stmt("v", var("x"))], 0, tuple(vec![var("v")]));
    let mut body = block_value(
        vec![Stmt::Eval(while_expr(
            block_value(vec![], Expr::Unit),
            bool_const(true),
            loop_body,
        ))],
        Expr::Unit,
    );
    let changed = copy_inline_once(&mut body);
    assert!(changed);
    if let Stmt::Eval(Expr::While { body: lb, .. }) = &body.stmts[0] {
        assert_eq!(lb.stmts.len(), 0);
        if let BlockTail::Continue { value, .. } = &lb.tail {
            if let Expr::Tuple(elems) = value.as_ref() {
                assert!(matches!(&elems[0], Expr::Var(name) if name.as_ref() == "x"));
            } else {
                panic!("expected Tuple in continue payload");
            }
        } else {
            panic!("expected Continue tail");
        }
    } else {
        panic!("expected Stmt::Eval(While)");
    }
}

#[test]
fn does_not_substitute_past_shadowing_let_in_arm() {
    // `let v = Var(x); if c { let v = call(7); v } else { v }`
    //
    // copy_inline inlines `v -> x`. In the then-arm, `let v = call(7)`
    // re-binds v, so the trailing `v` refers to the INNER binding and
    // must stay `v`; the else-arm `v` (the outer one) becomes `x`.
    // `Let` introduces scope uniformly with the Match/While/Quantifier
    // binders -- the substituter stops at the shadowing `let v`.
    let then_arm = block_value(vec![let_stmt("v", call(7, vec![]))], var("v"));
    let else_arm = block_value(vec![], var("v"));
    let mut body = block_value(
        vec![let_stmt("v", var("x"))],
        if_expr(var("c"), then_arm, else_arm),
    );
    let changed = copy_inline_once(&mut body);
    assert!(changed);
    let BlockTail::Value(Expr::If {
        then_branch,
        else_branch,
        ..
    }) = &body.tail
    else {
        panic!("expected If tail");
    };
    assert!(
        matches!(&then_branch.tail, BlockTail::Value(Expr::Var(v)) if v.as_ref() == "v"),
        "then-arm tail should stay the shadowed inner `v`"
    );
    assert!(
        matches!(&else_branch.tail, BlockTail::Value(Expr::Var(v)) if v.as_ref() == "x"),
        "else-arm tail should be substituted to `x`"
    );
}
