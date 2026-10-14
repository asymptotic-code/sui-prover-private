//! Hygiene tests for the substituter and the stage-6 sub-passes.
//!
//! Covers capture avoidance for `Quantifier::binder`,
//! `MatchArm::bindings`, and `Expr::While::iter_locals`. Each test
//! constructs a body where the would-be substitution location is
//! inside a scope that shadows the replacement's free vars, and
//! asserts the relevant inline op skips the inner scope.

use super::fixtures::*;
use crate::ir::{quant::QuantDomain, BlockTail, Expr, MatchArm, QuantifierKind, Stmt, Type};
use crate::stage_06_let_inline::copy_inline::copy_inline_once;
use crate::stage_06_let_inline::substitute::substitute_var;

#[test]
fn substitute_skips_capturing_match_arm() {
    // body: `match s { V0(y) => use(v) }` -- arm binds `y`.
    // Replacement is `Var(y)` -- capture hazard.
    let arm_body = block_value(vec![], call(7, vec![var("v")]));
    let mut body = block_value(
        vec![],
        Expr::Match {
            struct_id: 0,
            selector: Box::new(var("s")),
            cases: vec![MatchArm {
                variant: 0,
                bindings: vec![vid("y")],
                body: Box::new(arm_body),
            }],
        },
    );
    substitute_var(&mut body, &vid("v"), &var("y"));

    // The arm body's `Var(v)` should NOT be replaced (substitution
    // skipped due to `y` shadowing in the arm bindings).
    if let BlockTail::Value(Expr::Match { cases, .. }) = &body.tail {
        if let BlockTail::Value(Expr::Call { args, .. }) = &cases[0].body.tail {
            assert!(matches!(&args[0], Expr::Var(n) if n.as_ref() == "v"));
        } else {
            panic!("expected Call in arm body");
        }
    } else {
        panic!("expected Match tail");
    }
}

#[test]
fn substitute_descends_into_non_capturing_match_arm() {
    // body: `match s { V0(other) => use(v) }`. Replacement `Var(y)`,
    // arm binds `other` -- no collision.
    let arm_body = block_value(vec![], call(7, vec![var("v")]));
    let mut body = block_value(
        vec![],
        Expr::Match {
            struct_id: 0,
            selector: Box::new(var("s")),
            cases: vec![MatchArm {
                variant: 0,
                bindings: vec![vid("other")],
                body: Box::new(arm_body),
            }],
        },
    );
    substitute_var(&mut body, &vid("v"), &var("y"));

    if let BlockTail::Value(Expr::Match { cases, .. }) = &body.tail {
        if let BlockTail::Value(Expr::Call { args, .. }) = &cases[0].body.tail {
            assert!(matches!(&args[0], Expr::Var(n) if n.as_ref() == "y"));
        } else {
            panic!("expected Call in arm body");
        }
    } else {
        panic!("expected Match tail");
    }
}

#[test]
fn substitute_skips_capturing_while_iter_locals() {
    // body: `while_loop with iter_locals=[y] { use(v) }`.
    // Replacement is `Var(y)` -- capture hazard.
    let while_e = while_with_iter_locals(
        block_value(vec![], Expr::Unit),
        bool_const(true),
        block_continue(vec![Stmt::Eval(call(7, vec![var("v")]))], 0, Expr::Unit),
        vec![(vid("y"), Expr::Unit)],
    );
    let mut body = block_value(vec![Stmt::Eval(while_e)], Expr::Unit);
    substitute_var(&mut body, &vid("v"), &var("y"));

    // Find the inner Call inside the while body; its arg should
    // remain `Var(v)`.
    if let Stmt::Eval(Expr::While { body: wb, .. }) = &body.stmts[0] {
        if let Stmt::Eval(Expr::Call { args, .. }) = &wb.stmts[0] {
            assert!(matches!(&args[0], Expr::Var(n) if n.as_ref() == "v"));
        } else {
            panic!("expected Call in while body");
        }
    } else {
        panic!("expected Stmt::Eval(While)");
    }
}

#[test]
fn substitute_descends_into_non_capturing_while() {
    // body: `while_loop with iter_locals=[i] { use(v) }`.
    // Replacement is `Var(y)` -- no collision.
    let while_e = while_with_iter_locals(
        block_value(vec![], Expr::Unit),
        bool_const(true),
        block_continue(vec![Stmt::Eval(call(7, vec![var("v")]))], 0, Expr::Unit),
        vec![(vid("i"), Expr::Unit)],
    );
    let mut body = block_value(vec![Stmt::Eval(while_e)], Expr::Unit);
    substitute_var(&mut body, &vid("v"), &var("y"));

    if let Stmt::Eval(Expr::While { body: wb, .. }) = &body.stmts[0] {
        if let Stmt::Eval(Expr::Call { args, .. }) = &wb.stmts[0] {
            assert!(matches!(&args[0], Expr::Var(n) if n.as_ref() == "y"));
        } else {
            panic!("expected Call in while body");
        }
    } else {
        panic!("expected Stmt::Eval(While)");
    }
}

#[test]
fn copy_inline_respects_iter_locals_capture() {
    // body: `let v = Var(y); while iter_locals=[y] { use(v) }`.
    //
    // The Let triggers copy_inline. Substituting `v -> Var(y)` into
    // the while body would capture; copy_inline's substitute should
    // skip the body. The Let still drops; the body retains `Var(v)`
    // (broken — but the postcondition will catch it).
    let while_e = while_with_iter_locals(
        block_value(vec![], Expr::Unit),
        bool_const(true),
        block_continue(vec![Stmt::Eval(call(7, vec![var("v")]))], 0, Expr::Unit),
        vec![(vid("y"), Expr::Unit)],
    );
    let mut body = block_value(
        vec![let_stmt("v", var("y")), Stmt::Eval(while_e)],
        Expr::Unit,
    );
    let changed = copy_inline_once(&mut body);
    assert!(changed);
    // Let dropped.
    assert_eq!(body.stmts.len(), 1);
    // While body still has Var(v).
    if let Stmt::Eval(Expr::While { body: wb, .. }) = &body.stmts[0] {
        if let Stmt::Eval(Expr::Call { args, .. }) = &wb.stmts[0] {
            assert!(matches!(&args[0], Expr::Var(n) if n.as_ref() == "v"));
        } else {
            panic!("expected Call");
        }
    } else {
        panic!("expected While");
    }
}

#[test]
fn substitution_into_loop_state_payload_works() {
    // body: `let v = Var(y); while iter_locals=[i] {
    //   continue 0 carrying (v, i)
    // }`
    // -- v should be substituted to `Var(y)` inside the Continue
    // payload (no capture: iter_locals doesn't include `y`).
    let while_e = while_with_iter_locals(
        block_value(vec![], Expr::Unit),
        bool_const(true),
        block_continue(vec![], 0, tuple(vec![var("v"), var("i")])),
        vec![(vid("i"), Expr::Unit)],
    );
    let mut body = block_value(
        vec![let_stmt("v", var("y")), Stmt::Eval(while_e)],
        Expr::Unit,
    );
    let changed = copy_inline_once(&mut body);
    assert!(changed);
    if let Stmt::Eval(Expr::While { body: wb, .. }) = &body.stmts[0] {
        if let BlockTail::Continue { value, .. } = &wb.tail {
            if let Expr::Tuple(elems) = value.as_ref() {
                assert!(matches!(&elems[0], Expr::Var(n) if n.as_ref() == "y"));
                // `i` is the loop iter-local; it survives unchanged.
                assert!(matches!(&elems[1], Expr::Var(n) if n.as_ref() == "i"));
            } else {
                panic!("expected Tuple payload");
            }
        } else {
            panic!("expected Continue tail");
        }
    } else {
        panic!("expected While");
    }
}

#[test]
fn substitution_preserves_quantifier_binder() {
    // body: `forall i in 0..n, use(v)`. Replacing `v -> Var(i)` is
    // a capture hazard. Substitution skips the quantifier body.
    let q = Expr::Quantifier {
        kind: QuantifierKind::Forall,
        binder: vid("i"),
        binder_type: Type::UInt(64),
        domain: QuantDomain::Range {
            start: Box::new(u64_const(0)),
            end: Box::new(var("n")),
        },
        body: Box::new(block_value(vec![], call(7, vec![var("v")]))),
    };
    let mut body = block_value(vec![], q);
    substitute_var(&mut body, &vid("v"), &var("i"));

    if let BlockTail::Value(Expr::Quantifier { body: qbody, .. }) = &body.tail {
        if let BlockTail::Value(Expr::Call { args, .. }) = &qbody.tail {
            // `v` preserved (not replaced).
            assert!(matches!(&args[0], Expr::Var(n) if n.as_ref() == "v"));
        } else {
            panic!("expected Call in quantifier body");
        }
    } else {
        panic!("expected Quantifier tail");
    }
}
