//! `partial_fixpoint` loop bodies: a `match` on a let-bound local is selected
//! by the bound value (hashi `mpc_signing::to_signatures`).

use crate::ir::{Block, BlockTail, Expr, Stmt, Type, VarId};
use crate::render::function::{select_let_bound_match_values, self_calls_only_in_tail_position};

use super::fixtures::*;

fn call(fun: crate::ir::FunId) -> Expr {
    Expr::Call {
        fun,
        type_args: vec![],
        args: vec![var("xs")],
    }
}

fn loop_body(scrutinee: Expr) -> Block {
    Block {
        stmts: vec![Stmt::Let {
            pattern: vec![Some(VarId::from("s"))],
            value: scrutinee,
        }],
        tail: BlockTail::Value(Expr::Match {
            struct_id: 0,
            selector: Box::new(var("s")),
            cases: vec![],
        }),
    }
}

fn program() -> crate::ir::Program {
    let mut program = empty_program();
    add_function(
        &mut program,
        1,
        func(
            "borrow",
            sig(vec![param("xs", Type::Bool)], Type::Bool),
            body(vec![], Expr::Unit),
            0,
        ),
    );
    add_function(
        &mut program,
        2,
        func(
            "f.while_0",
            sig(vec![param("xs", Type::Bool)], Type::Bool),
            body(vec![], Expr::Unit),
            0,
        ),
    );
    program
}

fn selector(block: &Block) -> &Expr {
    match &block.tail {
        BlockTail::Value(Expr::Match { selector, .. }) => selector,
        other => panic!("not a match tail: {other:?}"),
    }
}

#[test]
fn a_let_bound_scrutinee_is_selected_by_its_value_and_the_let_is_kept() {
    let mut body = loop_body(call(1));
    select_let_bound_match_values(&mut body, 0, "f.while_0", &program());

    assert_eq!(selector(&body), &call(1));
    assert_eq!(body.stmts.len(), 1, "later uses of `s` still need the let");
}

#[test]
fn a_scrutinee_that_recurses_is_left_alone() {
    let mut body = loop_body(call(2));
    select_let_bound_match_values(&mut body, 0, "f.while_0", &program());

    assert_eq!(selector(&body), &var("s"));
}

fn tail_position(block: &Block) -> bool {
    self_calls_only_in_tail_position(block, &0, "f.while_0", &program())
}

fn branch(then_tail: Expr) -> Expr {
    Expr::If {
        cond: Box::new(var("xs")),
        then_branch: Box::new(body(vec![], then_tail)),
        else_branch: Box::new(body(vec![], var("xs"))),
    }
}

// `partial_fixpoint` only eliminates a tail-position recursive call. deepbook
// `fixed_math::math::ln` negates its own result and `strike_payout_tree::
// take_min` matches on it; both were emitted as fixpoints and rejected.
#[test]
fn a_self_call_is_tail_position_only_as_the_whole_value_of_a_tail() {
    assert!(tail_position(&body(vec![], call(2))));
    assert!(tail_position(&body(vec![], branch(call(2)))));
    assert!(tail_position(&body(vec![], call(1))), "no self-call at all");

    let consumed = Expr::Call {
        fun: 1,
        type_args: vec![],
        args: vec![call(2)],
    };
    assert!(!tail_position(&body(vec![], consumed.clone())));
    assert!(!tail_position(&body(vec![], branch(consumed))));
    assert!(
        !tail_position(&loop_body(call(2))),
        "a let-bound recursive result is consumed by what follows"
    );
    let in_condition = Expr::If {
        cond: Box::new(call(2)),
        then_branch: Box::new(body(vec![], var("xs"))),
        else_branch: Box::new(body(vec![], var("xs"))),
    };
    assert!(!tail_position(&body(vec![], in_condition)));
}

fn bind(name: &str, value: Expr) -> Stmt {
    Stmt::Let {
        pattern: vec![Some(VarId::from(name))],
        value,
    }
}

// priority_queue `max_heapify_recursive` lowers to
// `let t := if c then (let r := <rec>; r) else v; (t)`; refusing it downgraded
// the function to an opaque `partial def` with no `.eq_def`.
#[test]
fn a_let_bound_result_returned_as_is_stays_in_tail_position() {
    assert!(tail_position(&body(vec![bind("r", call(2))], var("r"))));

    let then_forwards = Expr::If {
        cond: Box::new(var("xs")),
        then_branch: Box::new(body(vec![bind("r", call(2))], var("r"))),
        else_branch: Box::new(body(vec![], var("xs"))),
    };
    assert!(tail_position(&body(
        vec![bind("t", then_forwards)],
        Expr::Tuple(vec![var("t")])
    )));
    assert!(tail_position(&body(vec![], Expr::Tuple(vec![call(2)]))));

    assert!(
        !tail_position(&body(vec![bind("r", call(2))], var("xs"))),
        "the recursive result is discarded, not returned"
    );
    assert!(
        !tail_position(&body(
            vec![bind("r", call(2))],
            Expr::Tuple(vec![var("r"), var("xs")])
        )),
        "a pair holding the recursive result is not the result"
    );
    let consumed = Expr::Call {
        fun: 1,
        type_args: vec![],
        args: vec![var("r")],
    };
    assert!(!tail_position(&body(vec![bind("r", call(2))], consumed)));
    let destructured = Stmt::Let {
        pattern: vec![Some(VarId::from("r")), Some(VarId::from("w"))],
        value: call(2),
    };
    assert!(
        !tail_position(&body(vec![destructured], var("r"))),
        "returning one component of a destructured result consumes it"
    );
}
