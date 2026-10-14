//! Phase 4 §11 unit tests for body-tail rewriting.

use crate::ir::builder::{lit_u64, var};
use crate::ir::{Block, BlockTail, Expr, Type, VarId};
use crate::stage_03_demut::{compute_demotion_map, rewrite_body_tails};

use super::fixtures::{func, mut_ref, param, program_with, sig, FuncOpts};

fn t() -> Type {
    Type::UInt(64)
}

fn vid(name: &str) -> VarId {
    VarId::from(name)
}

#[test]
fn standard_one_mut_unit_tail_becomes_var_p() {
    // f(x: &mut T): ()  body { return }
    // After: tail = Value(Var(x))
    let body = Block {
        stmts: Vec::new(),
        tail: BlockTail::Value(Expr::Unit),
    };
    let f = func(
        "f",
        sig(vec![param("x", mut_ref(t(), t()))], Type::Unit),
        body,
        FuncOpts::default(),
    );
    let mut prog = program_with(vec![(0, f)]);
    let demotion = compute_demotion_map(&prog);
    rewrite_body_tails(&mut prog, &demotion);

    match &prog.functions[&0].body.tail {
        BlockTail::Value(Expr::Var(name)) => assert_eq!(name, &vid("x")),
        other => panic!("expected Value(Var(x)), got {:?}", other),
    }
}

#[test]
fn standard_two_mut_unit_tail_becomes_tuple() {
    // f(x: &mut T, y: &mut T): ()  body { return }
    // After: tail = Value(Tuple([Var(x), Var(y)]))
    let body = Block {
        stmts: Vec::new(),
        tail: BlockTail::Value(Expr::Unit),
    };
    let f = func(
        "f",
        sig(
            vec![param("x", mut_ref(t(), t())), param("y", mut_ref(t(), t()))],
            Type::Unit,
        ),
        body,
        FuncOpts::default(),
    );
    let mut prog = program_with(vec![(0, f)]);
    let demotion = compute_demotion_map(&prog);
    rewrite_body_tails(&mut prog, &demotion);

    match &prog.functions[&0].body.tail {
        BlockTail::Value(Expr::Tuple(items)) => {
            assert_eq!(items, &vec![var("x"), var("y")]);
        }
        other => panic!("expected Value(Tuple), got {:?}", other),
    }
}

#[test]
fn standard_one_mut_simple_return_wraps_in_tuple() {
    // f(x: &mut T): u64  body { return 42 }
    // After: tail = Value(Tuple([42, Var(x)]))
    let body = Block {
        stmts: Vec::new(),
        tail: BlockTail::Value(lit_u64(42)),
    };
    let f = func(
        "f",
        sig(vec![param("x", mut_ref(t(), t()))], t()),
        body,
        FuncOpts::default(),
    );
    let mut prog = program_with(vec![(0, f)]);
    let demotion = compute_demotion_map(&prog);
    rewrite_body_tails(&mut prog, &demotion);

    match &prog.functions[&0].body.tail {
        BlockTail::Value(Expr::Tuple(items)) => {
            assert_eq!(items, &vec![lit_u64(42), var("x")]);
        }
        other => panic!("expected Value(Tuple), got {:?}", other),
    }
}

#[test]
fn standard_one_mut_tuple_return_flattens() {
    // f(x: &mut T): (T, T)  body { return (a, b) }
    // After: tail = Value(Tuple([a, b, Var(x)]))
    let body = Block {
        stmts: Vec::new(),
        tail: BlockTail::Value(Expr::Tuple(vec![var("a"), var("b")])),
    };
    let f = func(
        "f",
        sig(
            vec![param("x", mut_ref(t(), t()))],
            Type::Tuple(vec![t(), t()]),
        ),
        body,
        FuncOpts::default(),
    );
    let mut prog = program_with(vec![(0, f)]);
    let demotion = compute_demotion_map(&prog);
    rewrite_body_tails(&mut prog, &demotion);

    match &prog.functions[&0].body.tail {
        BlockTail::Value(Expr::Tuple(items)) => {
            assert_eq!(items, &vec![var("a"), var("b"), var("x")]);
        }
        other => panic!("expected Value(Tuple), got {:?}", other),
    }
}

#[test]
fn pattern_4a_self_return_tail_unchanged() {
    // f(x: &mut T): &mut T  body { x }
    // After: tail still Value(Var(x)).
    let body = Block {
        stmts: Vec::new(),
        tail: BlockTail::Value(var("x")),
    };
    let f = func(
        "f",
        sig(vec![param("x", mut_ref(t(), t()))], mut_ref(t(), t())),
        body,
        FuncOpts::default(),
    );
    let mut prog = program_with(vec![(0, f)]);
    let demotion = compute_demotion_map(&prog);
    rewrite_body_tails(&mut prog, &demotion);

    match &prog.functions[&0].body.tail {
        BlockTail::Value(Expr::Var(name)) => assert_eq!(name, &vid("x")),
        other => panic!("expected Value(Var(x)), got {:?}", other),
    }
}

#[test]
fn pattern_4b_sub_field_tail_unchanged() {
    // f(x: &mut Outer): &mut Inner  body { BorrowField(...) }
    // After: tail unchanged.
    let original_tail = BlockTail::Value(Expr::Borrow {
        step: crate::ir::path::PathStep::Field {
            struct_id: 0,
            field_index: 0,
        },
        base: Box::new(var("x")),
    });
    let body = Block {
        stmts: Vec::new(),
        tail: original_tail.clone(),
    };
    let f = func(
        "f",
        sig(vec![param("x", mut_ref(t(), t()))], mut_ref(t(), t())),
        body,
        FuncOpts::default(),
    );
    let mut prog = program_with(vec![(0, f)]);
    let demotion = compute_demotion_map(&prog);
    rewrite_body_tails(&mut prog, &demotion);
    assert_eq!(prog.functions[&0].body.tail, original_tail);
}

#[test]
fn no_mut_function_tail_unchanged() {
    // f(x: T): T  body { x }
    let original_tail = BlockTail::Value(var("x"));
    let body = Block {
        stmts: Vec::new(),
        tail: original_tail.clone(),
    };
    let f = func(
        "f",
        sig(vec![param("x", t())], t()),
        body,
        FuncOpts::default(),
    );
    let mut prog = program_with(vec![(0, f)]);
    let demotion = compute_demotion_map(&prog);
    rewrite_body_tails(&mut prog, &demotion);
    assert_eq!(prog.functions[&0].body.tail, original_tail);
}
