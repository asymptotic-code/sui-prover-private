//! Phase 3 unit tests for call-site rewriting.

use crate::ir::builder::var;
use crate::ir::{Block, BlockTail, Expr, Stmt, Type, VarId};
use crate::stage_03_demut::{compute_demotion_map, rewrite_calls};

use super::fixtures::{empty_body, func, mut_ref, param, program_with, sig, FuncOpts};

fn t() -> Type {
    Type::UInt(64)
}

fn r() -> Type {
    Type::Bool
}

/// Build a simple Call expression.
fn call(fid: crate::ir::FunId, args: Vec<Expr>) -> Expr {
    Expr::Call {
        fun: fid,
        type_args: Vec::new(),
        args,
    }
}

fn vid(name: &str) -> VarId {
    VarId::from(name)
}

#[test]
fn one_mut_unit_return_eval_becomes_let_arg() {
    // Caller: Stmt::Eval(g(Var(arg)))  where g(arg: &mut T): ()
    // Demoted g returns T; caller destructure: let arg = g(Var(arg)).
    let g = func(
        "g",
        sig(vec![param("x", mut_ref(t(), t()))], Type::Unit),
        empty_body(),
        FuncOpts::default(),
    );
    let caller_body = Block {
        stmts: vec![Stmt::Eval(call(0, vec![var("arg")]))],
        tail: BlockTail::Value(Expr::Unit),
    };
    let caller = func(
        "caller",
        sig(vec![param("arg", mut_ref(t(), t()))], Type::Unit),
        caller_body,
        FuncOpts::default(),
    );

    let mut prog = program_with(vec![(0, g), (1, caller)]);
    let demotion = compute_demotion_map(&prog);
    rewrite_calls(&mut prog, &demotion);

    let body = &prog.functions[&1].body;
    assert_eq!(body.stmts.len(), 1);
    match &body.stmts[0] {
        Stmt::Let { pattern, value } => {
            assert_eq!(pattern, &vec![Some(vid("arg"))]);
            assert!(matches!(value, Expr::Call { .. }));
        }
        other => panic!("expected Stmt::Let, got {:?}", other),
    }
}

#[test]
fn one_mut_simple_return_let_pattern_extends() {
    // Caller: let result = g(Var(arg))  where g(arg: &mut T): R
    // Demoted g returns (R, T); destructure: let (result, arg) = g(...).
    let g = func(
        "g",
        sig(vec![param("x", mut_ref(t(), t()))], r()),
        empty_body(),
        FuncOpts::default(),
    );
    let caller_body = Block {
        stmts: vec![Stmt::Let {
            pattern: vec![Some(vid("result"))],
            value: call(0, vec![var("arg")]),
        }],
        tail: BlockTail::Value(Expr::Unit),
    };
    let caller = func(
        "caller",
        sig(vec![param("arg", mut_ref(t(), t()))], Type::Unit),
        caller_body,
        FuncOpts::default(),
    );

    let mut prog = program_with(vec![(0, g), (1, caller)]);
    let demotion = compute_demotion_map(&prog);
    rewrite_calls(&mut prog, &demotion);

    let body = &prog.functions[&1].body;
    match &body.stmts[0] {
        Stmt::Let { pattern, .. } => {
            assert_eq!(pattern, &vec![Some(vid("result")), Some(vid("arg"))]);
        }
        other => panic!("expected Stmt::Let, got {:?}", other),
    }
}

#[test]
fn two_mut_unit_eval_becomes_let_pair() {
    // Caller: Eval(g(Var(a), Var(b)))  where g(a: &mut T, b: &mut U): ()
    // Demoted g returns (T, U); destructure: let (a, b) = g(...).
    let g = func(
        "g",
        sig(
            vec![param("x", mut_ref(t(), t())), param("y", mut_ref(r(), r()))],
            Type::Unit,
        ),
        empty_body(),
        FuncOpts::default(),
    );
    let caller_body = Block {
        stmts: vec![Stmt::Eval(call(0, vec![var("a"), var("b")]))],
        tail: BlockTail::Value(Expr::Unit),
    };
    let caller = func(
        "caller",
        sig(
            vec![param("a", mut_ref(t(), t())), param("b", mut_ref(r(), r()))],
            Type::Unit,
        ),
        caller_body,
        FuncOpts::default(),
    );

    let mut prog = program_with(vec![(0, g), (1, caller)]);
    let demotion = compute_demotion_map(&prog);
    rewrite_calls(&mut prog, &demotion);

    let body = &prog.functions[&1].body;
    match &body.stmts[0] {
        Stmt::Let { pattern, .. } => {
            assert_eq!(pattern, &vec![Some(vid("a")), Some(vid("b"))]);
        }
        other => panic!("expected Stmt::Let, got {:?}", other),
    }
}

#[test]
fn mixed_mut_and_value_args_only_rebinds_mut_slots() {
    // g(plain: T, m: &mut U): R   demoted to (plain: T, m: U): (R, U)
    // Caller: let result = g(Var(p), Var(m))  becomes  let (result, m) = g(...).
    let g = func(
        "g",
        sig(
            vec![param("p", t()), param("m", mut_ref(r(), r()))],
            Type::Address,
        ),
        empty_body(),
        FuncOpts::default(),
    );
    let caller_body = Block {
        stmts: vec![Stmt::Let {
            pattern: vec![Some(vid("result"))],
            value: call(0, vec![var("p"), var("m")]),
        }],
        tail: BlockTail::Value(Expr::Unit),
    };
    let caller = func(
        "caller",
        sig(vec![param("m", mut_ref(r(), r()))], Type::Unit),
        caller_body,
        FuncOpts::default(),
    );

    let mut prog = program_with(vec![(0, g), (1, caller)]);
    let demotion = compute_demotion_map(&prog);
    rewrite_calls(&mut prog, &demotion);

    let body = &prog.functions[&1].body;
    match &body.stmts[0] {
        Stmt::Let { pattern, .. } => {
            // p is NOT rebound; only m.
            assert_eq!(pattern, &vec![Some(vid("result")), Some(vid("m"))]);
        }
        other => panic!("expected Stmt::Let, got {:?}", other),
    }
}

#[test]
fn call_inside_if_arm_is_rewritten() {
    // Caller body has `Stmt::Eval(If { ... <Eval(Call(g, [Var(arg)])) inside then> ... })`.
    let g = func(
        "g",
        sig(vec![param("x", mut_ref(t(), t()))], Type::Unit),
        empty_body(),
        FuncOpts::default(),
    );

    let then_block = Block {
        stmts: vec![Stmt::Eval(call(0, vec![var("arg")]))],
        tail: BlockTail::Value(Expr::Unit),
    };
    let else_block = Block {
        stmts: Vec::new(),
        tail: BlockTail::Value(Expr::Unit),
    };
    let if_expr = Expr::If {
        cond: Box::new(Expr::Const(crate::ir::Const::Bool(true))),
        then_branch: Box::new(then_block),
        else_branch: Box::new(else_block),
    };
    let caller_body = Block {
        stmts: vec![Stmt::Eval(if_expr)],
        tail: BlockTail::Value(Expr::Unit),
    };
    let caller = func(
        "caller",
        sig(vec![param("arg", mut_ref(t(), t()))], Type::Unit),
        caller_body,
        FuncOpts::default(),
    );

    let mut prog = program_with(vec![(0, g), (1, caller)]);
    let demotion = compute_demotion_map(&prog);
    rewrite_calls(&mut prog, &demotion);

    let body = &prog.functions[&1].body;
    match &body.stmts[0] {
        Stmt::Eval(Expr::If { then_branch, .. }) => match &then_branch.stmts[0] {
            Stmt::Let { pattern, .. } => {
                assert_eq!(pattern, &vec![Some(vid("arg"))]);
            }
            other => panic!("expected then-arm Stmt::Let, got {:?}", other),
        },
        other => panic!("expected Eval(If), got {:?}", other),
    }
}

#[test]
fn pattern_4b_call_site_is_unchanged() {
    // borrow_field(x: &mut Outer): &mut Inner -- pattern 4b.
    // Caller: let r = borrow_field(Var(x))  stays unchanged.
    let outer = t();
    let inner = r();

    // 4b body: tail is a borrow chain (BorrowField off the param).
    let body_4b = Block {
        stmts: Vec::new(),
        tail: BlockTail::Value(Expr::Borrow {
            step: crate::ir::path::PathStep::Field {
                struct_id: 0,
                field_index: 0,
            },
            base: Box::new(var("x")),
        }),
    };
    let g = func(
        "borrow_field",
        sig(
            vec![param("x", mut_ref(outer.clone(), outer.clone()))],
            mut_ref(inner.clone(), outer.clone()),
        ),
        body_4b,
        FuncOpts::default(),
    );

    let original_call_stmt = Stmt::Let {
        pattern: vec![Some(vid("r"))],
        value: call(0, vec![var("arg")]),
    };
    let caller_body = Block {
        stmts: vec![original_call_stmt.clone()],
        tail: BlockTail::Value(Expr::Unit),
    };
    let caller = func(
        "caller",
        sig(
            vec![param("arg", mut_ref(outer.clone(), outer.clone()))],
            Type::Unit,
        ),
        caller_body,
        FuncOpts::default(),
    );

    let mut prog = program_with(vec![(0, g), (1, caller)]);
    let demotion = compute_demotion_map(&prog);
    rewrite_calls(&mut prog, &demotion);

    let body = &prog.functions[&1].body;
    assert_eq!(
        body.stmts[0], original_call_stmt,
        "4b call site should be unchanged"
    );
}

#[test]
fn non_demoted_call_is_unchanged() {
    let g = func(
        "g",
        sig(vec![param("x", t())], r()),
        empty_body(),
        FuncOpts::default(),
    );
    let original_stmt = Stmt::Let {
        pattern: vec![Some(vid("result"))],
        value: call(0, vec![var("y")]),
    };
    let caller_body = Block {
        stmts: vec![original_stmt.clone()],
        tail: BlockTail::Value(Expr::Unit),
    };
    let caller = func(
        "caller",
        sig(vec![param("y", t())], Type::Unit),
        caller_body,
        FuncOpts::default(),
    );

    let mut prog = program_with(vec![(0, g), (1, caller)]);
    let demotion = compute_demotion_map(&prog);
    rewrite_calls(&mut prog, &demotion);

    let body = &prog.functions[&1].body;
    assert_eq!(body.stmts[0], original_stmt);
}
