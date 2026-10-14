//! End-to-end tests for the stage-6 fixpoint driver.
//!
//! Exercises `run()` against representative inputs. The individual
//! sub-pass tests pin behaviour; these tests pin convergence,
//! determinism, and idempotency.

use super::fixtures::*;
use crate::ir::{
    BlockTail, Expr, FunId, Function, FunctionKind, ModId, Module, Param, Program, Signature, Stmt,
    Type,
};
use crate::stage_06_let_inline::run;

fn singleton_program(body: crate::ir::Block) -> Program {
    let mut p = Program::default();
    p.modules.insert(
        0 as ModId,
        Module {
            name: "m".to_string(),
            package_name: "p".to_string(),
            address: String::new(),
            required_imports: Vec::new(),
            is_native: false,
        },
    );
    let f = Function {
        module: 0,
        name: "test_fn".to_string(),
        signature: Signature {
            type_params: Vec::new(),
            params: vec![Param {
                name: "x".to_string(),
                var: vid("x"),
                ty: Type::UInt(64),
            }],
            return_type: Type::UInt(64),
        },
        body,
        kind: FunctionKind::Source,
        effects: crate::ir::Effects::PURE,
        explicit_pure: false,
    };
    p.functions.insert(0 as FunId, f);
    p
}

#[test]
fn end_to_end_copy_chain_collapses_fully() {
    // `let a = x; let b = a; let c = b; c`  ->  `x`
    let body = block_value(
        vec![
            let_stmt("a", var("x")),
            let_stmt("b", var("a")),
            let_stmt("c", var("b")),
        ],
        var("c"),
    );
    let mut program = singleton_program(body);
    run(&mut program).expect("stage 6 run");
    let f = &program.functions[&0];
    assert_eq!(f.body.stmts.len(), 0);
    assert!(matches!(&f.body.tail, BlockTail::Value(Expr::Var(v)) if v.as_ref() == "x"));
}

#[test]
fn end_to_end_dead_let_and_eval_dropped() {
    // `let a = x; eval(7); a` -> the eval drops; `let a = x` collapses
    // to `x`.
    let body = block_value(
        vec![let_stmt("a", var("x")), Stmt::Eval(u64_const(7))],
        var("a"),
    );
    let mut program = singleton_program(body);
    run(&mut program).expect("stage 6 run");
    let f = &program.functions[&0];
    assert_eq!(f.body.stmts.len(), 0);
    assert!(matches!(&f.body.tail, BlockTail::Value(Expr::Var(v)) if v.as_ref() == "x"));
}

#[test]
fn idempotent_on_clean_input() {
    // `x` -- no stmts, just a tail. Stage 6 has nothing to do.
    let body = block_value(vec![], var("x"));
    let mut program = singleton_program(body);
    run(&mut program).expect("first run");
    let snapshot = program.clone();
    run(&mut program).expect("second run");
    assert_eq!(program.functions, snapshot.functions);
}

#[test]
fn idempotent_on_non_clean_input() {
    // Convergent body; run twice and assert byte-identical.
    let body = block_value(
        vec![let_stmt("a", var("x")), let_stmt("b", var("a"))],
        var("b"),
    );
    let mut program = singleton_program(body);
    run(&mut program).expect("first run");
    let snapshot = program.clone();
    run(&mut program).expect("second run");
    assert_eq!(program.functions, snapshot.functions);
}

#[test]
fn deterministic_byte_identical_output() {
    // Construct two identical programs; run stage 6 on each;
    // assert the post-state matches exactly.
    let body1 = block_value(
        vec![let_stmt("a", var("x")), let_stmt("b", var("a"))],
        var("b"),
    );
    let body2 = body1.clone();
    let mut p1 = singleton_program(body1);
    let mut p2 = singleton_program(body2);
    run(&mut p1).expect("p1 run");
    run(&mut p2).expect("p2 run");
    assert_eq!(p1.functions, p2.functions);
}

#[test]
fn native_function_body_left_untouched() {
    // Obsolete: natives now live in program.natives.decls, not
    // program.functions; stages walk only functions, so this
    // behavior is structurally guaranteed.
}

#[test]
fn run_on_empty_program_succeeds() {
    let mut p = Program::default();
    p.modules.insert(
        0 as ModId,
        Module {
            name: "m".to_string(),
            package_name: "p".to_string(),
            address: String::new(),
            required_imports: Vec::new(),
            is_native: false,
        },
    );
    let res = run(&mut p);
    assert!(matches!(res, Ok(())));
}

#[test]
fn fixpoint_converges_quickly_on_synthetic_chain() {
    // A 20-long copy chain should converge in well under FIXPOINT_LIMIT
    // iterations.
    let mut stmts: Vec<Stmt> = Vec::new();
    let chain: Vec<String> = (0..20).map(|i| format!("v_{}", i)).collect();
    // Start from `x`.
    stmts.push(let_stmt(&chain[0], var("x")));
    for i in 1..chain.len() {
        stmts.push(let_stmt(&chain[i], var(&chain[i - 1])));
    }
    let last = chain.last().unwrap().clone();
    let body = block_value(stmts, var(&last));
    let mut program = singleton_program(body);
    run(&mut program).expect("converges");
    let f = &program.functions[&0];
    assert_eq!(f.body.stmts.len(), 0);
    assert!(matches!(&f.body.tail, BlockTail::Value(Expr::Var(v)) if v.as_ref() == "x"));
}

fn var(s: &str) -> Expr {
    super::fixtures::var(s)
}
