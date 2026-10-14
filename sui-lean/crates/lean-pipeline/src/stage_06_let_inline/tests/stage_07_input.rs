//! Cross-stage handoff: after stage 6 runs, the output meets the
//! shape stage 7 (rewrite) expects.
//!
//! Asserts that stage 6's postcondition passes on representative
//! inputs -- the contract stage 7's `.aborts`-variant materialiser
//! relies on.

use super::fixtures::*;
use crate::ir::{
    Effects, FunId, Function, FunctionKind, ModId, Module, Param, Program, Signature, Stmt, Type,
};
use crate::stage_06_let_inline::{postcondition::check, run};

fn caller_with(body: crate::ir::Block) -> Program {
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
        name: "caller".to_string(),
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
fn copy_chain_postcondition_clean_after_run() {
    let body = block_value(
        vec![
            let_stmt("a", var("x")),
            let_stmt("b", var("a")),
            let_stmt("c", var("b")),
        ],
        var("c"),
    );
    let mut p = caller_with(body);
    run(&mut p).expect("run");
    check(&p).expect("stage-6 postcondition holds");
}

#[test]
fn arithmetic_body_postcondition_clean_after_run() {
    // `let a = b + c; a` -- arithmetic is partial, won't inline. The
    // body survives unchanged through run() with a single Let. The
    // postcondition accepts it (it's not pure-total).
    let body = block_value(vec![let_stmt("a", add(var("x"), var("x")))], var("a"));
    let mut p = caller_with(body);
    run(&mut p).expect("run");
    check(&p).expect("stage-6 postcondition holds");
}

#[test]
fn impure_call_eval_postcondition_clean_after_run() {
    // `eval(imp()); 0` -- impure eval survives; postcondition fine.
    let callee = stub_callee("imp", Effects::CONSERVATIVE, Type::Unit);
    let body = block_value(vec![Stmt::Eval(call(7, vec![]))], u64_const(0));
    let mut p = caller_with(body);
    p.functions.insert(7 as FunId, callee);
    run(&mut p).expect("run");
    check(&p).expect("stage-6 postcondition holds");
}
