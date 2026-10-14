//! Call dispatch through `Function::effects` -- end-to-end via `run()`.
//!
//! Stage 2's `classify_effects` pre-pass classifies every Function;
//! stage 6 consumes that classification to decide which Calls
//! inline. These tests exercise the wiring without depending on
//! stage 2 actually having run.

use super::fixtures::*;
use crate::ir::{
    AbortBit, BlockTail, DetBit, Effects, Expr, FunId, Function, FunctionKind, ModId, Module,
    MutLevel, Param, Program, Signature, Stmt, Type,
};
use crate::stage_06_let_inline::run;

fn program_with_caller_and_callee(callee_effects: Effects) -> Program {
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
    // Callee: id 7, the classified effects, native (so stage 6 skips
    // its body). Returns u64.
    let callee = stub_callee("callee", callee_effects, Type::UInt(64));
    p.functions.insert(7 as FunId, callee);

    // Caller: `let a = callee(); a` -- single use, body would inline
    // iff callee is Effects::PURE.
    let caller_body = block_value(
        vec![Stmt::Let {
            pattern: vec![Some(vid("a"))],
            value: call(7, vec![]),
        }],
        var("a"),
    );
    let caller = Function {
        module: 0,
        name: "caller".to_string(),
        signature: Signature {
            type_params: Vec::new(),
            params: Vec::new(),
            return_type: Type::UInt(64),
        },
        body: caller_body,
        kind: FunctionKind::Source,
        effects: callee_effects,
        explicit_pure: false,
    };
    p.functions.insert(0 as FunId, caller);
    p
}

#[test]
fn pure_total_callee_inlines_single_use() {
    let mut p = program_with_caller_and_callee(Effects::PURE);
    run(&mut p).expect("run");
    let caller = &p.functions[&0];
    // Let dropped, tail is the call expression directly.
    assert_eq!(caller.body.stmts.len(), 0);
    assert!(matches!(
        &caller.body.tail,
        BlockTail::Value(Expr::Call { fun: 7, .. })
    ));
}

#[test]
fn pure_partial_callee_does_not_inline() {
    let mut p = program_with_caller_and_callee(Effects {
        aborts: AbortBit::Partial,
        det: DetBit::Det,
        mutation: MutLevel::NoMut,
        world_writes: false,
    });
    run(&mut p).expect("run");
    let caller = &p.functions[&0];
    assert_eq!(caller.body.stmts.len(), 1);
}

#[test]
fn impure_callee_does_not_inline() {
    let mut p = program_with_caller_and_callee(Effects::CONSERVATIVE);
    run(&mut p).expect("run");
    let caller = &p.functions[&0];
    assert_eq!(caller.body.stmts.len(), 1);
}

#[test]
fn pure_total_call_in_eval_position_is_dropped() {
    // `eval(pure_call()); 0`  -- pure-total eval drops.
    let callee = stub_callee("pure_call", Effects::PURE, Type::Unit);
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
    p.functions.insert(7 as FunId, callee);

    let body = block_value(vec![Stmt::Eval(call(7, vec![]))], u64_const(0));
    let caller = Function {
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
    p.functions.insert(0 as FunId, caller);

    run(&mut p).expect("run");
    let caller = &p.functions[&0];
    assert_eq!(caller.body.stmts.len(), 0);
}

#[test]
fn impure_call_in_eval_position_is_kept() {
    let callee = stub_callee("imp", Effects::CONSERVATIVE, Type::Unit);
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
    p.functions.insert(7 as FunId, callee);

    let body = block_value(vec![Stmt::Eval(call(7, vec![]))], u64_const(0));
    let caller = Function {
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
        effects: crate::ir::Effects::CONSERVATIVE,
        explicit_pure: false,
    };
    p.functions.insert(0 as FunId, caller);

    run(&mut p).expect("run");
    let caller = &p.functions[&0];
    assert_eq!(caller.body.stmts.len(), 1);
    assert!(matches!(&caller.body.stmts[0], Stmt::Eval(_)));
}
