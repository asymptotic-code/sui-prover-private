//! Postcondition validator tests.
//!
//! Each test constructs a deliberately-broken `Program` and asserts
//! the validator reports the right error variant.

use super::fixtures::*;
use crate::ir::{
    Expr, FunId, Function, FunctionKind, ModId, Module, Param, Program, Signature, Stmt, Type,
};
use crate::stage_06_let_inline::postcondition::{check, PostconditionError};
use crate::stage_06_let_inline::run;

fn singleton(body: crate::ir::Block) -> Program {
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
        name: "f".to_string(),
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
fn well_formed_post_run_output_passes() {
    let body = block_value(vec![], var("x"));
    let mut p = singleton(body);
    run(&mut p).expect("run");
    check(&p).expect("postcondition");
}

#[test]
fn identity_let_rejects() {
    let body = block_value(
        vec![Stmt::Let {
            pattern: vec![Some(vid("x"))],
            value: var("x"),
        }],
        var("x"),
    );
    let p = singleton(body);
    assert!(matches!(
        check(&p),
        Err(PostconditionError::IdentityLet { function: 0 })
    ));
}

#[test]
fn trivial_copy_let_rejects() {
    let body = block_value(
        vec![Stmt::Let {
            pattern: vec![Some(vid("a"))],
            value: var("x"),
        }],
        var("a"),
    );
    let p = singleton(body);
    assert!(matches!(
        check(&p),
        Err(PostconditionError::TrivialCopyLet { function: 0 })
    ));
}

#[test]
fn single_use_pure_total_let_rejects() {
    // `let a = s.f0; a`  -- single-use pure-total Field projection.
    let body = block_value(
        vec![Stmt::Let {
            pattern: vec![Some(vid("a"))],
            value: Expr::Field {
                struct_id: 0,
                field_index: 0,
                base: Box::new(var("x")),
            },
        }],
        var("a"),
    );
    // Need a struct registered so the validator passes (base validator runs first).
    let mut p = singleton(body);
    p.structs.insert(
        0,
        crate::ir::Struct {
            module_id: 0,
            name: "S".into(),
            qualified_name: "p::m::S".into(),
            type_params: Vec::new(),
            fields: vec![crate::ir::Field {
                name: "f0".into(),
                field_type: Type::UInt(64),
            }],
            variants: None,
            is_native: false,
        },
    );
    assert!(matches!(
        check(&p),
        Err(PostconditionError::SingleUsePureTotalLet { function: 0 })
    ));
}

#[test]
fn dead_pure_total_eval_rejects() {
    let body = block_value(vec![Stmt::Eval(u64_const(7))], var("x"));
    let p = singleton(body);
    assert!(matches!(
        check(&p),
        Err(PostconditionError::DeadPureTotalEval { function: 0 })
    ));
}

#[test]
fn native_function_skipped() {
    // Obsolete: natives now live in program.natives.decls, not
    // program.functions; stages walk only functions, so this
    // behavior is structurally guaranteed.
}
