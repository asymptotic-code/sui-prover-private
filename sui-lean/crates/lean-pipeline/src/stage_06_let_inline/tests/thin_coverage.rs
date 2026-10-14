//! Thin-coverage tests for sub-pass behaviour that the main suites
//! exercise indirectly.
//!
//! - Substitution into `BitOp` / `UpdateField` / `UpdateVec`.
//! - Use-counting inside `BitOp`.
//! - `SingleUsePureTotalLet` postcondition trigger on `Pack` and `Call`
//!   values (the existing test covers `Field`).
//! - Substitution through `Expr::While::iter_locals` init expressions.

use super::fixtures::*;
use crate::ir::{
    BitOp, BlockTail, Effects, Expr, FunId, Function, FunctionKind, ModId, Module, Param, Program,
    Signature, Stmt, Type, VarId,
};
use crate::stage_06_let_inline::postcondition::{check, PostconditionError};
use crate::stage_06_let_inline::substitute::substitute_var;
use crate::stage_06_let_inline::use_count::count_uses;

#[test]
fn substitute_into_bitop_extract() {
    // body: `BitOp::Extract { high: 8, low: 0, operand: Var(v) }`
    let mut body = block_value(
        vec![],
        Expr::BitOp(BitOp::Extract {
            high: 8,
            low: 0,
            operand: Box::new(var("v")),
        }),
    );
    substitute_var(&mut body, &vid("v"), &var("y"));
    if let BlockTail::Value(Expr::BitOp(BitOp::Extract { operand, .. })) = &body.tail {
        assert!(matches!(operand.as_ref(), Expr::Var(n) if n.as_ref() == "y"));
    } else {
        panic!("expected BitOp::Extract tail");
    }
}

#[test]
fn substitute_into_bitop_concat() {
    let mut body = block_value(
        vec![],
        Expr::BitOp(BitOp::Concat {
            high: Box::new(var("a")),
            low: Box::new(var("b")),
        }),
    );
    substitute_var(&mut body, &vid("a"), &var("a2"));
    substitute_var(&mut body, &vid("b"), &var("b2"));
    if let BlockTail::Value(Expr::BitOp(BitOp::Concat { high, low })) = &body.tail {
        assert!(matches!(high.as_ref(), Expr::Var(n) if n.as_ref() == "a2"));
        assert!(matches!(low.as_ref(), Expr::Var(n) if n.as_ref() == "b2"));
    } else {
        panic!("expected BitOp::Concat tail");
    }
}

#[test]
fn substitute_into_update_field() {
    let mut body = block_value(
        vec![],
        Expr::Update {
            step: crate::ir::path::PathStep::Field {
                struct_id: 7,
                field_index: 0,
            },
            base: Box::new(var("s")),
            value: Box::new(var("v")),
        },
    );
    substitute_var(&mut body, &vid("s"), &var("s2"));
    substitute_var(&mut body, &vid("v"), &var("v2"));
    if let BlockTail::Value(Expr::Update { base, value, .. }) = &body.tail {
        assert!(matches!(base.as_ref(), Expr::Var(n) if n.as_ref() == "s2"));
        assert!(matches!(value.as_ref(), Expr::Var(n) if n.as_ref() == "v2"));
    } else {
        panic!("expected UpdateField tail");
    }
}

#[test]
fn substitute_into_update_vec() {
    let mut body = block_value(
        vec![],
        Expr::Update {
            step: crate::ir::path::PathStep::VecIndex(Box::new(var("i"))),
            base: Box::new(var("vec")),
            value: Box::new(var("v")),
        },
    );
    substitute_var(&mut body, &vid("vec"), &var("vec2"));
    substitute_var(&mut body, &vid("i"), &var("i2"));
    substitute_var(&mut body, &vid("v"), &var("v2"));
    if let BlockTail::Value(Expr::Update {
        step: crate::ir::path::PathStep::VecIndex(index),
        base,
        value,
    }) = &body.tail
    {
        assert!(matches!(base.as_ref(), Expr::Var(n) if n.as_ref() == "vec2"));
        assert!(matches!(index.as_ref(), Expr::Var(n) if n.as_ref() == "i2"));
        assert!(matches!(value.as_ref(), Expr::Var(n) if n.as_ref() == "v2"));
    } else {
        panic!("expected UpdateVec tail");
    }
}

#[test]
fn use_count_walks_bitop() {
    let body = block_value(
        vec![],
        Expr::BitOp(BitOp::Concat {
            high: Box::new(var("a")),
            low: Box::new(var("a")),
        }),
    );
    let counts = count_uses(&body);
    assert_eq!(counts.get(&vid("a")), 2);
}

#[test]
fn postcondition_flags_single_use_pure_total_pack() {
    // `let p = Pack S { x }; p` -- pure-total single-use Pack.
    let pack = Expr::Pack {
        struct_id: 0,
        type_args: Vec::new(),
        variant: None,
        fields: vec![var("x")],
    };
    let body = block_value(
        vec![Stmt::Let {
            pattern: vec![Some(vid("p"))],
            value: pack,
        }],
        var("p"),
    );
    let mut p = singleton_with_struct(body);
    assert!(matches!(
        check(&p),
        Err(PostconditionError::SingleUsePureTotalLet { function: 0 })
    ));
    let _ = &mut p;
}

#[test]
fn postcondition_flags_single_use_pure_total_call() {
    // `let r = pure_call(); r` -- pure-total single-use Call.
    let callee = stub_callee("pure_call", Effects::PURE, Type::UInt(64));
    let body = block_value(
        vec![Stmt::Let {
            pattern: vec![Some(vid("r"))],
            value: call(7, vec![]),
        }],
        var("r"),
    );
    let mut p = singleton_no_struct(body);
    p.functions.insert(7 as FunId, callee);
    assert!(matches!(
        check(&p),
        Err(PostconditionError::SingleUsePureTotalLet { function: 0 })
    ));
}

#[test]
fn substitute_into_while_iter_local_init() {
    // body: `while iter_locals=[(i, Var(v))] { ... }`
    // Substituting `v -> Var(y)` should rewrite the init expression
    // (which evaluates in outer scope).
    let while_e = while_with_iter_locals(
        block_value(vec![], Expr::Unit),
        bool_const(true),
        block_continue(vec![], 0, Expr::Unit),
        vec![(vid("i"), var("v"))],
    );
    let mut body = block_value(vec![Stmt::Eval(while_e)], Expr::Unit);
    substitute_var(&mut body, &vid("v"), &var("y"));

    if let Stmt::Eval(Expr::While { iter_locals, .. }) = &body.stmts[0] {
        assert_eq!(iter_locals.len(), 1);
        assert!(matches!(&iter_locals[0].1, Expr::Var(n) if n.as_ref() == "y"));
    } else {
        panic!("expected While with iter_locals");
    }
}

#[test]
fn use_count_walks_while_iter_local_init() {
    // body: `while iter_locals=[(i, Var(init_var))] { Var(i) }`
    // `init_var` is in outer scope (counted); `i` shadows inside the
    // body (NOT counted).
    let while_e = while_with_iter_locals(
        block_value(vec![], Expr::Unit),
        bool_const(true),
        block_continue(vec![], 0, var("i")),
        vec![(vid("i"), var("init_var"))],
    );
    let body = block_value(vec![Stmt::Eval(while_e)], Expr::Unit);
    let counts = count_uses(&body);
    assert_eq!(counts.get(&vid("init_var")), 1);
    assert_eq!(counts.get(&vid("i")), 0);
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn singleton_with_struct(body: crate::ir::Block) -> Program {
    let mut p = singleton_no_struct(body);
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
    p
}

fn singleton_no_struct(body: crate::ir::Block) -> Program {
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
                var: VarId::from("x"),
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
