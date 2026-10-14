//! Phase 2 fixtures for Rewrite 3 (strip residual Type::MutableRef).
//!
//! Stage 3 already stripped `&mut` from parameters. This stage cleans
//! up:
//! - Return types of non-pattern-4b functions.
//! - `Call::type_args` and `Pack::type_args` in expressions.
//! - `Quantifier::binder_type`.
//!
//! Pattern-4b function return types are preserved (`MutableRef`
//! stays).

use crate::ir::{
    builder::{block, just, tail_value},
    Expr, Param, QuantDomain, QuantifierKind, Stmt, Type, VarId,
};
use crate::stage_04_erase_mut::strip_mutable_ref_types;

use super::fixtures::*;

const STRUCT_S: usize = 7;

fn one_fn_program_with_return(
    body_block: crate::ir::Block,
    ret: Type,
    extra_params: Vec<Param>,
) -> crate::ir::Program {
    let f = func("f", sig(extra_params, ret), body_block, FuncOpts::default());
    program_with(vec![(0, f)])
}

#[test]
fn return_type_mutable_ref_stripped_when_tail_is_var() {
    // Non-pattern-4b: tail is just `Var(some_local)`. The signature
    // still carries a residual `Type::MutableRef` somewhere. Stage 4
    // strips it.
    let body_block = block(
        vec![Stmt::Let {
            pattern: vec![Some(VarId::from("v"))],
            value: Expr::Const(crate::ir::Const::UInt {
                bits: 64,
                value: ethnum::U256::from(7u64),
            }),
        }],
        tail_value(Expr::Var(VarId::from("v"))),
    );
    let ret = mut_ref(Type::UInt(64), Type::UInt(64));
    let mut program = one_fn_program_with_return(body_block, ret, vec![]);
    strip_mutable_ref_types(&mut program);

    // The return type is stripped because the tail isn't a
    // BorrowLoc/BorrowField (so this is NOT pattern 4b).
    assert_eq!(program.functions[&0].signature.return_type, Type::UInt(64));
}

#[test]
fn pattern_4b_return_type_preserved() {
    // Tail = BorrowField(BorrowLoc(x), STRUCT_S, 0). Pattern 4b.
    let body_block = block(
        vec![let_borrow_loc("r0", "x")],
        tail_value(Expr::Borrow {
            step: crate::ir::path::PathStep::Field {
                struct_id: STRUCT_S,
                field_index: 0,
            },
            base: Box::new(Expr::Var(VarId::from("r0"))),
        }),
    );
    let ret = mut_ref(Type::UInt(64), Type::UInt(64));
    let p = param("x", Type::UInt(64));
    let mut program = one_fn_program_with_return(body_block, ret.clone(), vec![p]);
    strip_mutable_ref_types(&mut program);

    // Pattern 4b: return type stays as MutableRef.
    assert_eq!(program.functions[&0].signature.return_type, ret);
}

#[test]
fn pattern_4b_borrow_loc_only_tail_preserved() {
    // Tail = BorrowLoc(x). Also pattern 4b.
    let body_block = just(Expr::BorrowLoc(VarId::from("x")));
    let ret = mut_ref(Type::UInt(64), Type::UInt(64));
    let p = param("x", Type::UInt(64));
    let mut program = one_fn_program_with_return(body_block, ret.clone(), vec![p]);
    strip_mutable_ref_types(&mut program);
    assert_eq!(program.functions[&0].signature.return_type, ret);
}

#[test]
fn call_type_args_stripped() {
    // f calls g::<&mut u64>(). The mutref in type_args is stripped.
    let body_block = just(Expr::Call {
        fun: 99,
        type_args: vec![mut_ref(Type::UInt(64), Type::UInt(64))],
        args: vec![],
    });
    let mut program = one_fn_program_with_return(body_block, Type::Unit, vec![]);
    strip_mutable_ref_types(&mut program);

    if let crate::ir::BlockTail::Value(Expr::Call { type_args, .. }) =
        &program.functions[&0].body.tail
    {
        assert_eq!(type_args.as_slice(), &[Type::UInt(64)]);
    } else {
        panic!("expected Call at tail");
    }
}

#[test]
fn pack_type_args_stripped() {
    let body_block = just(Expr::Pack {
        struct_id: STRUCT_S,
        type_args: vec![mut_ref(Type::Bool, Type::Bool)],
        variant: None,
        fields: vec![],
    });
    let mut program = one_fn_program_with_return(body_block, Type::Unit, vec![]);
    strip_mutable_ref_types(&mut program);
    if let crate::ir::BlockTail::Value(Expr::Pack { type_args, .. }) =
        &program.functions[&0].body.tail
    {
        assert_eq!(type_args.as_slice(), &[Type::Bool]);
    } else {
        panic!("expected Pack at tail");
    }
}

#[test]
fn nested_mutable_ref_inside_vector_type_arg_stripped() {
    // Vector<&mut u64> -> Vector<u64>
    let inner = Type::Vector(Box::new(mut_ref(Type::UInt(64), Type::UInt(64))));
    let body_block = just(Expr::Call {
        fun: 99,
        type_args: vec![inner],
        args: vec![],
    });
    let mut program = one_fn_program_with_return(body_block, Type::Unit, vec![]);
    strip_mutable_ref_types(&mut program);
    if let crate::ir::BlockTail::Value(Expr::Call { type_args, .. }) =
        &program.functions[&0].body.tail
    {
        assert_eq!(
            type_args.as_slice(),
            &[Type::Vector(Box::new(Type::UInt(64)))]
        );
    } else {
        panic!("expected Call at tail");
    }
}

#[test]
fn quantifier_binder_type_stripped() {
    let q = Expr::Quantifier {
        kind: QuantifierKind::Forall,
        binder: VarId::from("i"),
        binder_type: mut_ref(Type::UInt(64), Type::UInt(64)),
        domain: QuantDomain::Unbounded,
        body: Box::new(just(Expr::Const(crate::ir::Const::Bool(true)))),
    };
    let body_block = just(q);
    let mut program = one_fn_program_with_return(body_block, Type::Bool, vec![]);
    strip_mutable_ref_types(&mut program);
    if let crate::ir::BlockTail::Value(Expr::Quantifier { binder_type, .. }) =
        &program.functions[&0].body.tail
    {
        assert_eq!(binder_type, &Type::UInt(64));
    } else {
        panic!("expected Quantifier at tail");
    }
}

#[test]
fn idempotent_run() {
    let body_block = just(Expr::Const(crate::ir::Const::UInt {
        bits: 64,
        value: ethnum::U256::from(0u64),
    }));
    let mut program =
        one_fn_program_with_return(body_block, mut_ref(Type::UInt(64), Type::UInt(64)), vec![]);
    strip_mutable_ref_types(&mut program);
    let after = program.clone();
    strip_mutable_ref_types(&mut program);
    assert_eq!(program, after);
}

#[test]
fn native_function_signature_untouched() {
    // Obsolete: natives now live in program.natives.decls, not
    // program.functions; stages walk only functions, so this
    // behavior is structurally guaranteed.
}
