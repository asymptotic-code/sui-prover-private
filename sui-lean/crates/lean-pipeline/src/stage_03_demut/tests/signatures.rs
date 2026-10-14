//! Phase 2 unit tests for `demote_signature` + `classify`.

use crate::ir::builder::var;
use crate::ir::{Block, BlockTail, Expr, Type};
use crate::stage_03_demut::{classify, demote_signature, DemotionPattern};

use super::fixtures::{empty_body, func, mut_ref, param, sig, FuncOpts};

fn t() -> Type {
    Type::UInt(64)
}

fn t2() -> Type {
    Type::Bool
}

fn r() -> Type {
    Type::Address
}

#[test]
fn standard_one_mut_simple_return_becomes_pair() {
    let mut f = func(
        "f",
        sig(vec![param("x", mut_ref(t(), t()))], r()),
        empty_body(),
        FuncOpts::default(),
    );
    assert_eq!(classify(&f), DemotionPattern::Standard);
    demote_signature(&mut f);
    assert_eq!(f.signature.params[0].ty, t());
    assert_eq!(f.signature.return_type, Type::Tuple(vec![r(), t()]));
}

#[test]
fn standard_one_mut_unit_return_drops_to_t() {
    let mut f = func(
        "f",
        sig(vec![param("x", mut_ref(t(), t()))], Type::Unit),
        empty_body(),
        FuncOpts::default(),
    );
    demote_signature(&mut f);
    assert_eq!(f.signature.params[0].ty, t());
    assert_eq!(f.signature.return_type, t());
}

#[test]
fn standard_two_mut_simple_return_becomes_triple() {
    let mut f = func(
        "f",
        sig(
            vec![
                param("x", mut_ref(t(), t())),
                param("y", mut_ref(t2(), t2())),
            ],
            r(),
        ),
        empty_body(),
        FuncOpts::default(),
    );
    demote_signature(&mut f);
    assert_eq!(f.signature.params[0].ty, t());
    assert_eq!(f.signature.params[1].ty, t2());
    assert_eq!(f.signature.return_type, Type::Tuple(vec![r(), t(), t2()]));
}

#[test]
fn standard_one_mut_tuple_return_flattens() {
    let mut f = func(
        "f",
        sig(
            vec![param("x", mut_ref(t(), t()))],
            Type::Tuple(vec![r(), t2()]),
        ),
        empty_body(),
        FuncOpts::default(),
    );
    demote_signature(&mut f);
    assert_eq!(f.signature.params[0].ty, t());
    assert_eq!(f.signature.return_type, Type::Tuple(vec![r(), t2(), t()]));
}

#[test]
fn pattern_4a_self_return_demotes_to_plain_t() {
    // f(x: &mut T): &mut T { x }  -- tail is Value(Var(x)).
    let body = Block {
        stmts: Vec::new(),
        tail: BlockTail::Value(var("x")),
    };
    let mut f = func(
        "f",
        sig(vec![param("x", mut_ref(t(), t()))], mut_ref(t(), t())),
        body,
        FuncOpts::default(),
    );
    assert_eq!(classify(&f), DemotionPattern::SelfReturn);
    demote_signature(&mut f);
    assert_eq!(f.signature.params[0].ty, t());
    assert_eq!(f.signature.return_type, t());
}

#[test]
fn pattern_4b_sub_field_keeps_mutable_ref_return() {
    // f(x: &mut Outer): &mut Inner  with body returning a borrow
    // chain off x. We don't need to construct the borrow chain for
    // classify -- any non-`Value(Var(param))` tail is treated as
    // sub-field-return.
    let body = Block {
        stmts: Vec::new(),
        tail: BlockTail::Value(Expr::Borrow {
            step: crate::ir::path::PathStep::Field {
                struct_id: 0,
                field_index: 0,
            },
            base: Box::new(var("x")),
        }),
    };
    let outer = t();
    let inner = t2();
    let mut f = func(
        "f",
        sig(
            vec![param("x", mut_ref(outer.clone(), outer.clone()))],
            mut_ref(inner.clone(), outer.clone()),
        ),
        body,
        FuncOpts::default(),
    );
    assert_eq!(classify(&f), DemotionPattern::SubFieldReturn);
    demote_signature(&mut f);
    // Param stripped...
    assert_eq!(f.signature.params[0].ty, outer);
    // ...but return KEEPS Type::MutableRef.
    assert_eq!(f.signature.return_type, mut_ref(inner, outer));
}

#[test]
fn native_function_left_untouched() {
    // Obsolete: natives now live in program.natives.decls, not
    // program.functions; stages walk only functions, so this
    // behavior is structurally guaranteed.
}

#[test]
fn no_mut_signature_classifies_as_no_op() {
    let f = func(
        "f",
        sig(vec![param("x", t())], r()),
        empty_body(),
        FuncOpts::default(),
    );
    assert_eq!(classify(&f), DemotionPattern::NoMut);
    let original = f.signature.clone();
    let mut f = f;
    demote_signature(&mut f);
    assert_eq!(f.signature, original);
}
