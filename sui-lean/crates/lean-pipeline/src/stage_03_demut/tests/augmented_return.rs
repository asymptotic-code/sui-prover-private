//! Phase 1 unit tests for `augment_return`.
//!
//! Covers all five rows of the augmented-return convention table
//! (see `signatures.rs` module docs).

use crate::ir::Type;
use crate::stage_03_demut::augment_return;

#[test]
fn no_mut_params_returns_r_unchanged() {
    let r = Type::UInt(64);
    let result = augment_return(r.clone(), &[]);
    assert_eq!(result, r);
}

#[test]
fn unit_one_mut_param_returns_t1_no_wrap() {
    let result = augment_return(Type::Unit, &[Type::UInt(64)]);
    assert_eq!(result, Type::UInt(64));
}

#[test]
fn unit_two_mut_params_returns_tuple() {
    let muts = vec![Type::UInt(64), Type::Bool];
    let result = augment_return(Type::Unit, &muts);
    assert_eq!(result, Type::Tuple(muts));
}

#[test]
fn r_simple_one_mut_returns_pair() {
    let result = augment_return(Type::Bool, &[Type::UInt(64)]);
    assert_eq!(result, Type::Tuple(vec![Type::Bool, Type::UInt(64)]));
}

#[test]
fn r_tuple_one_mut_flattens() {
    let r = Type::Tuple(vec![Type::Bool, Type::Address]);
    let result = augment_return(r, &[Type::UInt(64)]);
    assert_eq!(
        result,
        Type::Tuple(vec![Type::Bool, Type::Address, Type::UInt(64)])
    );
}
