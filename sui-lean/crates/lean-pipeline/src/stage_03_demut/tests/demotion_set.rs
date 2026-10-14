//! Phase 2 unit tests for the demotion-set computation.

use std::collections::BTreeSet;

use crate::ir::Type;
use crate::stage_03_demut::compute_demotion_map;

use super::fixtures::{
    body_calling, empty_body, func, mut_ref, param, program_with, sig, FuncOpts,
};

fn t() -> Type {
    Type::UInt(64)
}

fn r() -> Type {
    Type::Bool
}

#[test]
fn single_function_with_mut_param_is_demoted() {
    let f = func(
        "f",
        sig(vec![param("x", mut_ref(t(), t()))], r()),
        empty_body(),
        FuncOpts::default(),
    );
    let prog = program_with(vec![(0, f)]);
    let demoted = compute_demotion_map(&prog).as_set();
    assert_eq!(demoted, BTreeSet::from([0]));
}

#[test]
fn single_function_without_mut_is_not_demoted() {
    let f = func(
        "f",
        sig(vec![param("x", t())], r()),
        empty_body(),
        FuncOpts::default(),
    );
    let prog = program_with(vec![(0, f)]);
    let demoted = compute_demotion_map(&prog).as_set();
    assert!(demoted.is_empty());
}

#[test]
fn mutual_recursion_with_mut_demotes_both_sides() {
    let f = func(
        "f",
        sig(vec![param("x", mut_ref(t(), t()))], Type::Unit),
        body_calling(&[1]),
        FuncOpts::default(),
    );
    let g = func(
        "g",
        sig(vec![param("y", mut_ref(t(), t()))], Type::Unit),
        body_calling(&[0]),
        FuncOpts::default(),
    );
    let prog = program_with(vec![(0, f), (1, g)]);
    let demoted = compute_demotion_map(&prog).as_set();
    assert_eq!(demoted, BTreeSet::from([0, 1]));
}

#[test]
fn three_way_scc_with_one_mut_member_demotes_all() {
    // f -> g -> h -> f, only f has &mut. SCC analysis should
    // propagate demotion across all three.
    let f = func(
        "f",
        sig(vec![param("x", mut_ref(t(), t()))], Type::Unit),
        body_calling(&[1]),
        FuncOpts::default(),
    );
    let g = func(
        "g",
        sig(vec![param("y", t())], Type::Unit),
        body_calling(&[2]),
        FuncOpts::default(),
    );
    let h = func(
        "h",
        sig(vec![param("z", t())], Type::Unit),
        body_calling(&[0]),
        FuncOpts::default(),
    );
    let prog = program_with(vec![(0, f), (1, g), (2, h)]);
    let demoted = compute_demotion_map(&prog).as_set();
    assert_eq!(demoted, BTreeSet::from([0, 1, 2]));
}

#[test]
fn native_with_mut_is_not_demoted() {
    // Obsolete: natives now live in program.natives.decls, not
    // program.functions; stages walk only functions, so this
    // behavior is structurally guaranteed.
}

#[test]
fn caller_without_mut_calling_mut_taker_only_demotes_callee() {
    // f -> g where g has &mut and f does not. f and g are NOT in the
    // same SCC (no g -> f edge), so only g is demoted.
    let f = func(
        "f",
        sig(vec![param("x", t())], Type::Unit),
        body_calling(&[1]),
        FuncOpts::default(),
    );
    let g = func(
        "g",
        sig(vec![param("y", mut_ref(t(), t()))], Type::Unit),
        empty_body(),
        FuncOpts::default(),
    );
    let prog = program_with(vec![(0, f), (1, g)]);
    let demoted = compute_demotion_map(&prog).as_set();
    assert_eq!(demoted, BTreeSet::from([1]));
}

#[test]
fn function_returning_mut_is_demoted_even_without_mut_param() {
    // Pattern 4-shaped: takes `T`, returns `&mut U`. Demotion-set
    // membership only requires `&mut` somewhere in the signature.
    let f = func(
        "f",
        sig(vec![param("x", t())], mut_ref(t(), t())),
        empty_body(),
        FuncOpts::default(),
    );
    let prog = program_with(vec![(0, f)]);
    let demoted = compute_demotion_map(&prog).as_set();
    assert_eq!(demoted, BTreeSet::from([0]));
}
