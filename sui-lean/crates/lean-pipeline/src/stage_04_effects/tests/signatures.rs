//! Stage 4 signature augmentation tests.

use crate::ir::{AbortBit, DetBit, Effects, MutLevel, Stmt, Type, VarId};
use crate::stage_04_effects::common::WORLD_VAR;
use crate::stage_04_effects::{augment_signatures, ensure_world_struct, world_type};

use super::fixtures::*;

#[test]
fn pure_function_signature_unchanged() {
    let f = func(
        "g",
        sig(vec![param("x", Type::UInt(64))], Type::UInt(64)),
        body(Vec::new(), Expr::Var(VarId::from("x"))),
        FuncOpts {
            effects: Effects::PURE,
            ..Default::default()
        },
    );
    let mut program = program_with(vec![(0, f)]);
    let world_id = ensure_world_struct(&mut program);
    let needs_world = crate::stage_04_effects::common::compute_needs_world(&program);

    augment_signatures(&mut program, world_id, &needs_world).unwrap();
    let g = &program.functions[&0];
    assert_eq!(g.signature.params.len(), 1);
    assert_eq!(g.signature.return_type, Type::UInt(64));
}

#[test]
fn impure_unit_return_becomes_world_tuple() {
    let f = func(
        "f",
        sig(Vec::new(), Type::Unit),
        body(Vec::new(), Expr::Unit),
        FuncOpts::default(),
    );
    let mut program = program_with(vec![(0, f)]);
    let world_id = ensure_world_struct(&mut program);
    let needs_world = crate::stage_04_effects::common::compute_needs_world(&program);

    augment_signatures(&mut program, world_id, &needs_world).unwrap();
    let f = &program.functions[&0];
    assert_eq!(f.signature.params.len(), 1);
    assert_eq!(f.signature.params[0].name, WORLD_VAR);
    assert_eq!(f.signature.params[0].ty, world_type(world_id));
    assert_eq!(
        f.signature.return_type,
        Type::Tuple(vec![world_type(world_id)])
    );
}

#[test]
fn impure_with_return_becomes_tuple_of_two() {
    let f = func(
        "f",
        sig(Vec::new(), Type::UInt(64)),
        body(Vec::new(), lit_u64(7)),
        FuncOpts::default(),
    );
    let mut program = program_with(vec![(0, f)]);
    let world_id = ensure_world_struct(&mut program);
    let needs_world = crate::stage_04_effects::common::compute_needs_world(&program);

    augment_signatures(&mut program, world_id, &needs_world).unwrap();
    let f = &program.functions[&0];
    assert_eq!(
        f.signature.return_type,
        Type::Tuple(vec![Type::UInt(64), world_type(world_id)])
    );
}

#[test]
fn impure_with_existing_tuple_flattens() {
    let f = func(
        "f",
        sig(Vec::new(), Type::Tuple(vec![Type::UInt(64), Type::Bool])),
        body(
            Vec::new(),
            Expr::Tuple(vec![lit_u64(1), Expr::Const(crate::ir::Const::Bool(true))]),
        ),
        FuncOpts::default(),
    );
    let mut program = program_with(vec![(0, f)]);
    let world_id = ensure_world_struct(&mut program);
    let needs_world = crate::stage_04_effects::common::compute_needs_world(&program);

    augment_signatures(&mut program, world_id, &needs_world).unwrap();
    let f = &program.functions[&0];
    assert_eq!(
        f.signature.return_type,
        Type::Tuple(vec![Type::UInt(64), Type::Bool, world_type(world_id)])
    );
}

#[test]
fn native_impure_signature_augmented_uniformly() {
    // Impure natives (e.g., `event::emit`, `transfer::transfer`) get
    // their IR signature augmented just like non-native Impure
    // functions: the IR is the single source of truth consumed by
    // stage 10's TypeOf, the renderer, etc. The hand-written
    // `Prover.World.*` Lean prelude already declares the same shape.
    let mut native = native_impure("event::emit", Vec::new(), Type::Unit);
    native.module = 0;
    let mut program = program_with_natives(vec![], vec![(0, native)]);
    let world_id = ensure_world_struct(&mut program);
    let needs_world = crate::stage_04_effects::common::compute_needs_world(&program);

    augment_signatures(&mut program, world_id, &needs_world).unwrap();
    // Native is in natives.decls, not functions.
    let n = &program.natives.decls[&0];
    // `world: World` parameter appended.
    assert_eq!(n.signature.params.len(), 1);
    assert_eq!(n.signature.params[0].ty, world_type(world_id));
    // Unit + world return -> Tuple([World]).
    assert_eq!(
        n.signature.return_type,
        Type::Tuple(vec![world_type(world_id)])
    );
}

#[test]
fn pure_partial_function_untouched() {
    let f = func(
        "f",
        sig(vec![param("x", Type::UInt(64))], Type::UInt(64)),
        body(Vec::new(), Expr::Var(VarId::from("x"))),
        FuncOpts {
            effects: Effects {
                aborts: AbortBit::Partial,
                det: DetBit::Det,
                mutation: MutLevel::NoMut,
                world_writes: false,
            },
            ..Default::default()
        },
    );
    let mut program = program_with(vec![(0, f)]);
    let world_id = ensure_world_struct(&mut program);
    let needs_world = crate::stage_04_effects::common::compute_needs_world(&program);

    augment_signatures(&mut program, world_id, &needs_world).unwrap();
    let f = &program.functions[&0];
    assert_eq!(f.signature.params.len(), 1);
    assert_eq!(f.signature.return_type, Type::UInt(64));
}

#[test]
fn idempotent_two_runs() {
    let f = func(
        "f",
        sig(Vec::new(), Type::UInt(64)),
        body(Vec::new(), lit_u64(7)),
        FuncOpts::default(),
    );
    let mut program = program_with(vec![(0, f)]);
    let world_id = ensure_world_struct(&mut program);
    let needs_world = crate::stage_04_effects::common::compute_needs_world(&program);

    augment_signatures(&mut program, world_id, &needs_world).unwrap();
    let after_first = program.functions[&0].signature.clone();
    let needs_world = crate::stage_04_effects::common::compute_needs_world(&program);

    augment_signatures(&mut program, world_id, &needs_world).unwrap();
    assert_eq!(program.functions[&0].signature, after_first);
}

// Suppress unused-import warning when only one helper is used.
#[allow(unused_imports)]
use crate::ir::Expr;
#[allow(unused_imports)]
use Stmt as _;
