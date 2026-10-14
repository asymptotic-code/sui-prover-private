//! Rewrite-correctness smoke tests for stage 10.

use crate::ir::expr::{Block, BlockTail, Expr};
use crate::ir::function::{Function, FunctionKind, Signature};
use crate::ir::ops::UnOp;
use crate::ir::ty::{Const, Type};
use crate::stage_10_bounded_nat::prelude_fids::{aborts_name, main_name, Op};
use crate::stage_10_bounded_nat::{run, Stage10Error, Stage10RewritePhase};

use super::fixtures::{fn_add_u64, fn_cast_u64_to_u8, fn_lt_u64, func, param, program_with, vid};

fn find_native_fid_by_name(program: &crate::ir::Program, name: &str) -> Option<crate::ir::FunId> {
    program
        .natives
        .decls
        .iter()
        .find(|(_, d)| d.name == name)
        .map(|(id, _)| *id)
}

fn malformed_binder_function() -> Function {
    func(
        "bad_binder",
        vec![],
        Type::Unit,
        Block {
            stmts: vec![crate::ir::Stmt::Let {
                pattern: vec![Some(vid("a")), Some(vid("b"))],
                value: Expr::Const(Const::UInt {
                    bits: 64,
                    value: ethnum::U256::ZERO,
                }),
            }],
            tail: BlockTail::Value(Expr::Unit),
        },
    )
}

#[test]
fn add_u64_rewrites_to_bounded_call() {
    let mut p = program_with(vec![(0, fn_add_u64())]);
    run(&mut p).unwrap();

    let main = main_name(Op::Add, 64);
    let aborts = aborts_name(Op::Add, 64);
    let main_fid = find_native_fid_by_name(&p, &main).expect("BoundedU64_add registered");
    let aborts_fid =
        find_native_fid_by_name(&p, &aborts).expect("BoundedU64_add_aborts registered");

    let body = &p.functions[&0].body;
    match &body.tail {
        BlockTail::Value(Expr::Call {
            fun,
            args,
            type_args,
        }) => {
            assert_eq!(*fun, main_fid);
            assert!(type_args.is_empty());
            assert_eq!(args.len(), 2);
        }
        other => panic!("expected Call tail, got {other:?}"),
    }

    let aborts_decl = &p.natives.decls[&aborts_fid];
    assert_eq!(
        aborts_decl.spec_target,
        Some(main_fid),
        "aborts companion must back-reference main op via spec_target"
    );
    assert!(aborts_decl.is_framework);
}

#[test]
fn comparison_has_no_aborts_companion() {
    let mut p = program_with(vec![(0, fn_lt_u64())]);
    run(&mut p).unwrap();

    let main = main_name(Op::Lt, 64);
    let aborts = aborts_name(Op::Lt, 64);
    assert!(
        find_native_fid_by_name(&p, &main).is_some(),
        "BoundedU64_lt should be registered"
    );
    assert!(
        find_native_fid_by_name(&p, &aborts).is_none(),
        "comparisons don't get an aborts companion"
    );
}

#[test]
fn narrowing_cast_registers_aborts_companion() {
    let mut p = program_with(vec![(0, fn_cast_u64_to_u8())]);
    run(&mut p).unwrap();

    let main = main_name(Op::Cast { dst: 8 }, 64);
    let aborts = aborts_name(Op::Cast { dst: 8 }, 64);
    assert!(find_native_fid_by_name(&p, &main).is_some());
    assert!(
        find_native_fid_by_name(&p, &aborts).is_some(),
        "narrowing cast u64 -> u8 should get a companion"
    );
}

#[test]
fn widening_cast_does_not_register_aborts_companion() {
    let f = func(
        "widen",
        vec![param("x", Type::UInt(8))],
        Type::UInt(64),
        Block {
            stmts: vec![],
            tail: BlockTail::Value(Expr::UnOp {
                op: UnOp::Cast(64),
                operand: Box::new(Expr::Var(vid("x"))),
            }),
        },
    );
    let mut p = program_with(vec![(0, f)]);
    run(&mut p).unwrap();

    let aborts = aborts_name(Op::Cast { dst: 64 }, 8);
    assert!(
        find_native_fid_by_name(&p, &aborts).is_none(),
        "widening u8 -> u64 cannot abort -- no companion expected"
    );
}

#[test]
fn run_is_idempotent() {
    let mut p = program_with(vec![(0, fn_add_u64())]);
    run(&mut p).unwrap();
    let after_first = p.functions.len();

    run(&mut p).unwrap();
    let after_second = p.functions.len();

    assert_eq!(
        after_first, after_second,
        "second stage_10 run must not register new functions"
    );
}

#[test]
fn postcondition_passes_after_run() {
    let mut p = program_with(vec![(0, fn_add_u64())]);
    run(&mut p).unwrap();
    crate::stage_10_bounded_nat::postcondition::check(&p).unwrap();
}

#[test]
fn postcondition_catches_surviving_binop() {
    let p = program_with(vec![(0, fn_add_u64())]);
    let result = crate::stage_10_bounded_nat::postcondition::check(&p);
    match result {
        Err(Stage10Error::Postcondition(msg)) => {
            assert!(msg.contains("BinOp"), "expected BinOp in diagnostic: {msg}");
        }
        other => panic!("expected Stage10Error::Postcondition, got {other:?}"),
    }
}

#[test]
fn natives_are_not_walked() {
    let native = Function {
        module: 0,
        name: "my_native".to_string(),
        signature: Signature {
            type_params: vec![],
            params: vec![],
            return_type: Type::UInt(64),
        },
        body: Block {
            stmts: vec![],
            tail: BlockTail::Value(Expr::Const(Const::UInt {
                bits: 64,
                value: ethnum::U256::ZERO,
            })),
        },
        kind: FunctionKind::Synthetic,
        effects: crate::ir::Effects::PURE,
        explicit_pure: true,
    };

    let mut p = program_with(vec![(0, fn_add_u64()), (1, native)]);
    run(&mut p).unwrap();
}

#[test]
fn reserved_user_native_collision_allocates_distinct_intrinsic() {
    let mut p = program_with(vec![(0, fn_add_u64())]);
    let collision_fid = 1;
    let name = main_name(Op::Add, 64);
    let signature = Signature {
        type_params: Vec::new(),
        params: vec![param("a", Type::UInt(64)), param("b", Type::UInt(64))],
        return_type: Type::UInt(64),
    };
    p.natives.decls.insert(
        collision_fid,
        crate::ir::NativeDecl {
            module: 0,
            name: name.clone(),
            signature: signature.clone(),
            effects: Op::Add.main_effects(64),
            explicit_pure: true,
            is_framework: false,
            spec_target: None,
            user_native: Some(false),
        },
    );

    run(&mut p).unwrap();

    let BlockTail::Value(Expr::Call { fun, .. }) = &p.functions[&0].body.tail else {
        panic!("expected lowered call, got {:?}", p.functions[&0].body.tail);
    };
    assert_ne!(*fun, collision_fid);
    let intrinsic_fid = *fun;
    let intrinsic = &p.natives.decls[&intrinsic_fid];
    assert_eq!(intrinsic.name, name);
    assert_eq!(intrinsic.signature, signature);
    assert_eq!(intrinsic.effects, Op::Add.main_effects(64));
    assert!(intrinsic.explicit_pure);
    assert!(intrinsic.is_framework);
    assert_eq!(intrinsic.spec_target, None);
    assert_eq!(intrinsic.user_native, None);
    assert_eq!(
        p.natives
            .decls
            .values()
            .filter(|decl| decl.name == name)
            .count(),
        2
    );

    let native_count = p.natives.decls.len();
    run(&mut p).unwrap();
    assert_eq!(p.natives.decls.len(), native_count);
    assert!(matches!(
        &p.functions[&0].body.tail,
        BlockTail::Value(Expr::Call { fun, .. }) if *fun == intrinsic_fid
    ));
}

#[test]
fn collect_failure_is_reported_and_preserves_the_original_body() {
    let mut p = program_with(vec![(0, malformed_binder_function())]);
    let original_body = p.functions[&0].body.clone();

    let err = run(&mut p).unwrap_err();
    let Stage10Error::FunctionFailures(failures) = err else {
        panic!("expected function collect failure, got {err:?}");
    };
    assert_eq!(failures.len(), 1);
    assert_eq!(failures[0].function, 0);
    assert_eq!(failures[0].phase, Stage10RewritePhase::CollectNeeds);
    assert!(matches!(
        &failures[0].err,
        crate::ir::analysis::type_of::TypeOfError::MalformedAccess { .. }
    ));
    assert_eq!(p.functions[&0].body, original_body);
}

#[test]
fn one_collect_failure_does_not_block_other_function_rewrites() {
    let mut p = program_with(vec![(0, malformed_binder_function()), (1, fn_add_u64())]);
    let failed_body = p.functions[&0].body.clone();

    let err = run(&mut p).unwrap_err();
    let Stage10Error::FunctionFailures(failures) = err else {
        panic!("expected function collect failure, got {err:?}");
    };
    assert_eq!(failures.len(), 1);
    assert_eq!(failures[0].function, 0);
    assert_eq!(failures[0].phase, Stage10RewritePhase::CollectNeeds);
    assert_eq!(p.functions[&0].body, failed_body);
    assert!(matches!(
        &p.functions[&1].body.tail,
        BlockTail::Value(Expr::Call { .. })
    ));
}
