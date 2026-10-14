//! Stage 4 end-to-end tests: run the full pipeline (all five
//! transforms) and verify the postcondition holds plus the IR shape
//! matches expectations on representative fixtures.

use crate::ir::{BlockTail, Expr, Stmt, Type, VarId};
use crate::stage_04_effects::common::WORLD_VAR;
use crate::stage_04_effects::{ensure_world_struct, postcondition, run, world_type};

use super::fixtures::*;

#[test]
fn run_on_empty_program_is_ok() {
    let mut program = program_with(Vec::new());
    run(&mut program).unwrap();
    // World struct still registered (one struct, one prelude module).
    assert_eq!(program.structs.len(), 1);
}

#[test]
fn run_full_pipeline_on_impure_emitter() {
    // event::emit native + caller emit_one():
    //   fn emit_one() { event::emit::<u64>(7) }
    let emit = native_impure("event::emit", vec![param("e", Type::UInt(64))], Type::Unit);
    let caller = func(
        "emit_one",
        sig(Vec::new(), Type::Unit),
        body(
            vec![Stmt::Eval(Expr::Call {
                fun: 0,
                type_args: Vec::new(),
                args: vec![lit_u64(7)],
            })],
            Expr::Unit,
        ),
        FuncOpts::default(),
    );
    let mut program = program_with_natives(vec![(1, caller)], vec![(0, emit)]);
    run(&mut program).unwrap();

    let world_id = ensure_world_struct(&mut program); // idempotent retrieve
    postcondition::check(&program, world_id).expect("postcondition should hold");

    // Caller signature: (world: World) -> Tuple([World]).
    let caller = &program.functions[&1];
    assert_eq!(caller.signature.params.len(), 1);
    assert_eq!(caller.signature.params[0].name, WORLD_VAR);
    assert_eq!(
        caller.signature.return_type,
        Type::Tuple(vec![world_type(world_id)])
    );

    // Body: Stmt::Let { pattern: [Some(world)], value: Call(0, [7, world]) }
    //       then tail = Tuple([Var(world)]).
    assert_eq!(caller.body.stmts.len(), 1);
    match &caller.body.stmts[0] {
        Stmt::Let {
            pattern,
            value: Expr::Call { args, .. },
        } => {
            assert_eq!(pattern.len(), 1);
            assert!(matches!(&pattern[0], Some(v) if v.as_ref() == WORLD_VAR));
            assert_eq!(args.len(), 2);
            assert!(matches!(&args[0], Expr::Const(_)));
            assert!(matches!(&args[1], Expr::Var(v) if v.as_ref() == WORLD_VAR));
        }
        other => panic!("expected Let with Call, got {:?}", other),
    }
    match &caller.body.tail {
        BlockTail::Value(Expr::Tuple(items)) => {
            assert_eq!(items.len(), 1);
            assert!(matches!(&items[0], Expr::Var(v) if v.as_ref() == WORLD_VAR));
        }
        other => panic!("expected Value(Tuple([Var(world)])), got {:?}", other),
    }
}

#[test]
fn run_full_pipeline_chain_of_natives() {
    let emit = native_impure("event::emit", Vec::new(), Type::Unit);
    let transfer = native_impure("transfer::transfer", Vec::new(), Type::Unit);
    let caller = func(
        "f",
        sig(Vec::new(), Type::UInt(64)),
        body(
            vec![
                Stmt::Eval(Expr::Call {
                    fun: 0,
                    type_args: Vec::new(),
                    args: Vec::new(),
                }),
                Stmt::Eval(Expr::Call {
                    fun: 1,
                    type_args: Vec::new(),
                    args: Vec::new(),
                }),
            ],
            lit_u64(42),
        ),
        FuncOpts::default(),
    );
    let mut program = program_with_natives(vec![(2, caller)], vec![(0, emit), (1, transfer)]);
    run(&mut program).unwrap();

    let world_id = ensure_world_struct(&mut program);
    postcondition::check(&program, world_id).expect("postcondition should hold");

    let f = &program.functions[&2];
    // Return type: Tuple([UInt(64), World]).
    assert_eq!(
        f.signature.return_type,
        Type::Tuple(vec![Type::UInt(64), world_type(world_id)])
    );
    // Body: two Stmt::Let-wrapped Calls, then tail Tuple([42, world]).
    assert_eq!(f.body.stmts.len(), 2);
    match &f.body.tail {
        BlockTail::Value(Expr::Tuple(items)) => {
            assert_eq!(items.len(), 2);
            assert!(matches!(&items[0], Expr::Const(_)));
            assert!(matches!(&items[1], Expr::Var(v) if v.as_ref() == WORLD_VAR));
        }
        other => panic!("expected Tuple tail, got {:?}", other),
    }
}

#[test]
fn run_on_pure_program_leaves_signatures_alone() {
    let f = func(
        "add",
        sig(
            vec![param("a", Type::UInt(64)), param("b", Type::UInt(64))],
            Type::UInt(64),
        ),
        body(
            Vec::new(),
            Expr::BinOp {
                op: crate::ir::BinOp::Add,
                lhs: Box::new(Expr::Var(VarId::from("a"))),
                rhs: Box::new(Expr::Var(VarId::from("b"))),
            },
        ),
        FuncOpts {
            // BinOp::Add on UInt is partial. After re-classification
            // by stage 4, this should be PurePartial, NOT Impure.
            // Even if we seed Impure, the re-run should fix it.
            ..Default::default()
        },
    );
    let mut program = program_with(vec![(0, f)]);
    run(&mut program).unwrap();

    let f = &program.functions[&0];
    // After re-classification: partial-aborting, deterministic,
    // no global mutation. No world threading.
    assert_eq!(
        f.effects,
        crate::ir::Effects {
            aborts: crate::ir::AbortBit::Partial,
            det: crate::ir::DetBit::Det,
            mutation: crate::ir::MutLevel::NoMut,
            world_writes: false,
        }
    );
    assert_eq!(f.signature.params.len(), 2);
    assert_eq!(f.signature.return_type, Type::UInt(64));
}
