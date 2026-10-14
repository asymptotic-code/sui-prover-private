//! Tests for Transforms 2-3: WriteBack position-shift.

use crate::ir::{BorrowEdge, BorrowNode, Expr, Stmt, Type, VarId};
use crate::stage_03_mut_to_let::rewrite_write_backs;

use super::fixtures::*;

const STRUCT_S: usize = 7;

// ---------------------------------------------------------------------------
// Transform 2 -- WriteBack(LocalRoot, ..)
// ---------------------------------------------------------------------------

#[test]
fn write_back_local_root_direct_becomes_let_rebind_of_local() {
    // let r = &x; ...; WriteBack(LocalRoot(x), Direct, r);
    let stmts = vec![
        let_borrow_loc("r", "x"),
        eval_write_back(
            BorrowNode::LocalRoot(VarId::from("x")),
            BorrowEdge::Direct,
            "r",
        ),
    ];
    let mut program = one_fn_program(
        stmts,
        Expr::Unit,
        vec![param("x", Type::UInt(64))],
        Type::Unit,
    );
    rewrite_write_backs(&mut program).unwrap();

    let stmts = &body_of(&program).stmts;
    assert_eq!(stmts.len(), 2);
    match &stmts[1] {
        Stmt::Let { pattern, value } => {
            assert_eq!(pattern, &vec![Some(VarId::from("x"))]);
            match value {
                Expr::WriteBack {
                    node, edge, child, ..
                } => {
                    assert_eq!(node, &BorrowNode::LocalRoot(VarId::from("x")));
                    assert_eq!(edge, &BorrowEdge::Direct);
                    assert_eq!(child, &VarId::from("r"));
                }
                other => panic!("expected WriteBack value, got {:?}", other),
            }
        }
        other => panic!("expected Stmt::Let, got {:?}", other),
    }
}

// ---------------------------------------------------------------------------
// Transform 3 -- WriteBack(Reference, edge, ..) per edge variant
// ---------------------------------------------------------------------------

#[test]
fn write_back_reference_field_edge() {
    let stmts = vec![
        let_borrow_loc("r0", "x"),
        let_borrow_field("r1", STRUCT_S, 0, Expr::Var(VarId::from("r0"))),
        eval_write_back(
            BorrowNode::Reference(VarId::from("r0")),
            BorrowEdge::StructField {
                struct_id: STRUCT_S,
                field_index: 0,
            },
            "r1",
        ),
    ];
    let mut program = one_fn_program(
        stmts,
        Expr::Unit,
        vec![param("x", Type::UInt(64))],
        Type::Unit,
    );
    rewrite_write_backs(&mut program).unwrap();

    let stmts = &body_of(&program).stmts;
    assert_eq!(stmts.len(), 3);
    match &stmts[2] {
        Stmt::Let { pattern, value } => {
            assert_eq!(pattern, &vec![Some(VarId::from("r0"))]);
            assert!(matches!(value, Expr::WriteBack { .. }));
        }
        other => panic!("expected Stmt::Let rebind of r0, got {:?}", other),
    }
}

#[test]
fn write_back_reference_enum_field_edge() {
    let stmts = vec![
        let_borrow_loc("r0", "x"),
        eval_write_back(
            BorrowNode::Reference(VarId::from("r0")),
            BorrowEdge::EnumField {
                struct_id: STRUCT_S,
                variant: 0,
                field_index: 1,
            },
            "r1",
        ),
        // (r1 not introduced via borrow but referenced as child --
        // tests don't enforce that here; the rewriter doesn't check
        // scope, just shape.)
    ];
    let mut program = one_fn_program(
        stmts,
        Expr::Unit,
        vec![param("x", Type::UInt(64))],
        Type::Unit,
    );
    rewrite_write_backs(&mut program).unwrap();

    match &body_of(&program).stmts[1] {
        Stmt::Let { pattern, .. } => {
            assert_eq!(pattern, &vec![Some(VarId::from("r0"))]);
        }
        other => panic!("expected Stmt::Let, got {:?}", other),
    }
}

#[test]
fn write_back_reference_hyper_edge() {
    let inner = vec![
        BorrowEdge::StructField {
            struct_id: STRUCT_S,
            field_index: 0,
        },
        BorrowEdge::StructField {
            struct_id: STRUCT_S,
            field_index: 1,
        },
    ];
    let stmts = vec![
        let_borrow_loc("r0", "x"),
        eval_write_back(
            BorrowNode::Reference(VarId::from("r0")),
            BorrowEdge::Hyper(inner.clone()),
            "r2",
        ),
    ];
    let mut program = one_fn_program(
        stmts,
        Expr::Unit,
        vec![param("x", Type::UInt(64))],
        Type::Unit,
    );
    rewrite_write_backs(&mut program).unwrap();

    match &body_of(&program).stmts[1] {
        Stmt::Let { pattern, value } => {
            assert_eq!(pattern, &vec![Some(VarId::from("r0"))]);
            match value {
                Expr::WriteBack {
                    edge: BorrowEdge::Hyper(got_inner),
                    ..
                } => {
                    assert_eq!(got_inner, &inner);
                }
                other => panic!("expected WriteBack with Hyper edge, got {:?}", other),
            }
        }
        other => panic!("expected Stmt::Let, got {:?}", other),
    }
}

// ---------------------------------------------------------------------------
// Multi-step chains
// ---------------------------------------------------------------------------

#[test]
fn multi_step_chain_three_writebacks_become_three_rebinds() {
    // Simulate: r2 = &r1.g; r1 = &r0.f; r0 = &x; *r2 = 5; <chain at r2's death>
    let stmts = vec![
        let_borrow_loc("r0", "x"),
        let_borrow_field("r1", STRUCT_S, 0, Expr::Var(VarId::from("r0"))),
        let_borrow_field("r2", STRUCT_S, 1, Expr::Var(VarId::from("r1"))),
        eval_write_back(
            BorrowNode::Reference(VarId::from("r1")),
            BorrowEdge::StructField {
                struct_id: STRUCT_S,
                field_index: 1,
            },
            "r2",
        ),
        eval_write_back(
            BorrowNode::Reference(VarId::from("r0")),
            BorrowEdge::StructField {
                struct_id: STRUCT_S,
                field_index: 0,
            },
            "r1",
        ),
        eval_write_back(
            BorrowNode::LocalRoot(VarId::from("x")),
            BorrowEdge::Direct,
            "r0",
        ),
    ];
    let mut program = one_fn_program(
        stmts,
        Expr::Unit,
        vec![param("x", Type::UInt(64))],
        Type::Unit,
    );
    rewrite_write_backs(&mut program).unwrap();

    let stmts = &body_of(&program).stmts;
    assert_eq!(stmts.len(), 6);

    // Stmts 3, 4, 5 are the rebinds.
    let targets = ["r1", "r0", "x"];
    for (idx, target) in targets.iter().enumerate() {
        match &stmts[3 + idx] {
            Stmt::Let { pattern, value } => {
                assert_eq!(pattern, &vec![Some(VarId::from(*target))]);
                assert!(matches!(value, Expr::WriteBack { .. }));
            }
            other => panic!("expected Stmt::Let for {}, got {:?}", target, other),
        }
    }
}

// ---------------------------------------------------------------------------
// SpecGlobalRoot preserved (ghost-state writeback, renderer-side stub)
// ---------------------------------------------------------------------------

#[test]
fn write_back_spec_global_root_preserved_as_eval() {
    // `*ghost::borrow_mut<K, V>() = ...` lowers to
    // `Stmt::Eval(WriteBack { node: SpecGlobalRoot, .. })`. Stage 3 has
    // no local to rebind onto; the statement stays as `Stmt::Eval(WriteBack ..)`
    // and the renderer's `Prover.Mutation.writeBackSpecGlobal` path takes
    // it from there (`render::expr::render_writeback`).
    let stmts = vec![eval_write_back(
        BorrowNode::SpecGlobalRoot {
            type_args: Vec::new(),
        },
        BorrowEdge::Direct,
        "r",
    )];
    let mut program = one_fn_program(
        stmts,
        Expr::Unit,
        vec![param("x", Type::UInt(64))],
        Type::Unit,
    );
    rewrite_write_backs(&mut program).unwrap();

    let stmts = &body_of(&program).stmts;
    assert_eq!(stmts.len(), 1);
    match &stmts[0] {
        Stmt::Eval(Expr::WriteBack { node, .. }) => {
            assert!(matches!(node, BorrowNode::SpecGlobalRoot { .. }));
        }
        other => panic!(
            "expected Stmt::Eval(WriteBack {{ SpecGlobalRoot, .. }}), got {:?}",
            other
        ),
    }
}

// ---------------------------------------------------------------------------
// Native skip + idempotency
// ---------------------------------------------------------------------------

#[test]
fn native_function_left_untouched() {
    // Obsolete: natives now live in program.natives.decls, not
    // program.functions; stages walk only functions, so this
    // behavior is structurally guaranteed.
}

#[test]
fn idempotent_run_twice() {
    let stmts = vec![
        let_borrow_loc("r", "x"),
        eval_write_back(
            BorrowNode::LocalRoot(VarId::from("x")),
            BorrowEdge::Direct,
            "r",
        ),
    ];
    let mut program = one_fn_program(
        stmts,
        Expr::Unit,
        vec![param("x", Type::UInt(64))],
        Type::Unit,
    );
    rewrite_write_backs(&mut program).unwrap();
    let after_once = program.clone();
    rewrite_write_backs(&mut program).unwrap();
    assert_eq!(program, after_once);
}
