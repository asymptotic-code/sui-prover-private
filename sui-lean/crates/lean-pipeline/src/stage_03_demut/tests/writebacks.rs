//! Phase 4 unit tests for the WriteRef / WriteBack rewriters.

use crate::ir::builder::{lit_u64, var};
use crate::ir::{Block, BlockTail, BorrowEdge, BorrowNode, Expr, Stmt, Type, VarId};
use crate::stage_03_demut::{path_to_update, rewrite_writebacks};

use super::fixtures::{func, param, program_with, sig, FuncOpts};

const STRUCT_S: usize = 7;
const STRUCT_T: usize = 11;

fn t() -> Type {
    Type::UInt(64)
}

fn vid(name: &str) -> VarId {
    VarId::from(name)
}

#[test]
fn write_ref_field_chain_lowers_to_update_field_rebind() {
    // let r0 = BorrowLoc(local);
    // let r1 = BorrowField { struct: S, field: 1, base: Var(r0) };
    // *r1 = 42;
    // After Phase 4: let r0 = BorrowLoc(local); let r1 = BorrowField{...}; let local = UpdateField(S, 1, local, 42);
    let body = Block {
        stmts: vec![
            Stmt::Let {
                pattern: vec![Some(vid("r0"))],
                value: Expr::BorrowLoc(vid("local")),
            },
            Stmt::Let {
                pattern: vec![Some(vid("r1"))],
                value: Expr::Borrow {
                    step: crate::ir::path::PathStep::Field {
                        struct_id: STRUCT_S,
                        field_index: 1,
                    },
                    base: Box::new(var("r0")),
                },
            },
            Stmt::Eval(Expr::WriteRef {
                reference: Box::new(var("r1")),
                value: Box::new(lit_u64(42)),
            }),
        ],
        tail: BlockTail::Value(Expr::Unit),
    };
    let f = func(
        "f",
        sig(vec![param("local", t())], Type::Unit),
        body,
        FuncOpts::default(),
    );
    let mut prog = program_with(vec![(0, f)]);
    rewrite_writebacks(&mut prog);

    let stmts = &prog.functions[&0].body.stmts;
    assert_eq!(stmts.len(), 3);
    match &stmts[2] {
        Stmt::Let { pattern, value } => {
            assert_eq!(pattern, &vec![Some(vid("local"))]);
            let expected = path_to_update(
                var("local"),
                &[BorrowEdge::StructField {
                    struct_id: STRUCT_S,
                    field_index: 1,
                }],
                lit_u64(42),
            );
            assert_eq!(value, &expected);
        }
        other => panic!("expected Stmt::Let rebinding 'local', got {:?}", other),
    }
}

#[test]
fn write_ref_two_deep_chain_lowers_correctly() {
    // r0 = BorrowLoc(local); r1 = BF(r0, S, 0); r2 = BF(r1, T, 2); *r2 = 7;
    // -> let local = path_to_update(local, [Field(S,0), Field(T,2)], 7)
    let body = Block {
        stmts: vec![
            Stmt::Let {
                pattern: vec![Some(vid("r0"))],
                value: Expr::BorrowLoc(vid("local")),
            },
            Stmt::Let {
                pattern: vec![Some(vid("r1"))],
                value: Expr::Borrow {
                    step: crate::ir::path::PathStep::Field {
                        struct_id: STRUCT_S,
                        field_index: 0,
                    },
                    base: Box::new(var("r0")),
                },
            },
            Stmt::Let {
                pattern: vec![Some(vid("r2"))],
                value: Expr::Borrow {
                    step: crate::ir::path::PathStep::Field {
                        struct_id: STRUCT_T,
                        field_index: 2,
                    },
                    base: Box::new(var("r1")),
                },
            },
            Stmt::Eval(Expr::WriteRef {
                reference: Box::new(var("r2")),
                value: Box::new(lit_u64(7)),
            }),
        ],
        tail: BlockTail::Value(Expr::Unit),
    };
    let f = func(
        "f",
        sig(vec![param("local", t())], Type::Unit),
        body,
        FuncOpts::default(),
    );
    let mut prog = program_with(vec![(0, f)]);
    rewrite_writebacks(&mut prog);

    let stmts = &prog.functions[&0].body.stmts;
    match &stmts[3] {
        Stmt::Let { pattern, value } => {
            assert_eq!(pattern, &vec![Some(vid("local"))]);
            let expected = path_to_update(
                var("local"),
                &[
                    BorrowEdge::StructField {
                        struct_id: STRUCT_S,
                        field_index: 0,
                    },
                    BorrowEdge::StructField {
                        struct_id: STRUCT_T,
                        field_index: 2,
                    },
                ],
                lit_u64(7),
            );
            assert_eq!(value, &expected);
        }
        other => panic!("expected Stmt::Let, got {:?}", other),
    }
}

#[test]
fn write_back_local_root_rebinds_parent_local() {
    // WriteBack { node: LocalRoot(local), edge: Field(S,1), child: r1 }
    // -> let local = path_to_update(local, [Field(S,1)], ReadRef(r1))
    let body = Block {
        stmts: vec![Stmt::Eval(Expr::WriteBack {
            node: BorrowNode::LocalRoot(vid("local")),
            edge: BorrowEdge::StructField {
                struct_id: STRUCT_S,
                field_index: 1,
            },
            child: vid("r1"),
            world: None,
        })],
        tail: BlockTail::Value(Expr::Unit),
    };
    let f = func(
        "f",
        sig(vec![param("local", t())], Type::Unit),
        body,
        FuncOpts::default(),
    );
    let mut prog = program_with(vec![(0, f)]);
    rewrite_writebacks(&mut prog);

    let stmts = &prog.functions[&0].body.stmts;
    match &stmts[0] {
        Stmt::Let { pattern, value } => {
            assert_eq!(pattern, &vec![Some(vid("local"))]);
            let expected = path_to_update(
                var("local"),
                &[BorrowEdge::StructField {
                    struct_id: STRUCT_S,
                    field_index: 1,
                }],
                Expr::ReadRef(Box::new(var("r1"))),
            );
            assert_eq!(value, &expected);
        }
        other => panic!("expected Stmt::Let, got {:?}", other),
    }
}

#[test]
fn write_back_reference_rebinds_intermediate_temp() {
    // WriteBack { node: Reference(r0), edge: Direct, child: r1 }
    // -> let r0 = path_to_update(r0, [Direct], ReadRef(r1)) = ReadRef(r1)
    let body = Block {
        stmts: vec![Stmt::Eval(Expr::WriteBack {
            node: BorrowNode::Reference(vid("r0")),
            edge: BorrowEdge::Direct,
            child: vid("r1"),
            world: None,
        })],
        tail: BlockTail::Value(Expr::Unit),
    };
    let f = func(
        "f",
        sig(vec![param("local", t())], Type::Unit),
        body,
        FuncOpts::default(),
    );
    let mut prog = program_with(vec![(0, f)]);
    rewrite_writebacks(&mut prog);

    let stmts = &prog.functions[&0].body.stmts;
    match &stmts[0] {
        Stmt::Let { pattern, value } => {
            assert_eq!(pattern, &vec![Some(vid("r0"))]);
            // path_to_update with Direct edge collapses to inner.
            assert_eq!(value, &Expr::ReadRef(Box::new(var("r1"))));
        }
        other => panic!("expected Stmt::Let, got {:?}", other),
    }
}

#[test]
fn write_back_chained_two_levels() {
    // WriteBack { Reference(r0), Field(S,1), r1 };
    // WriteBack { LocalRoot(local), Direct, r0 };
    // -> let r0 = UpdateField(S,1, r0, ReadRef(r1)); let local = ReadRef(r0);
    let body = Block {
        stmts: vec![
            Stmt::Eval(Expr::WriteBack {
                node: BorrowNode::Reference(vid("r0")),
                edge: BorrowEdge::StructField {
                    struct_id: STRUCT_S,
                    field_index: 1,
                },
                child: vid("r1"),
                world: None,
            }),
            Stmt::Eval(Expr::WriteBack {
                node: BorrowNode::LocalRoot(vid("local")),
                edge: BorrowEdge::Direct,
                child: vid("r0"),
                world: None,
            }),
        ],
        tail: BlockTail::Value(Expr::Unit),
    };
    let f = func(
        "f",
        sig(vec![param("local", t())], Type::Unit),
        body,
        FuncOpts::default(),
    );
    let mut prog = program_with(vec![(0, f)]);
    rewrite_writebacks(&mut prog);

    let stmts = &prog.functions[&0].body.stmts;
    assert_eq!(stmts.len(), 2);
    match &stmts[0] {
        Stmt::Let { pattern, value } => {
            assert_eq!(pattern, &vec![Some(vid("r0"))]);
            let expected = Expr::Update {
                step: crate::ir::path::PathStep::Field {
                    struct_id: STRUCT_S,
                    field_index: 1,
                },
                base: Box::new(var("r0")),
                value: Box::new(Expr::ReadRef(Box::new(var("r1")))),
            };
            assert_eq!(value, &expected);
        }
        other => panic!("expected Let r0, got {:?}", other),
    }
    match &stmts[1] {
        Stmt::Let { pattern, value } => {
            assert_eq!(pattern, &vec![Some(vid("local"))]);
            // Direct edge collapses to ReadRef(r0).
            assert_eq!(value, &Expr::ReadRef(Box::new(var("r0"))));
        }
        other => panic!("expected Let local, got {:?}", other),
    }
}

#[test]
fn write_back_inside_if_arm_is_rewritten() {
    // if true { WriteBack(LocalRoot(local), Direct, r1); 0 } else { 0 }
    let then_block = Block {
        stmts: vec![Stmt::Eval(Expr::WriteBack {
            node: BorrowNode::LocalRoot(vid("local")),
            edge: BorrowEdge::Direct,
            child: vid("r1"),
            world: None,
        })],
        tail: BlockTail::Value(Expr::Unit),
    };
    let else_block = Block {
        stmts: Vec::new(),
        tail: BlockTail::Value(Expr::Unit),
    };
    let body = Block {
        stmts: vec![Stmt::Eval(Expr::If {
            cond: Box::new(Expr::Const(crate::ir::Const::Bool(true))),
            then_branch: Box::new(then_block),
            else_branch: Box::new(else_block),
        })],
        tail: BlockTail::Value(Expr::Unit),
    };
    let f = func(
        "f",
        sig(vec![param("local", t())], Type::Unit),
        body,
        FuncOpts::default(),
    );
    let mut prog = program_with(vec![(0, f)]);
    rewrite_writebacks(&mut prog);

    let stmts = &prog.functions[&0].body.stmts;
    match &stmts[0] {
        Stmt::Eval(Expr::If { then_branch, .. }) => match &then_branch.stmts[0] {
            Stmt::Let { pattern, .. } => {
                assert_eq!(pattern, &vec![Some(vid("local"))]);
            }
            other => panic!("expected Let, got {:?}", other),
        },
        other => panic!("expected Eval(If), got {:?}", other),
    }
}
