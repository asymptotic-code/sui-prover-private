//! Phase 4 unit tests for the borrow-state map builder.

use crate::ir::builder::var;
use crate::ir::{Block, BlockTail, BorrowEdge, Expr, Stmt, Type, VarId};
use crate::stage_03_demut::{build_borrow_state, BorrowChain};

use super::fixtures::{func, param, sig, FuncOpts};

fn t() -> Type {
    Type::UInt(64)
}

fn vid(name: &str) -> VarId {
    VarId::from(name)
}

#[test]
fn borrow_loc_records_root_with_empty_edges() {
    // let r = BorrowLoc(local)
    let body = Block {
        stmts: vec![Stmt::Let {
            pattern: vec![Some(vid("r"))],
            value: Expr::BorrowLoc(vid("local")),
        }],
        tail: BlockTail::Value(Expr::Unit),
    };
    let f = func(
        "f",
        sig(vec![param("local", t())], Type::Unit),
        body,
        FuncOpts::default(),
    );
    let state = build_borrow_state(&f);
    assert_eq!(
        state.get(&vid("r")),
        Some(&BorrowChain {
            root: vid("local"),
            edges: Vec::new(),
        })
    );
}

#[test]
fn borrow_field_off_borrow_loc_records_one_edge() {
    // let r = BorrowField { f: 1, base: BorrowLoc(local) }
    let body = Block {
        stmts: vec![Stmt::Let {
            pattern: vec![Some(vid("r"))],
            value: Expr::Borrow {
                step: crate::ir::path::PathStep::Field {
                    struct_id: 7,
                    field_index: 1,
                },
                base: Box::new(Expr::BorrowLoc(vid("local"))),
            },
        }],
        tail: BlockTail::Value(Expr::Unit),
    };
    let f = func(
        "f",
        sig(vec![param("local", t())], Type::Unit),
        body,
        FuncOpts::default(),
    );
    let state = build_borrow_state(&f);
    assert_eq!(
        state.get(&vid("r")),
        Some(&BorrowChain {
            root: vid("local"),
            edges: vec![BorrowEdge::StructField {
                struct_id: 7,
                field_index: 1,
            }],
        })
    );
}

#[test]
fn two_step_chain_extends_through_var() {
    // let r0 = BorrowLoc(local);
    // let r1 = BorrowField { f: 0, base: Var(r0) };
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
                        struct_id: 7,
                        field_index: 0,
                    },
                    base: Box::new(var("r0")),
                },
            },
        ],
        tail: BlockTail::Value(Expr::Unit),
    };
    let f = func(
        "f",
        sig(vec![param("local", t())], Type::Unit),
        body,
        FuncOpts::default(),
    );
    let state = build_borrow_state(&f);
    assert_eq!(
        state.get(&vid("r0")),
        Some(&BorrowChain {
            root: vid("local"),
            edges: Vec::new(),
        })
    );
    assert_eq!(
        state.get(&vid("r1")),
        Some(&BorrowChain {
            root: vid("local"),
            edges: vec![BorrowEdge::StructField {
                struct_id: 7,
                field_index: 0,
            }],
        })
    );
}

#[test]
fn three_step_chain_records_full_path() {
    // let r0 = BorrowLoc(local);
    // let r1 = BorrowField { f: 0, base: Var(r0) };
    // let r2 = BorrowField { f: 1, base: Var(r1) };
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
                        struct_id: 7,
                        field_index: 0,
                    },
                    base: Box::new(var("r0")),
                },
            },
            Stmt::Let {
                pattern: vec![Some(vid("r2"))],
                value: Expr::Borrow {
                    step: crate::ir::path::PathStep::Field {
                        struct_id: 11,
                        field_index: 1,
                    },
                    base: Box::new(var("r1")),
                },
            },
        ],
        tail: BlockTail::Value(Expr::Unit),
    };
    let f = func(
        "f",
        sig(vec![param("local", t())], Type::Unit),
        body,
        FuncOpts::default(),
    );
    let state = build_borrow_state(&f);
    assert_eq!(
        state.get(&vid("r2")),
        Some(&BorrowChain {
            root: vid("local"),
            edges: vec![
                BorrowEdge::StructField {
                    struct_id: 7,
                    field_index: 0,
                },
                BorrowEdge::StructField {
                    struct_id: 11,
                    field_index: 1,
                },
            ],
        })
    );
}

#[test]
fn binding_inside_if_arm_is_recorded() {
    // if true { let r = BorrowLoc(local); 0 } else { 0 }
    let then_block = Block {
        stmts: vec![Stmt::Let {
            pattern: vec![Some(vid("r"))],
            value: Expr::BorrowLoc(vid("local")),
        }],
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
    let state = build_borrow_state(&f);
    assert_eq!(
        state.get(&vid("r")),
        Some(&BorrowChain {
            root: vid("local"),
            edges: Vec::new(),
        })
    );
}
