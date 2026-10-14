//! Phase 1 unit tests for `path_to_expr`.
//!
//! Covers `Direct`, `Field`, fail-closed `EnumField`, two-deep `Field;Field`,
//! `Hyper`-flattening, the empty-edges base case, and the
//! `Direct;Field` skip-Direct case. The `Index { Vector }` variant
//! is deferred (mirrors `path_to_update`).

use crate::ir::{BorrowEdge, Expr, VarId};
use crate::stage_04_erase_mut::path_to_expr;

const STRUCT_S: usize = 7;
const STRUCT_T: usize = 11;

fn x_root() -> VarId {
    VarId::from("x")
}

fn x_var() -> Expr {
    Expr::Var(x_root())
}

#[test]
fn empty_edges_returns_root_var() {
    let result = path_to_expr(x_root(), &[]);
    assert_eq!(result, x_var());
}

#[test]
fn direct_edge_is_identity() {
    let result = path_to_expr(x_root(), &[BorrowEdge::Direct]);
    assert_eq!(result, x_var());
}

#[test]
fn field_edge_emits_field() {
    let edges = [BorrowEdge::StructField {
        struct_id: STRUCT_S,
        field_index: 1,
    }];
    let result = path_to_expr(x_root(), &edges);
    let expected = Expr::Field {
        struct_id: STRUCT_S,
        field_index: 1,
        base: Box::new(x_var()),
    };
    assert_eq!(result, expected);
}

#[test]
#[should_panic(expected = "BorrowEdge::EnumField requires a tagged value projection")]
fn enum_field_edge_fails_closed() {
    let edges = [BorrowEdge::EnumField {
        struct_id: STRUCT_S,
        variant: 2,
        field_index: 0,
    }];
    let _ = path_to_expr(x_root(), &edges);
}

#[test]
fn two_deep_field_field_nests_field() {
    let edges = [
        BorrowEdge::StructField {
            struct_id: STRUCT_S,
            field_index: 0,
        },
        BorrowEdge::StructField {
            struct_id: STRUCT_T,
            field_index: 2,
        },
    ];
    let result = path_to_expr(x_root(), &edges);
    let inner = Expr::Field {
        struct_id: STRUCT_S,
        field_index: 0,
        base: Box::new(x_var()),
    };
    let expected = Expr::Field {
        struct_id: STRUCT_T,
        field_index: 2,
        base: Box::new(inner),
    };
    assert_eq!(result, expected);
}

#[test]
fn hyper_flattens_into_chain() {
    let inner = vec![
        BorrowEdge::StructField {
            struct_id: STRUCT_S,
            field_index: 0,
        },
        BorrowEdge::StructField {
            struct_id: STRUCT_T,
            field_index: 2,
        },
    ];
    let edges = [BorrowEdge::Hyper(inner.clone())];
    let result = path_to_expr(x_root(), &edges);
    let expected = path_to_expr(x_root(), &inner);
    assert_eq!(result, expected);
}

#[test]
fn hyper_then_field_continues_chain() {
    let edges = [
        BorrowEdge::Hyper(vec![BorrowEdge::StructField {
            struct_id: STRUCT_S,
            field_index: 0,
        }]),
        BorrowEdge::StructField {
            struct_id: STRUCT_T,
            field_index: 2,
        },
    ];
    let result = path_to_expr(x_root(), &edges);
    let flat = [
        BorrowEdge::StructField {
            struct_id: STRUCT_S,
            field_index: 0,
        },
        BorrowEdge::StructField {
            struct_id: STRUCT_T,
            field_index: 2,
        },
    ];
    let expected = path_to_expr(x_root(), &flat);
    assert_eq!(result, expected);
}

#[test]
fn direct_then_field_skips_direct() {
    let edges = [
        BorrowEdge::Direct,
        BorrowEdge::StructField {
            struct_id: STRUCT_S,
            field_index: 1,
        },
    ];
    let result = path_to_expr(x_root(), &edges);
    let expected = path_to_expr(
        x_root(),
        &[BorrowEdge::StructField {
            struct_id: STRUCT_S,
            field_index: 1,
        }],
    );
    assert_eq!(result, expected);
}

#[test]
fn hyper_empty_is_no_op() {
    // Edge case: a Hyper with no inner edges is equivalent to
    // skipping the head.
    let edges = [
        BorrowEdge::Hyper(vec![]),
        BorrowEdge::StructField {
            struct_id: STRUCT_S,
            field_index: 0,
        },
    ];
    let result = path_to_expr(x_root(), &edges);
    let expected = path_to_expr(
        x_root(),
        &[BorrowEdge::StructField {
            struct_id: STRUCT_S,
            field_index: 0,
        }],
    );
    assert_eq!(result, expected);
}
