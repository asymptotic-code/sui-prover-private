//! Phase 1 unit tests for `path_to_update`.
//!
//! Covers `Direct`, `Field`, `EnumField`, two-deep `Field;Field`,
//! `Hyper`-flattening, and the empty-edges base case. The
//! `Index { Vector }` variant is deferred to Phase 4 (see
//! `writebacks.rs` module docs).

use crate::ir::builder::{lit_u64, var};
use crate::ir::{BorrowEdge, Expr};
use crate::stage_03_demut::path_to_update;

const STRUCT_S: usize = 7;
const STRUCT_T: usize = 11;

#[test]
fn empty_edges_returns_inner_unchanged() {
    let result = path_to_update(var("x"), &[], lit_u64(42));
    assert_eq!(result, lit_u64(42));
}

#[test]
fn direct_edge_is_identity() {
    let result = path_to_update(var("x"), &[BorrowEdge::Direct], lit_u64(42));
    assert_eq!(result, lit_u64(42));
}

#[test]
fn field_edge_emits_update_field() {
    let edges = [BorrowEdge::StructField {
        struct_id: STRUCT_S,
        field_index: 1,
    }];
    let result = path_to_update(var("x"), &edges, lit_u64(42));
    let expected = Expr::Update {
        step: crate::ir::path::PathStep::Field {
            struct_id: STRUCT_S,
            field_index: 1,
        },
        base: Box::new(var("x")),
        value: Box::new(lit_u64(42)),
    };
    assert_eq!(result, expected);
}

#[test]
fn enum_field_edge_emits_tagged_variant_update() {
    let edges = [BorrowEdge::EnumField {
        struct_id: STRUCT_S,
        variant: 2,
        field_index: 0,
    }];
    let result = path_to_update(var("x"), &edges, lit_u64(7));
    let expected = Expr::Update {
        step: crate::ir::path::PathStep::VariantField {
            struct_id: STRUCT_S,
            variant: 2,
            field_index: 0,
        },
        base: Box::new(var("x")),
        value: Box::new(lit_u64(7)),
    };
    assert_eq!(result, expected);
}

#[test]
#[should_panic(expected = "nested BorrowEdge::EnumField requires a tagged value projection")]
fn nested_enum_field_fails_closed() {
    let edges = [
        BorrowEdge::EnumField {
            struct_id: STRUCT_S,
            variant: 2,
            field_index: 0,
        },
        BorrowEdge::StructField {
            struct_id: STRUCT_T,
            field_index: 1,
        },
    ];
    let _ = path_to_update(var("x"), &edges, lit_u64(7));
}

#[test]
fn two_deep_field_field_nests_update_field() {
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
    let result = path_to_update(var("x"), &edges, lit_u64(99));
    let inner_update = Expr::Update {
        step: crate::ir::path::PathStep::Field {
            struct_id: STRUCT_T,
            field_index: 2,
        },
        base: Box::new(Expr::Field {
            struct_id: STRUCT_S,
            field_index: 0,
            base: Box::new(var("x")),
        }),
        value: Box::new(lit_u64(99)),
    };
    let expected = Expr::Update {
        step: crate::ir::path::PathStep::Field {
            struct_id: STRUCT_S,
            field_index: 0,
        },
        base: Box::new(var("x")),
        value: Box::new(inner_update),
    };
    assert_eq!(result, expected);
}

#[test]
fn hyper_flattens_into_chain() {
    // Hyper at the head of a chain is equivalent to inlining its
    // sub-edges in place.
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
    let result = path_to_update(var("x"), &edges, lit_u64(99));
    let expected = path_to_update(var("x"), &inner, lit_u64(99));
    assert_eq!(result, expected);
}

#[test]
fn hyper_then_field_continues_chain() {
    // [Hyper([Field f0]), Field f1] is the same as [Field f0, Field f1].
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
    let result = path_to_update(var("x"), &edges, lit_u64(7));

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
    let expected = path_to_update(var("x"), &flat, lit_u64(7));
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
    let result = path_to_update(var("x"), &edges, lit_u64(42));
    let expected = path_to_update(
        var("x"),
        &[BorrowEdge::StructField {
            struct_id: STRUCT_S,
            field_index: 1,
        }],
        lit_u64(42),
    );
    assert_eq!(result, expected);
}
