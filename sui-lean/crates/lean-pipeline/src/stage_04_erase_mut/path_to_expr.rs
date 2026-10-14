//! `path_to_expr` -- read-side mirror of stage 3's `path_to_update`.
//!
//! Given a borrow chain (root `VarId` + sequence of `BorrowEdge`s),
//! build the projection expression that reads the value at the end of
//! the chain.
//!
//! Stage 3's `path_to_update` substitutes a new `inner` value at the
//! chain's leaf; this helper has no leaf value to substitute -- it
//! just builds the projection.
//!
//! `Direct` is the identity step and struct fields produce nested
//! `Expr::Field`. `Hyper(sub)` flattens at the head of the chain.
//! Enum-field and container projections fail closed: this retained
//! prototype has no pure tagged-value projection or runtime key/index source.

use crate::ir::{BorrowEdge, Expr, VarId};

// Stage 4 consumes stage 3's `BorrowChain` directly (re-exported
// from `crate::stage_03_demut`); no local mirror type is needed.

/// Build a read expression that projects from `Var(root)` along
/// `edges`. Returns `Var(root)` if `edges` is empty.
///
/// Pure recursion. `Hyper(sub)` flattens at the head of the chain and
/// `Direct` is identity. Struct fields produce nested `Expr::Field`;
/// enum and container edges panic because this prototype has no tagged
/// projection or runtime key/index source.
pub fn path_to_expr(root: VarId, edges: &[BorrowEdge]) -> Expr {
    apply_edges(Expr::Var(root), edges)
}

fn apply_edges(base: Expr, edges: &[BorrowEdge]) -> Expr {
    if edges.is_empty() {
        return base;
    }
    let head = &edges[0];
    let rest = &edges[1..];
    match head {
        BorrowEdge::Direct => apply_edges(base, rest),
        BorrowEdge::StructField {
            struct_id,
            field_index,
        } => apply_edges(
            Expr::Field {
                struct_id: *struct_id,
                field_index: *field_index,
                base: Box::new(base),
            },
            rest,
        ),
        BorrowEdge::EnumField {
            struct_id: _,
            variant: _,
            field_index: _,
        } => {
            unimplemented!("path_to_expr: BorrowEdge::EnumField requires a tagged value projection")
        }
        BorrowEdge::VecIndex => {
            unimplemented!(
                "path_to_expr: BorrowEdge::VecIndex deferred -- requires runtime-index source"
            )
        }
        BorrowEdge::MapKey { .. } => {
            unimplemented!(
                "path_to_expr: BorrowEdge::MapKey deferred -- active path uses Mutation prelude"
            )
        }
        BorrowEdge::Hyper(sub) => {
            // Flatten: prepend the Hyper's inner edges to the rest
            // of the chain and recurse.
            let mut flat: Vec<BorrowEdge> = sub.clone();
            flat.extend_from_slice(rest);
            apply_edges(base, &flat)
        }
    }
}
