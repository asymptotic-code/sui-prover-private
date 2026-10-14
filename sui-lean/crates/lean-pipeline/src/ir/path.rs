//! `PathStep` -- the operand-bearing half of the borrow-path contract.
//!
//! A `PathStep` belongs to the forward `Expr::Borrow` / `Expr::Update`
//! site and carries the runtime operand for a vector index or map key.
//! Its operand-free sibling, [`super::borrow::BorrowEdge`], is the
//! structural ancestry template attached to `WriteBack` / `IsParent`.
//! [`PathStep::to_edge`] deliberately erases runtime operands while
//! preserving that structural identity and a map edge's key/value types.
//!
//! Statically traceable writebacks recover these steps after SSA and
//! lower to `Expr::Update`. For paths that cross a function or cannot be
//! traced uniquely, the rendered `Mutation.path` remains the runtime
//! source of the actual index/key. These three roles are complementary;
//! runtime expressions do not belong on `BorrowEdge`.
//!
//! Step-4 of `plans/lean-pipeline/container-df-unification.md`:
//! `Expr::Borrow { step, base }` / `Expr::Update { step, base, value }`
//! replace the per-container constructor pairs
//! (`BorrowField`/`UpdateField`, `BorrowVecIndex`/`UpdateVec`,
//! `BorrowMapKey`/--) so every future container joins by adding ONE
//! `PathStep` variant instead of N `Expr` variants times every walker.

use super::borrow::BorrowEdge;
use super::expr::Expr;
use super::{StructId, Type, VarId};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum PathStep {
    /// Struct-field projection.
    Field {
        struct_id: StructId,
        field_index: usize,
    },
    /// Field projection inside the enum variant with declared numeric
    /// `variant` tag.
    VariantField {
        struct_id: StructId,
        variant: usize,
        field_index: usize,
    },
    /// Vector element at a runtime index.
    VecIndex(Box<Expr>),
    /// Map entry at a runtime key (`table` / `bag` / `vec_map` /
    /// `dynamic_field` / `dynamic_object_field` borrows). `key_type`
    /// drives the renderer's `AnyKey.k_<...>` dispatch; `value_type`
    /// is the borrowed value's Move type.
    MapKey {
        key: Box<Expr>,
        key_type: Type,
        value_type: Type,
        /// `Some(v)` => this map-key borrow's value is supplied
        /// EXTERNALLY by `v` (a prior `store_(bag_)borrow` read from
        /// `World`), not by a lookup into `base.val`. Used by
        /// `dynamic_field_rewrite` to model a dynamic-field borrow as
        /// a path-EXTENDING borrow off the UID mutation (so the df key
        /// rides `child.path` and the escaping writeback can recover
        /// it) while the value comes from World. The renderer emits
        /// `borrowMapKey base key (fun _ _ => v)`. `None` for ordinary
        /// in-value map borrows (lookup into `base.val`).
        df_value: Option<VarId>,
    },
}

impl PathStep {
    /// The step's runtime-operand expressions (vec index / map key),
    /// for walkers. Field steps have none.
    pub fn exprs(&self) -> impl Iterator<Item = &Expr> {
        match self {
            PathStep::Field { .. } | PathStep::VariantField { .. } => [None, None],
            PathStep::VecIndex(i) => [Some(i.as_ref()), None],
            PathStep::MapKey { key, .. } => [Some(key.as_ref()), None],
        }
        .into_iter()
        .flatten()
    }

    /// Mutable variant of [`PathStep::exprs`].
    pub fn exprs_mut(&mut self) -> impl Iterator<Item = &mut Expr> {
        match self {
            PathStep::Field { .. } | PathStep::VariantField { .. } => [None, None],
            PathStep::VecIndex(i) => [Some(i.as_mut()), None],
            PathStep::MapKey { key, .. } => [Some(key.as_mut()), None],
        }
        .into_iter()
        .flatten()
    }

    /// The operand-free borrow-graph edge for this step.
    pub fn to_edge(&self) -> BorrowEdge {
        match self {
            PathStep::Field {
                struct_id,
                field_index,
            } => BorrowEdge::StructField {
                struct_id: *struct_id,
                field_index: *field_index,
            },
            PathStep::VariantField {
                struct_id,
                variant,
                field_index,
            } => BorrowEdge::EnumField {
                struct_id: *struct_id,
                variant: *variant,
                field_index: *field_index,
            },
            PathStep::VecIndex(_) => BorrowEdge::VecIndex,
            PathStep::MapKey {
                key_type,
                value_type,
                ..
            } => BorrowEdge::MapKey {
                key_type: key_type.clone(),
                value_type: value_type.clone(),
            },
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn to_edge_erases_runtime_operands_but_preserves_structure_and_map_types() {
        let vec_a = PathStep::VecIndex(Box::new(Expr::Var(VarId::from("i"))));
        let vec_b = PathStep::VecIndex(Box::new(Expr::Var(VarId::from("j"))));
        assert_ne!(vec_a, vec_b);
        assert_eq!(vec_a.to_edge(), BorrowEdge::VecIndex);
        assert_eq!(vec_a.to_edge(), vec_b.to_edge());

        let map_a = PathStep::MapKey {
            key: Box::new(Expr::Var(VarId::from("key_a"))),
            key_type: Type::UInt(64),
            value_type: Type::Bool,
            df_value: Some(VarId::from("external_value")),
        };
        let map_b = PathStep::MapKey {
            key: Box::new(Expr::Var(VarId::from("key_b"))),
            key_type: Type::UInt(64),
            value_type: Type::Bool,
            df_value: None,
        };
        assert_ne!(map_a, map_b);
        assert_eq!(
            map_a.to_edge(),
            BorrowEdge::MapKey {
                key_type: Type::UInt(64),
                value_type: Type::Bool,
            }
        );
        assert_eq!(map_a.to_edge(), map_b.to_edge());

        assert_eq!(
            PathStep::Field {
                struct_id: 7,
                field_index: 3,
            }
            .to_edge(),
            BorrowEdge::StructField {
                struct_id: 7,
                field_index: 3,
            }
        );
        assert_eq!(
            PathStep::VariantField {
                struct_id: 9,
                variant: 2,
                field_index: 1,
            }
            .to_edge(),
            BorrowEdge::EnumField {
                struct_id: 9,
                variant: 2,
                field_index: 1,
            }
        );
    }
}
