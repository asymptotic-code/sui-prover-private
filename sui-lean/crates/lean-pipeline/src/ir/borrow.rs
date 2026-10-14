//! Borrow-graph nodes and edges (upstream-mirroring).
//!
//! After the bytecode->IR refactor (no summary `MutBorrow`), the IR
//! carries borrow operations directly: `Expr::BorrowLoc`, unified
//! `Expr::Borrow { step, .. }`, `Expr::WriteBack`, etc. mirror upstream
//! `Operation` variants 1:1. This module supplies the shared types
//! used by `WriteBack`.
//!
//! The active mutation-to-let and writeback passes lower these ops in
//! program order. Stage 2 emits them without resolving borrow chains.

use super::{GlobalId, StructId, VarId};

/// A borrow-graph node. Mirrors upstream's
/// `move_stackless_bytecode::stackless_bytecode::BorrowNode`. The
/// [`GlobalRoot`](Self::GlobalRoot) variant names a first-class C global;
/// it is deliberately separate from Move classic global storage, which is
/// not present in Sui Move. Used as the parent (`dst`) reference of an
/// `Expr::WriteBack`.
///
/// `LocalRoot` / `Reference` carry [`VarId`]s (our IR variable
/// identifier) instead of upstream's `TempIndex` because by the time
/// stage 2 emits the op, temps have been named (`$t0`, `$t1`, ...)
/// and from there on we always speak `VarId`.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum BorrowNode {
    /// Root storage for a mutable first-class program global. Construction is
    /// covered by the same frontend exclusivity/root-access certificate and
    /// `Program::external_global_borrows_certified` assertion as
    /// `Expr::BorrowGlobal`.
    GlobalRoot(GlobalId),
    /// Spec-only ghost global storage root, identified by the type
    /// arguments to `prover::ghost::borrow_mut<T, U>()`. Mirrors
    /// upstream's `SpecGlobalRoot(Vec<Type>)`. The pair `(T, U)`
    /// uniquely names the ghost variable.
    SpecGlobalRoot { type_args: Vec<super::Type> },
    /// A local-variable root. The borrow chain originated at this
    /// local (no incoming edges).
    LocalRoot(VarId),
    /// Another reference temp -- chains a borrow off an existing ref.
    Reference(VarId),
}

/// The operand-free structural ancestry template for a borrow path.
/// Mirrors upstream's
/// `move_stackless_bytecode::stackless_bytecode::BorrowEdge` and is
/// attached to `Expr::WriteBack` / `Expr::IsParent`. Runtime vector
/// indices and map keys belong to the forward borrow's
/// [`super::path::PathStep`], then to the rendered `Mutation.path` when
/// the borrow crosses a boundary that prevents static recovery.
///
/// Upstream's `Index(IndexEdgeKind::{Vector, Table, Custom})` and
/// `DynamicField(...)` collapse into two named variants here: `VecIndex`
/// (vector borrows) and `MapKey { key_type, value_type }` (Table /
/// Bag / VecMap / dynamic_field / dynamic_object_field / custom natives).
/// Map edges retain `(K, V)` because those types are structural metadata
/// used by validation, `AnyKey` generation, and writeback dispatch; they
/// do not retain the runtime key expression. See
/// `plans/lean-pipeline/mutable-references.md` for the runtime semantics
/// and `plans/lean-pipeline/ir.md` decision-log §19/§20.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum BorrowEdge {
    /// Identity step (no projection).
    Direct,
    /// Field projection on a struct.
    StructField {
        struct_id: StructId,
        field_index: usize,
    },
    /// Field projection inside the enum variant with declared numeric
    /// `variant` tag.
    EnumField {
        struct_id: StructId,
        variant: usize,
        field_index: usize,
    },
    /// Vector index borrow (`vector::borrow_mut(v, i)`). The runtime
    /// index lives on the borrow-construction
    /// `Expr::Borrow { step: PathStep::VecIndex(..), .. }`, not on the edge.
    VecIndex,
    /// Map-key borrow (`table::borrow_mut`, `bag::borrow_mut`,
    /// `vec_map::get_mut`, `dynamic_field::borrow_mut`,
    /// `dynamic_object_field::borrow_mut`, or any other native
    /// `IndexEdgeKind::Custom` upstream emits). The `(K, V)` Move
    /// types let the renderer collect this site into `AnyKey`; the
    /// runtime key lives on the borrow-construction
    /// `Expr::Borrow { step: PathStep::MapKey { .. }, .. }`.
    MapKey {
        key_type: super::Type,
        value_type: super::Type,
    },
    /// A nested chain. Used when upstream emits a `Hyper` over a
    /// composed path (e.g. `StructField` then `MapKey` for a
    /// table-field-on-struct borrow).
    Hyper(Vec<BorrowEdge>),
}
