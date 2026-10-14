//! IR data shapes for the new Lean-backend pipeline.
//!
//! See `plans/lean-pipeline/ir.md` (in the agent repo) for the full design
//! rationale, validator invariants, and stage-by-stage variant lifecycle.
//!
//! Convention: stages reference IR types via `crate::ir::*`. Other tools that
//! want the IR import from `lean_pipeline::ir`.

pub mod abort_provenance;
pub mod analysis;
pub mod borrow;
pub mod builder;
pub mod connectives;
pub mod expr;
pub mod fmt;
pub mod function;
pub mod invariants;
pub mod names;
pub mod natives;
pub mod ops;
pub mod path;
pub mod program;
pub mod quant;
pub mod ty;
pub mod validate;
pub mod visit;

pub use abort_provenance::{
    canonical_addressed_module, is_canonical_addressed_module, AbortOriginEntry,
    AbortOriginsDocument, AbortPayloadMode, AbortProvenance, ObservedErrorKind, ABORT_ORIGINS_FILE,
    ABORT_ORIGINS_SCHEMA_VERSION, UNKNOWN_ABORT_ORIGIN_TAG,
};
pub use borrow::{BorrowEdge, BorrowNode};
pub(crate) use builder::ProverFnKind;
pub use builder::{ProgramBuilder, ProverFnIds};
pub use expr::{Block, BlockTail, Expr, MatchArm, Stmt};
pub use function::{
    AbortBit, DetBit, Effects, Function, FunctionKind, MutLevel, Param, Signature, SpecKind,
    TestExpectation, TrustReason,
};
pub use natives::{CalleeRef, NativeDecl, NativeRegistry};
pub use ops::{BinOp, BitOp, UnOp};
pub use program::{
    Field, FunctionGlobalBinding, Global, GlobalDefinition, Module, Program, StaticValue, Struct,
    SyntheticNativeOpts, Variant,
};
pub use quant::{QuantDomain, QuantifierKind};
pub use ty::{Const, Type};

/// Variable identifier. Cheap to clone.
pub type VarId = std::rc::Rc<str>;

/// Function identifier within a `Program`.
pub type FunId = usize;

/// Struct (or enum) identifier within a `Program`.
pub type StructId = usize;

/// Module identifier within a `Program`.
pub type ModId = usize;

/// Global declaration identifier within a [`Program`].
///
/// Like the other declaration IDs, this is allocated deterministically by
/// [`ProgramBuilder`] and remains stable as the program moves through the
/// pipeline.
pub type GlobalId = usize;
