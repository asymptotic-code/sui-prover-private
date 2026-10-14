//! Stage 2 -- Bytecode Structured CFG -> IR Structured CFG.
//!
//! Consumes a [`BytecodeCfg`](crate::stage_01_bytecode_cfg::BytecodeCfg)
//! produced by stage 1 plus the upstream `FunctionTarget` and translates
//! it into IR. Every `Region` lifts to a [`Block`](crate::ir::Block);
//! every Move stackless [`Bytecode`] op lifts to one or more
//! [`Stmt`](crate::ir::Stmt) / [`Expr`](crate::ir::Expr) nodes; every
//! `Region::Term` lifts to the matching `BlockTail` variant.
//!
//! Stage 2 emits IR that **still contains** mutable references
//! (eliminated by stage 3), `Expr::While` and jump tails (both
//! eliminated by stage 7's dejumps), and raw arithmetic (wrapped by
//! stage 10's bounded-nat). Each later stage promises which variants it
//! removes; see `plans/lean-pipeline/ir.md` "Stage-by-stage variant
//! lifecycle".
//!
//! The full design lives in `plans/lean-pipeline/stage-02-ir-cfg.md`.
//!
//! ## Implementation
//!
//! [`run`] lifts one structured function. [`run_pipeline`] owns the
//! package-wide prepasses, module/function lifting, and the downstream
//! transformation sequence. Unsupported bytecode shapes are reported as
//! [`Stage2Error`] values; permissive pipeline mode can replace an
//! unsupported function with a diagnostic stub.
//!
//! Structural correctness is enforced by the baseline invariant registry,
//! which is checked between stages and again at the render gate.
//!
//! ## Borrow handling
//!
//! Stage 2 lifts upstream borrow ops to explicit IR variants
//! (`Operation::BorrowLoc` -> `Expr::BorrowLoc`,
//! `Operation::BorrowField` -> `Expr::BorrowField`,
//! `Operation::WriteBack(node, edge)` -> `Expr::WriteBack { node,
//! edge, child }`, etc.), translates the borrow edges supplied by the
//! upstream instrumentation, and records map-key types for native and
//! user-defined borrow wrappers. Later stages reposition mutable writes,
//! thread effects, and lower the explicit write-back chains.

mod canonicalize_terminators;
mod consts;
mod dynamic_field_rewrite;
mod dynamic_fields;
pub(crate) mod effects;
mod function_lift;
mod lift_region;
mod module_lift;
mod mutation_natives;
pub(crate) mod natives;
mod operand_normalization;
mod pipeline;
mod translate_op;
mod translate_quant;
mod types;
mod wrapper_kv;

use move_stackless_bytecode::function_target::FunctionTarget;

use crate::ir::{FunId, ProgramBuilder};
use crate::stage_01_bytecode_cfg::BytecodeCfg;

pub use consts::{translate_constant, translate_constant_with_type};
pub use module_lift::lift_module;
// `natives::NATIVE_FUNCTIONS` is per-function now; no module-level
// view to re-export. Callers consult `natives::is_native_function`.
pub use effects::classify_effects;
pub use natives::has_ext_world;
// The native effect classification is the emission-side half of the
// world-threading contract: a `GlobalMut` + `world_writes` native gets a
// trailing `world` argument appended to every call site (stage 4) and a
// trailing `World` slot appended to every destructure. The shipped Lean
// model must declare exactly that shape. `tests/table_native_lemmas.rs`
// reads this to build the Lean side of the contract from the same source
// of truth, so the two halves cannot drift silently.
pub use natives::native_effects;
pub use pipeline::{
    run as run_pipeline, run_with_abort_payload_mode, run_with_mode, DiagnosticSeverity,
    DriverError, FailureMode, PipelineDiagnostic, PipelineOutput,
};
pub use types::translate_type;

/// Errors produced by stage 2. See `plans/lean-pipeline/stage-02-ir-cfg.md`
/// "Reject cases" for full semantics.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Stage2Error {
    /// `Bytecode::Call` resolves to a function `qid` we couldn't
    /// locate in the Move model. Should be impossible if upstream's
    /// pipeline produced valid bytecode; defensive guard.
    UnknownFunction { module: String, function: String },

    /// A `Region::Switch` branch's `UnpackVariant` struct/variant
    /// doesn't match the `Region::Switch::switch_at`'s `VariantSwitch`.
    /// Indicates stage 1 produced a malformed Switch.
    MalformedMatchArm {
        switch_at: move_binary_format::file_format::CodeOffset,
        branch_index: usize,
    },

    /// `dynamic_field::*` callsite has a non-UID parent. Move's type
    /// system normally enforces `&mut UID`; this fires defensively if
    /// upstream's bytecode somehow violates that.
    NonUidDynamicFieldParent {
        pc: move_binary_format::file_format::CodeOffset,
        parent_type: String,
    },

    /// A Move type variant we don't lift -- spec-only types like
    /// `Num`, `Range`, `EventStore`, `Fun`, `TypeDomain`,
    /// `ResourceDomain`, or type-checking temporaries (`Var`, `Error`)
    /// that should never appear in fully-checked bytecode. The
    /// `description` is a human-readable rendering of the type for
    /// the error message.
    UnsupportedMoveType { description: String },

    /// A bytecode op produced an unexpected number of `dests` or
    /// `srcs`. Defensive guard against upstream pipeline drift; in
    /// well-formed Move bytecode, every `Operation` has a known
    /// arity.
    MalformedArity {
        op: String,
        slot: String,
        expected: usize,
        actual: usize,
        pc: move_binary_format::file_format::CodeOffset,
    },

    /// Placeholder while stage 2 is being built out incrementally.
    /// `reason` is a short tag identifying which translation case
    /// fired (e.g. "Operation::Stop", "BorrowEdge::DynamicField",
    /// "Up::ReturnPlaceholder"). Removed once the full lifting path
    /// is in place.
    NotImplemented { reason: &'static str },
}

impl Stage2Error {
    pub(crate) fn malformed_arity(
        op: &str,
        slot: &str,
        expected: usize,
        actual: usize,
        pc: move_binary_format::file_format::CodeOffset,
    ) -> Self {
        Stage2Error::MalformedArity {
            op: op.to_string(),
            slot: slot.to_string(),
            expected,
            actual,
            pc,
        }
    }
}

/// Translate a structured CFG produced by stage 1 into IR, registering
/// the resulting `Function` in `prog`.
///
/// `prog` is shared across all stage-1+2 calls for a Move package --
/// stage 2 allocates `FunId` / `StructId` / `ModId` deterministically
/// through it so cross-function references resolve consistently.
///
/// On success, returns the [`FunId`] under which the function was
/// registered. The function is also reachable via `prog.program()` for
/// callers that need to inspect it.
pub fn run(
    cfg: BytecodeCfg,
    target: &FunctionTarget,
    prog: &mut ProgramBuilder,
) -> Result<FunId, Stage2Error> {
    function_lift::lift_function(cfg, target, prog)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn stage2_error_variants_round_trip_through_clone() {
        // Smoke test: each constructor compiles, Clone/PartialEq work.
        let e1 = Stage2Error::NotImplemented { reason: "test" };
        let e2 = e1.clone();
        assert_eq!(e1, e2);

        let e3 = Stage2Error::UnknownFunction {
            module: "m".to_string(),
            function: "f".to_string(),
        };
        assert_ne!(e1, e3);
    }
}
