//! Stage 10 -- bounded-nat lowering.
//!
//! See `plans/lean-pipeline/stage-10-bounded-nat.md`.
//!
//! ## Scope
//!
//! Rewrites every `Expr::BinOp` and `Expr::UnOp { op: Cast(_), .. }`
//! whose operand has type `Type::UInt(N)` into a `Call` against a
//! synthetic `BoundedU{N}_<op>` native registered in
//! [`prelude_fids`].
//!
//! After stage 10:
//!
//! - No `Expr::BinOp` on UInt operands survives in any function body.
//! - No `Expr::UnOp { op: Cast(_), operand }` with a UInt operand
//!   survives.
//! - For each op that can abort (arithmetic / shifts / narrowing
//!   casts), a `Spec(Aborts)` companion `BoundedU{N}_<op>_aborts` is
//!   registered with `target` = the main FunId. Stage 7's existing
//!   `aborts_map` collection (keyed on `FunctionKind::Spec(Aborts)`)
//!   picks them up automatically.
//!
//! Modular arithmetic (`WrappingAdd`/`WrappingSub`/`WrappingMul`), bitwise
//! (`BitAnd`/`BitOr`/`BitXor`/`BitNot`), and comparison
//! (`Eq`/`Neq`/`Lt`/`Le`/`Gt`/`Ge` plus signed variants) route through the prelude
//! too but get no aborts companion -- their native registrations
//! carry `Effects::PURE` (i.e. `AbortBit::Total`), so stage 7's
//! abort-companion walker contributes `Bool(false)` for them. They
//! appear in the IR purely for uniformity (no raw `BinOp` on
//! `UInt(N)` survives).
//!
//! Logical ops `BinOp::And`/`Or` operate on `Bool` and are not
//! rewritten.
//!
//! ## Ordering
//!
//! The driver runs stage 10 at two semantic boundaries. The pre-stage-7 pass
//! follows a narrow normalization of aborting UInt arithmetic, making partial
//! operations visible when stage 7 builds `.aborts` companions. The final pass
//! follows full post-cleanup auto-dereference normalization and establishes the
//! render representation. The former immediate post-stage-7 pass was
//! redundant: active stages 7 and 8 synthesize no UInt operations.
//!
//! The stage-10 invariant remains live through the render gate after the final
//! pass, so a later stage that introduces a raw UInt operation fails the final
//! render contract.
//!
//! ## Idempotency
//!
//! An immediate second invocation, with no intervening IR mutation, finds zero
//! raw `BinOp` / `Cast` sites and returns `Ok(())` without mutation. The
//! driver's final invocation can still find operations exposed by intervening
//! normalization. Already-present exact BoundedU declarations are never
//! re-registered; a same-named non-intrinsic declaration remains separate.

pub mod postcondition;
pub mod prelude_fids;
pub mod rewrite;

#[cfg(test)]
mod tests;

use crate::ir::analysis::type_of::TypeOfError;
use crate::ir::{FunId, Program};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Stage10RewritePhase {
    CollectNeeds,
    Rewrite,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Stage10FunctionFailure {
    pub function: FunId,
    pub phase: Stage10RewritePhase,
    pub err: TypeOfError,
}

/// Errors produced by stage 10.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Stage10Error {
    /// Type inference failed while collecting or rewriting one or
    /// more function bodies. Every failed body remains unchanged.
    FunctionFailures(Vec<Stage10FunctionFailure>),
    /// Postcondition check failed: a raw `BinOp` / `Cast` on UInt
    /// survived. Includes a human-readable diagnostic.
    Postcondition(String),
}

/// Run stage 10 over `program`. Idempotent.
pub fn run(program: &mut Program) -> Result<(), Stage10Error> {
    rewrite::run(program)?;
    postcondition::check(program)?;
    Ok(())
}
