//! Pipeline-level invariants framework.
//!
//! Each invariant is a `Invariant` impl tagged with the stages where
//! it must hold. Registering an invariant once makes it auto-checked
//! at every applicable stage's postcondition AND at every later
//! stage's precondition. See `plans/lean-pipeline/invariants.md`.
//!
//! ## Layout
//!
//! - [`traits`]: the `Invariant` trait, `Stage` enum, `pipeline_order`.
//! - [`registry`]: `all_invariants`, `verify_at`, `verify_precondition`.
//! - [`baseline`]: cross-pipeline well-formedness and render-form invariants.
//! - [`stages`]: stage-established invariants (per-stage promises).
//!
//! ## Adding a new invariant
//!
//! 1. Write a unit-struct `Invariant` impl in the appropriate module.
//! 2. Add a `&'static` reference to that struct to the corresponding
//!    `INVARIANTS` slice (`baseline::INVARIANTS` or `stages::INVARIANTS`).
//! 3. The framework picks it up automatically -- no other wiring.

pub mod baseline;
#[cfg(test)]
mod cross_stage_tests;
pub mod registry;
pub mod report;
pub mod stages;
pub mod traits;

pub use registry::{all_invariants, verify_at, verify_precondition};
pub use report::{display_table, format_result};
pub use traits::{pipeline_order, Invariant, InvariantViolation, Stage};
