//! Global invariant registry + runners.
//!
//! [`all_invariants`] returns every registered invariant. It is the
//! single source of truth -- adding a new invariant means registering it
//! here.
//!
//! [`verify_at`] runs every invariant that applies at a given stage
//! (i.e. `established_by <= stage <= held_through` in pipeline order).
//! [`verify_precondition`] runs every invariant that should already
//! hold on `stage`'s input (i.e. `established_by < stage <= held_through`).
//!
//! Both runners collect EVERY violation rather than short-circuiting on
//! the first -- the caller sees a complete view of what the IR is
//! violating, not just the first thing that broke.

use crate::ir::Program;

use super::traits::{applies_as_precondition, applies_at, Invariant, InvariantViolation, Stage};

/// Return every registered invariant.
///
/// Aggregates `baseline::INVARIANTS` and `stages::INVARIANTS`. Order
/// is module-then-registration-order; consumers should treat the
/// result as a set, not a list. Tests that need a stable order
/// should sort by `inv.id()`.
///
/// Cached after the first call -- the underlying slices are static,
/// so the aggregate `Vec` only needs to be built once per process.
pub fn all_invariants() -> Vec<&'static dyn Invariant> {
    use std::sync::OnceLock;
    static CACHE: OnceLock<Vec<&'static dyn Invariant>> = OnceLock::new();
    CACHE
        .get_or_init(|| {
            let mut out: Vec<&'static dyn Invariant> = Vec::new();
            out.extend(super::baseline::INVARIANTS.iter().copied());
            out.extend(super::stages::INVARIANTS.iter().copied());
            out
        })
        .clone()
}

/// Run every invariant that applies at `stage`.
///
/// On success: `Ok(())`. On failure: `Err(violations)` containing every
/// violation found across every applicable invariant.
pub fn verify_at(stage: Stage, program: &Program) -> Result<(), Vec<InvariantViolation>> {
    let mut violations = Vec::new();
    for inv in all_invariants() {
        if !applies_at(inv, stage) {
            continue;
        }
        if let Err(vs) = inv.check(program) {
            violations.extend(vs);
        }
    }
    if violations.is_empty() {
        Ok(())
    } else {
        Err(violations)
    }
}

/// Run every invariant that should hold as `stage`'s **precondition**.
///
/// The precondition set is "every invariant whose lifespan covers
/// `stage` but was established before `stage`". This is the contract
/// `stage`'s `run()` is allowed to assume about its input.
///
/// Note: invariants established by `stage` itself are NOT in the
/// precondition set -- by definition, `stage` is the one establishing
/// them.
pub fn verify_precondition(stage: Stage, program: &Program) -> Result<(), Vec<InvariantViolation>> {
    let mut violations = Vec::new();
    for inv in all_invariants() {
        if !applies_as_precondition(inv, stage) {
            continue;
        }
        if let Err(vs) = inv.check(program) {
            violations.extend(vs);
        }
    }
    if violations.is_empty() {
        Ok(())
    } else {
        Err(violations)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn empty_program_passes_at_every_stage() {
        let p = Program::default();
        for stage in [
            Stage::Baseline,
            Stage::S02IrCfg,
            Stage::S03MutToLet,
            Stage::S04Effects,
            Stage::S05Ssa,
            Stage::S10BoundedNat,
            Stage::S07Dejumps,
            Stage::S06LetInline,
            Stage::S08Loops,
            Stage::Render,
        ] {
            assert!(
                verify_at(stage, &p).is_ok(),
                "verify_at({:?}) should pass on empty program",
                stage,
            );
            assert!(
                verify_precondition(stage, &p).is_ok(),
                "verify_precondition({:?}) should pass on empty program",
                stage,
            );
        }
    }

    #[test]
    fn invariant_ids_are_unique() {
        let mut ids: Vec<&'static str> = all_invariants().iter().map(|i| i.id()).collect();
        ids.sort();
        let original_len = ids.len();
        ids.dedup();
        assert_eq!(
            ids.len(),
            original_len,
            "every invariant must have a unique id",
        );
    }

    #[test]
    fn baseline_invariants_held_through_at_least_program_build() {
        // Sanity: every baseline-established invariant must be held
        // through at least one further stage (otherwise it's
        // baseline-AND-only-baseline, which doesn't make sense -- the
        // post-stage-2 program is the first thing the renderer would
        // ever see).
        for inv in all_invariants() {
            if inv.established_by() == Stage::Baseline {
                assert!(
                    inv.held_through().at_or_after(Stage::S02IrCfg),
                    "baseline invariant {} ends before stage 2",
                    inv.id(),
                );
            }
        }
    }
}
