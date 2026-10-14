//! Invariant trait, stage ordering, and violation type.
//!
//! Each pipeline-level invariant is a unit struct that implements
//! [`Invariant`]. The framework runs every invariant whose
//! `established_by..held_through` range covers a given stage at the end
//! of that stage (via [`super::registry::verify_at`]) and at the start of
//! the next stage (via [`super::registry::verify_precondition`]).
//!
//! See `plans/lean-pipeline/invariants.md` for the design.

use crate::ir::{FunId, Program};

/// Pipeline stage tags used as endpoints in invariant lifespans.
///
/// `Baseline` is a pseudo-stage representing the well-formedness
/// constraints any program built via `ProgramBuilder` must satisfy --
/// the baseline IR validator's checks all carry this tag.
///
/// `Render` is a pseudo-stage representing "the IR is about to be
/// handed to the renderer". An invariant whose `held_through` is
/// `Render` must still hold immediately before render-time.
///
/// **Ordering by enum-discriminant is NOT pipeline order.** Use
/// [`pipeline_order`] for comparisons; the discriminant is just an id.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Stage {
    /// Pseudo-stage: well-formedness checks that hold from program-build
    /// time onward. Established by `ProgramBuilder` / stage 2.
    Baseline,
    /// Stage 2: bytecode -> IR.
    S02IrCfg,
    /// Stage 3 (active): mut-to-let lowering of WriteRef/WriteBack.
    S03MutToLet,
    /// Stage 4 (active): effects threading via `world: World`.
    S04Effects,
    /// Stage 5: SSA construction.
    S05Ssa,
    /// Stage 6: let-inlining + DCE.
    S06LetInline,
    /// Stage 7: dejumps + spec companion extraction.
    S07Dejumps,
    /// Stage 8: final loop-helper effect propagation.
    S08Loops,
    /// Stage 10: bounded-nat lowering.
    S10BoundedNat,
    /// Pseudo-stage: the renderer is about to consume the IR.
    Render,
}

/// Position of a stage in the **active pipeline order**.
///
/// Active path per `stage_02_ir_cfg::pipeline::run_with_mode`:
///
///   Baseline -> S02 -> S03MutToLet -> S04Effects -> S05Ssa
///   -> S10BoundedNat -> S07Dejumps -> S06LetInline -> S08Loops
///   -> Render
///
/// `S10BoundedNat` marks the first establishment boundary. The same
/// idempotent lowering runs again after `S08Loops`, following final operand
/// normalization, before the render contract is checked.
///
/// Note that stage-numbering and pipeline-ordering do NOT agree:
/// stage 10 runs before stage 7, and stage 6 runs after stage 7.
/// Invariant lifespan comparisons use this ordering, not the
/// enum-variant order.
pub fn pipeline_order(s: Stage) -> u8 {
    match s {
        Stage::Baseline => 0,
        Stage::S02IrCfg => 1,
        Stage::S03MutToLet => 2,
        Stage::S04Effects => 3,
        Stage::S05Ssa => 4,
        Stage::S10BoundedNat => 5,
        Stage::S07Dejumps => 6,
        Stage::S06LetInline => 7,
        Stage::S08Loops => 8,
        Stage::Render => 9,
    }
}

impl Stage {
    /// Pipeline-order position (see [`pipeline_order`]).
    pub fn order(self) -> u8 {
        pipeline_order(self)
    }

    /// `self` runs at-or-before `other` in the active pipeline order.
    pub fn at_or_before(self, other: Stage) -> bool {
        self.order() <= other.order()
    }

    /// `self` runs at-or-after `other` in the active pipeline order.
    pub fn at_or_after(self, other: Stage) -> bool {
        self.order() >= other.order()
    }

    /// `self` runs strictly before `other` in the active pipeline order.
    pub fn strictly_before(self, other: Stage) -> bool {
        self.order() < other.order()
    }
}

/// A single failed invariant check.
///
/// Carries the invariant id (for greppability), an optional function
/// id to point at the offending site, and a free-form detail string.
/// Tests use `invariant` + `function` for matching; `detail` is for
/// human consumption.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InvariantViolation {
    /// The invariant's stable id (e.g. `"no-write-ref-in-body"`).
    pub invariant: &'static str,
    /// Function the violation was found in. `None` for program-level
    /// violations (e.g. missing module entries).
    pub function: Option<FunId>,
    /// Human-readable detail. Format is invariant-specific; tests
    /// should not match on it.
    pub detail: String,
}

impl InvariantViolation {
    pub fn new(
        invariant: &'static str,
        function: Option<FunId>,
        detail: impl Into<String>,
    ) -> Self {
        Self {
            invariant,
            function,
            detail: detail.into(),
        }
    }
}

/// A named structural check over a `Program`.
///
/// Every invariant has:
///
/// - a globally-unique stable [`id`](Invariant::id), used for greppability
///   and selective enabling;
/// - a lifespan `[established_by..=held_through]` over pipeline stages
///   (see [`Stage`] / [`pipeline_order`]);
/// - a [`check`](Invariant::check) method that walks the program and
///   collects **every** violation found, or returns `Ok(())` if the
///   IR satisfies the invariant. (See `new-invariant-checks.md` Q1
///   for the collect-not-short-circuit rationale.)
///
/// Invariants are stateless: every method takes `&self` and `&Program`.
/// Side-channel data the check needs (prover function ids, world
/// struct id, etc.) is discovered at check time by scanning the
/// program structure -- see `stages.rs::discover_prover_ids` and
/// `stages.rs::find_world_struct_id` for the patterns.
pub trait Invariant: Send + Sync + 'static {
    /// Stable kebab-case id, e.g. `"no-write-ref-in-body"`.
    fn id(&self) -> &'static str;

    /// Stage that first establishes the invariant.
    fn established_by(&self) -> Stage;

    /// Highest stage at which the invariant must still hold (inclusive).
    fn held_through(&self) -> Stage;

    /// Run the check. Reports **all** violations found, or `Ok(())`.
    ///
    /// Per `new-invariant-checks.md` open question #1, invariants
    /// collect every violation in a single pass rather than
    /// short-circuiting on the first one -- much better triage in
    /// debug builds, only marginally more code.
    fn check(&self, program: &Program) -> Result<(), Vec<InvariantViolation>>;
}

/// `self.established_by() <= stage <= self.held_through()` in pipeline order.
pub(crate) fn applies_at(inv: &dyn Invariant, stage: Stage) -> bool {
    inv.established_by().at_or_before(stage) && inv.held_through().at_or_after(stage)
}

/// `self.established_by() < stage <= self.held_through()` -- precondition
/// shape: every invariant established by an earlier stage that must still
/// hold at `stage`'s entry.
pub(crate) fn applies_as_precondition(inv: &dyn Invariant, stage: Stage) -> bool {
    inv.established_by().strictly_before(stage) && inv.held_through().at_or_after(stage)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn pipeline_order_matches_active_path() {
        // Active path: Baseline -> S02 -> S03MutToLet -> S04Effects -> S05Ssa
        // -> S10BoundedNat -> S07Dejumps -> S06LetInline -> S08Loops -> Render
        let order = [
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
        ];
        for w in order.windows(2) {
            assert!(
                w[0].strictly_before(w[1]),
                "expected {:?} < {:?} in pipeline order",
                w[0],
                w[1],
            );
        }
    }

    #[test]
    fn stage_10_runs_before_stage_7() {
        // The trap the plan warned about.
        assert!(Stage::S10BoundedNat.strictly_before(Stage::S07Dejumps));
    }

    #[test]
    fn stage_6_runs_after_stage_7() {
        // Same trap, other direction.
        assert!(Stage::S07Dejumps.strictly_before(Stage::S06LetInline));
    }

    #[test]
    fn baseline_is_earliest_render_is_latest() {
        for s in [
            Stage::S02IrCfg,
            Stage::S03MutToLet,
            Stage::S04Effects,
            Stage::S05Ssa,
            Stage::S10BoundedNat,
            Stage::S07Dejumps,
            Stage::S06LetInline,
            Stage::S08Loops,
        ] {
            assert!(Stage::Baseline.strictly_before(s));
            assert!(s.strictly_before(Stage::Render));
        }
    }

    #[test]
    fn applies_at_uses_pipeline_order_not_enum_order() {
        // S10 (numerically large) actually runs before S07.
        // An invariant established by S10 and held through S07 should
        // apply at S07.
        struct DummyInv;
        impl Invariant for DummyInv {
            fn id(&self) -> &'static str {
                "dummy"
            }
            fn established_by(&self) -> Stage {
                Stage::S10BoundedNat
            }
            fn held_through(&self) -> Stage {
                Stage::S07Dejumps
            }
            fn check(&self, _: &Program) -> Result<(), Vec<InvariantViolation>> {
                Ok(())
            }
        }
        let inv = DummyInv;
        assert!(applies_at(&inv, Stage::S10BoundedNat));
        assert!(applies_at(&inv, Stage::S07Dejumps));
        assert!(!applies_at(&inv, Stage::S05Ssa)); // before establishment
        assert!(!applies_at(&inv, Stage::S06LetInline)); // after held_through
    }
}
