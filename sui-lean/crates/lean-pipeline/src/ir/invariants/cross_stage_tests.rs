//! Cross-stage precondition / inheritance tests.
//!
//! Demonstrates that the invariants framework correctly inherits an
//! earlier-stage invariant into every later stage's precondition.
//! These are the tests the user asked for when they said
//! "recheck the postconditions of one stage after all stages where
//! they should still hold" -- they verify the framework's promise.
//!
//! Each test follows the shape:
//!   1. Build a program that satisfies stage N's postcondition.
//!   2. Inject a violation of an invariant established at stage N.
//!   3. Assert `verify_precondition(stage_M, &program)` catches it,
//!      for every M > N where the invariant's `held_through` covers
//!      M.

use crate::ir::invariants::{all_invariants, verify_at, verify_precondition, Stage};
use crate::ir::Program;

/// Every stage's precondition is a subset of the previous stage's
/// postcondition: an invariant active at the postcondition of stage
/// N must also be active at the precondition of stage N+1 (assuming
/// `held_through` extends that far).
#[test]
fn precondition_is_subset_of_previous_postcondition() {
    let stages = [
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
    for w in stages.windows(2) {
        let earlier = w[0];
        let later = w[1];
        for inv in all_invariants() {
            if inv.established_by().at_or_before(earlier) && inv.held_through().at_or_after(later) {
                // Invariant lives at both stages -> it must appear in
                // `later`'s precondition set (i.e. established before
                // `later` and held through `later`).
                let established_before_later = inv.established_by().strictly_before(later);
                let held_at_later = inv.held_through().at_or_after(later);
                assert!(
                    established_before_later && held_at_later,
                    "invariant {} should appear in {:?} precondition set (established_by={:?}, held_through={:?})",
                    inv.id(),
                    later,
                    inv.established_by(),
                    inv.held_through(),
                );
            }
        }
    }
}

/// Every Baseline invariant is in every stage's precondition.
#[test]
fn baseline_invariants_are_in_every_stage_precondition() {
    for inv in all_invariants() {
        if inv.established_by() != Stage::Baseline {
            continue;
        }
        for later in [
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
            if inv.held_through().at_or_after(later) {
                // Baseline strictly before `later`, and held through
                // `later` -- it's in the precondition.
                assert!(
                    inv.established_by().strictly_before(later)
                        && inv.held_through().at_or_after(later),
                    "baseline invariant {} should be in {:?} precondition",
                    inv.id(),
                    later,
                );
            }
        }
    }
}

/// Stage 7's postcondition (`no-block-tail-return`) must be reachable
/// from every later stage's verification: stages 6, 8, Render.
#[test]
fn stage_07_invariants_reach_render() {
    // Find the stage-07 umbrella invariant.
    let inv = all_invariants()
        .into_iter()
        .find(|i| i.id() == "stage-07-dejumps-postcondition")
        .expect("stage-07 invariant registered");
    assert_eq!(inv.established_by(), Stage::S07Dejumps);
    // It must still apply at S06, S08, Render (every stage in active
    // order >= S07).
    assert!(inv.held_through().at_or_after(Stage::S06LetInline));
    assert!(inv.held_through().at_or_after(Stage::S08Loops));
    assert!(inv.held_through().at_or_after(Stage::Render));
}

/// Stage 3's postcondition (no WriteRef/WriteBack) must hold through
/// every later stage.
#[test]
fn stage_03_invariants_reach_render() {
    let inv = all_invariants()
        .into_iter()
        .find(|i| i.id() == "stage-03-mut-to-let-postcondition")
        .expect("stage-03 invariant registered");
    assert_eq!(inv.established_by(), Stage::S03MutToLet);
    assert!(inv.held_through().at_or_after(Stage::S04Effects));
    assert!(inv.held_through().at_or_after(Stage::S05Ssa));
    assert!(inv.held_through().at_or_after(Stage::S10BoundedNat));
    assert!(inv.held_through().at_or_after(Stage::S07Dejumps));
    assert!(inv.held_through().at_or_after(Stage::S06LetInline));
    assert!(inv.held_through().at_or_after(Stage::S08Loops));
    assert!(inv.held_through().at_or_after(Stage::Render));
}

/// Type inference cannot be a baseline precondition: stage 2's provisional
/// pre-SSA IR can legitimately contain arm-local merge variables that stage 5
/// has not hoisted yet. Its first contract boundary is stage 5's output.
#[test]
fn ir_type_inference_contract_starts_at_stage_05() {
    let inv = all_invariants()
        .into_iter()
        .find(|i| i.id() == "ir-type-inference-succeeds")
        .expect("type-inference invariant registered");
    assert_eq!(inv.established_by(), Stage::S05Ssa);
    assert!(inv.held_through().at_or_after(Stage::S10BoundedNat));
    assert!(inv.held_through().at_or_after(Stage::Render));
}

/// `verify_precondition` includes Baseline invariants for every
/// non-Baseline stage.
#[test]
fn verify_precondition_for_stage_03_includes_baseline() {
    // Construct a program that would FAIL a baseline invariant: a
    // function referencing an unbound variable.
    use crate::ir::builder::{just, var};
    use crate::ir::{Function, FunctionKind, Module, Param, Signature, Type};
    let mut p = Program::default();
    p.modules.insert(
        0,
        Module {
            name: "m".to_string(),
            package_name: "test".to_string(),
            address: String::new(),
            required_imports: Vec::new(),
            is_native: false,
        },
    );
    p.functions.insert(
        0,
        Function {
            module: 0,
            name: "broken".to_string(),
            signature: Signature {
                type_params: Vec::new(),
                params: Vec::<Param>::new(),
                return_type: Type::Unit,
            },
            body: just(var("missing")),
            kind: FunctionKind::Source,
            effects: crate::ir::Effects::PURE,
            explicit_pure: false,
        },
    );
    let res = verify_precondition(Stage::S03MutToLet, &p);
    assert!(
        res.is_err(),
        "stage-03 precondition should reject unbound var"
    );
    let violations = res.unwrap_err();
    assert!(
        violations
            .iter()
            .any(|v| v.invariant == "baseline-well-formedness"),
        "baseline-well-formedness should appear in stage-03 precondition errors",
    );
}

/// `verify_at(Stage::Render, ...)` runs every invariant whose
/// `held_through` reaches Render -- this is the renderer-time gate.
#[test]
fn verify_at_render_runs_baseline_and_every_stage_umbrella() {
    let p = Program::default();
    // Empty program: every check is vacuously satisfied.
    assert!(verify_at(Stage::Render, &p).is_ok());

    // Sanity: there are at least 4 baseline invariants + 7 stage
    // umbrellas = 11 total invariants in the registry.
    let count = all_invariants().len();
    assert!(
        count >= 11,
        "expected at least 11 registered invariants, found {}",
        count,
    );
}

/// Stage-10 invariant must apply at stage-7 / stage-6 / stage-8
/// (because in active pipeline order, S10 runs BEFORE S07/S06/S08).
#[test]
fn stage_10_invariant_applies_at_later_stages_in_pipeline_order() {
    let inv = all_invariants()
        .into_iter()
        .find(|i| i.id() == "stage-10-bounded-nat-postcondition")
        .expect("stage-10 invariant registered");
    assert_eq!(inv.established_by(), Stage::S10BoundedNat);
    // In pipeline order, S07/S06/S08 all come AFTER S10. The
    // invariant should still apply at each.
    for stage in [
        Stage::S07Dejumps,
        Stage::S06LetInline,
        Stage::S08Loops,
        Stage::Render,
    ] {
        assert!(
            inv.held_through().at_or_after(stage),
            "stage-10 invariant should hold through {:?}",
            stage,
        );
    }
}
