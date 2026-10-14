//! Stage 3 -- Demut: thread `&mut` parameters as values.
//!
//! Eliminates every mutation operation through `&mut` references by
//! demoting `&mut`-taking signatures (param types stripped, return
//! types augmented) and rewriting `WriteRef` / `WriteBack` ops as
//! value-form `path_to_update` rebinds.
//!
//! See `plans/lean-pipeline/stage-03-demut.md` for the full algorithm
//! and `plans/lean-pipeline/stage-03-demut-impl.md` for the phase plan.
//!
//! This is the full last pre-deletion prototype, with its tests and known
//! deferred container-edge cases, retained for a possible future migration to
//! value-style mutable references. The active pipeline uses
//! `stage_03_mut_to_let`; [`run`] is not wired into `run_pipeline`.

mod borrow_state;
mod calls;
mod demotion_set;
pub mod postcondition;
mod signatures;
pub mod writebacks;

#[cfg(test)]
mod tests;

pub use borrow_state::{build as build_borrow_state, BorrowChain, BorrowState};
pub use calls::rewrite_calls;
pub use demotion_set::{compute as compute_demotion_map, DemotionMap, FunDemotion};
pub use signatures::{
    augment_return, classify, demote_signature, rewrite_body_tails, DemotionPattern,
};
pub use writebacks::{path_to_update, rewrite_writebacks};

use crate::ir::Program;

/// Reserved error surface for the inactive prototype. The current
/// implementation does not return errors, but unsupported `VecIndex` and
/// `MapKey` writeback paths panic; [`run`] is not activation-ready until
/// those paths become explicit errors or are implemented.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Stage3Error {}

/// Run stage 3 over `program`.
///
/// Pipeline order (Phases 2-4 of `stage-03-demut-impl.md`):
/// 1. Compute the demotion map from the un-demoted program.
/// 2. Rewrite call sites to standard-demoted callees (destructure
///    augmented returns, rebind `&mut`-arg caller temps).
/// 3. Rewrite `WriteRef` / `WriteBack` ops in every body to value-form
///    `path_to_update` rebinds (consumes a per-function borrow-state
///    map built from `BorrowLoc` / `BorrowField` chains).
/// 4. Mutate every demoted function's signature in place (strip
///    `Type::MutableRef` from params; augment / replace return).
/// 5. Rewrite body tails of Standard-demoted functions to emit the
///    augmented-return tuple.
///
/// Pattern 4a / 4b call sites are structurally untouched: their demoted
/// returns match the consumer's expectations once stage 4 lowers the
/// surviving `MutBorrow` / `ReadRef` ops.
pub fn run(program: &mut Program) -> Result<(), Stage3Error> {
    let demotion_map = compute_demotion_map(program);
    rewrite_calls(program, &demotion_map);
    rewrite_writebacks(program);
    for fid in demotion_map.demoted() {
        if let Some(func) = program.functions.get_mut(&fid) {
            demote_signature(func);
        }
    }
    rewrite_body_tails(program, &demotion_map);

    // Stage-3 postcondition: gated on debug assertions to keep
    // production builds fast. Tests call `postcondition::check`
    // directly when they want explicit validation.
    #[cfg(debug_assertions)]
    {
        if let Err(_e) = postcondition::check(program) {
            // Postcondition failures are programmer-visible prototype bugs;
            // the reserved error surface is still empty.
            debug_assert!(false, "stage 3 postcondition check failed: {_e:?}");
        }
    }
    Ok(())
}
