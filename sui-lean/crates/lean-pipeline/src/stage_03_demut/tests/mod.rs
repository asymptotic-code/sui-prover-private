//! Stage-3 fixtures, grouped by what they exercise.
//!
//! Phase 1 ships pure-helper tests only: `path_to_update` and
//! `augment_return`. Phases 2-5 add fixtures for demotion-set,
//! signature rewriter, call-site rewriter, WriteRef / WriteBack
//! rebinders, body-tail rewriter, pattern 4b, nested tails, and the
//! postcondition validator.

#![cfg(test)]

mod augmented_return;
mod body_tail;
mod borrow_state;
mod calls;
mod demotion_set;
mod end_to_end;
mod fixtures;
mod path_to_update;
mod postcondition;
mod run_invariants;
mod signatures;
mod writebacks;
