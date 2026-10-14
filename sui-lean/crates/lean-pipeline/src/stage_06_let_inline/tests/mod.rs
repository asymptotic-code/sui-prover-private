//! Stage-6 tests, grouped by what they exercise.
//!
//! Phase 1 ships:
//! - `use_count` -- per-function walker.
//! - `effects_predicate` -- structural is_pure_total dispatch.
//!
//! Phases 2-5 add `copy_inline`, `single_use`, `tuple_split`,
//! `tuple_simplify`, `eval_dce`, `hygiene`, `effects_calls`,
//! `postcondition`, `run_invariants`, and `stage_07_input`.

#![cfg(test)]

mod borrow_use;
mod copy_inline;
mod effects_calls;
mod effects_predicate;
mod eval_dce;
mod fixtures;
mod hygiene;
mod is_eval_dce_droppable;
mod postcondition;
mod run_invariants;
mod single_use;
mod stage_07_input;
mod thin_coverage;
mod tuple_simplify;
mod tuple_split;
mod use_count;
