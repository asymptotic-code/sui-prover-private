//! Stage-4 fixtures, grouped by what they exercise.
//!
//! Phase 1 ships:
//! - `path_to_expr` -- pure helper unit tests.
//! - `read_ref` -- Rewrite 1 fixtures (ReadRef substitution).
//!
//! Phases 2-3 add `drop_dead_mutborrow`, `strip_types`, `pattern_4b`,
//! `postcondition`, `regressions`, `run_invariants`, and
//! `stage_05_input` (cross-stage handoff).

#![cfg(test)]

mod drop_dead;
mod fixtures;
mod path_to_expr;
mod pattern_4b;
mod postcondition;
mod read_ref;
mod run_invariants;
mod strip_types;
