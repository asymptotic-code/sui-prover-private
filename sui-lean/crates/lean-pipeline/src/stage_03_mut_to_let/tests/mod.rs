//! Stage-3 (mut-to-let) test fixtures.
//!
//! Each module exercises one transform or invariant.

#![cfg(test)]

mod body_tail;
mod call_augment;
mod end_to_end;
mod fixtures;
mod global_lifecycle;
mod nested;
mod postcondition;
mod run_invariants;
mod signatures;
mod write_back;
mod write_ref;
