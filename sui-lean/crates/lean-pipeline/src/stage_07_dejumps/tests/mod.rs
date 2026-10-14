//! Stage 7 (rewrite) test fixtures.
//!
//! Exercises the variant-pair design -- value function plus its
//! `.aborts` companion.

mod aborts_live_loop;
mod aborts_live_loop_passthrough;
mod aborts_loop_propagate;
mod aborts_variant;
mod end_to_end;
mod labeled_block_extract;
mod postcondition;
mod return_lift_deref_skew;
