//! Stage 8 -- final loop-helper effect propagation.
//!
//! Stage 7 extracts loops and continuations after the ordinary stage-4 effect
//! fixpoint has run. This stage recomputes the conservative World-write
//! closure over that final recursive call graph so the renderer can distinguish
//! read-only World fixpoints from writers.
//!
//! Loop termination uses the renderer's `partial_fixpoint`; this stage does
//! not inject fuel or synthesize numeric operations.

pub mod world_writes_postcondition;

use crate::ir::Program;

/// Recompute the final conservative World-write closure. Idempotent.
pub fn run(program: &mut Program) {
    crate::stage_04_effects::common::propagate_world_writes(program);
}
