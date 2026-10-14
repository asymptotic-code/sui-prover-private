//! Stage 4 -- Effects: thread a `World` value through the executable
//! world-needing call-graph closure so observable side effects (events,
//! transfers, deletes, receives) become explicit in the IR.
//!
//! Five transformations in pipeline order (see
//! `plans/lean-pipeline/stage-04-effects.md` for the design):
//!
//! 1. **Transform A** (`world::ensure_world_struct` + effects re-run)
//!    -- register the `World` struct and re-classify effects now
//!    that stage 3's WriteRef/WriteBack ops are gone.
//! 2. **Transform B** (`signatures::augment_signatures`) -- add
//!    `world: World` and augment the return type for every translated
//!    function and native declaration in the world-threading closure.
//! 3. **Transforms C + D** (`call_augment::augment_call_sites`) --
//!    thread `Var(world)` into Call args and extend destructure
//!    patterns. Idempotent.
//! 4. **Transform E** (`body_tail::augment_body_tails`) -- wrap
//!    every reachable `BlockTail::Return` and the body's top-level
//!    fall-off `BlockTail::Value` with `Tuple([..orig, Var(world)])`.
//!    Idempotent.
//!
//! Function names and FunIds are unchanged. Native IR declarations and
//! their hand-written `Prover.World.*` Lean definitions share the same
//! augmented signature.

pub mod body_tail;
pub mod call_augment;
pub mod common;
pub mod postcondition;
pub mod signatures;
pub mod world;
mod world_flow;

#[cfg(test)]
mod tests;

pub use body_tail::augment_body_tails;
pub use call_augment::augment_call_sites;
pub use signatures::augment_signatures;
pub use world::{ensure_world_struct, world_type, WORLD_QUALIFIED_NAME};

use crate::ir::{FunId, Program};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Stage4Error {
    /// A `Call` to a World-needing callee appeared in a compound
    /// expression position (e.g., inside a `Tuple` / `Pack` / `BinOp`)
    /// rather than as the value of a `Stmt::Eval` or `Stmt::Let`.
    /// Stage 4 cannot attach a destructure pattern in those positions;
    /// stage 2's bytecode lift normally hoists such calls into named
    /// temps.
    CallInExpressionPosition { function: FunId },
}

/// Run stage 4 over `program`.
pub fn run(program: &mut Program) -> Result<(), Stage4Error> {
    let trace = |name: &str| {
        if std::env::var_os("FOXY_DEBUG_PIPELINE_TRACE").is_some() {
            eprintln!("[stage-04-effects] entering {name}");
        }
    };
    // Transform A: register World struct.
    trace("ensure_world_struct");
    let world_id = ensure_world_struct(program);

    // Re-classify effects now that stage 3 has erased WriteRef /
    // WriteBack ops. Functions that had `GlobalMut` purely because of
    // mutref machinery are now `NoMut` and don't need world
    // threading. `compute_needs_world` below gates on
    // `effects.mutation == GlobalMut`, so this pass must run on the
    // post-stage-3 program shape. One fixpoint pass.
    trace("classify_effects");
    crate::stage_02_ir_cfg::classify_effects(program);

    // Compute the transitive closure of functions that need a
    // `world: World` parameter threaded through them. This subsumes
    // the previous `is_impure_user` predicate -- a `#[ext(pure)]`
    // user helper whose `Function::effects` is locked at
    // `Effects::PURE` but which calls a globally-mutating framework
    // native (e.g. `math_specs::math_div` -> `Integer::mul`) is
    // included in the closure even though it's not itself
    // classified GlobalMut. The strict alternative leaves such a
    // helper un-augmented at the signature level while
    // `augment_call_sites` would still try to thread world through
    // its body's Calls --
    // producing a body with `Var(world)` references that have no
    // matching `world` parameter to bind them.
    trace("compute_needs_world");
    let needs_world = self::common::compute_needs_world(program);

    // Transform B: signature augmentation.
    trace("augment_signatures");
    augment_signatures(program, world_id, &needs_world)?;

    // Transforms C + D: call-site threading + destructure extension.
    // Must run BEFORE body-tail augmentation so a direct tail
    // `Value(Call(impure, ..))` is rejected here with
    // `CallInExpressionPosition` rather than getting hidden inside
    // body_tail's wrapping Tuple.
    trace("augment_call_sites");
    augment_call_sites(program, &needs_world)?;

    // Transform E: body-tail augmentation.
    trace("augment_body_tails");
    augment_body_tails(program, world_id, &needs_world)?;

    #[cfg(debug_assertions)]
    {
        trace("postcondition");
        if let Err(_e) = postcondition::check(program, world_id) {
            debug_assert!(false, "stage 4 (effects) postcondition failed: {_e:?}");
        }
    }

    // Ghost threading + op lowering is a SEPARATE stage
    // (`crate::stage_04_ghost`), wired in `run_pipeline` right after this
    // one -- it is spec-only and independent of world/effects. It must run
    // after this stage (its slots append after the `world` slot) and
    // before SSA.
    Ok(())
}
