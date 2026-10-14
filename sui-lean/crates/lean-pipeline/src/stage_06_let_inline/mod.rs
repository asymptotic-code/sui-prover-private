//! Stage 6 -- `let` inlining + DCE over post-stage-5 (SSA) IR.
//!
//! Drops redundant bindings and inlines single-use pure-and-total
//! expressions. After stage 6, function bodies are free of trivial
//! copy chains and free of `Stmt::Eval(<pure-and-total>)`. Calls
//! whose callee carries `Effects::PURE` (per stage 2's
//! `classify_effects` pre-pass) are inlined when single-use;
//! partial / mutating callees keep their evaluation order.
//!
//! See:
//! - `plans/lean-pipeline/stage-06-let-inline.md` -- algorithm + decision log.
//! - `plans/lean-pipeline/stage-06-let-inline-impl.md` -- phase plan.
//!
//! ## Pipeline order
//!
//! Per the impl plan:
//!
//! 1. **Pre-pass:** `tuple_split` -- split `let (a,b) = (e0,e1)` into
//!    per-position lets so sub-passes 2a/2b can pick up each `e_i`
//!    uniformly. Runs ONCE before the fixpoint.
//! 2. **Fixpoint** (bounded by `FIXPOINT_LIMIT`) over per-function
//!    bodies. Each iteration runs the four sub-passes interleaved:
//!    - `copy_inline` (2a) -- `let v = Var(y) | Const(c)` -> substitute.
//!    - `single_use_inline` (2b) -- `let v = e` where `is_pure_total(e)`
//!      AND `use_count(v) == 1` -> substitute the unique use site.
//!    - `tuple_simplify` (2c) -- unused tuple positions -> `None` wildcard;
//!      all-wildcard `Stmt::Let` -> drop (if pure) or `Stmt::Eval`.
//!    - `eval_dce` (2d) -- drop `Stmt::Eval(<pure-total>)`.
//! 3. **Postcondition** in `cfg(debug_assertions)`.

const FIXPOINT_LIMIT: usize = 100;

pub mod copy_inline;
pub mod effects_predicate;
pub mod eval_dce;
pub mod postcondition;
pub mod single_use;
pub mod substitute;
pub mod tuple_simplify;
pub mod tuple_split;
pub mod use_count;

#[cfg(test)]
mod tests;

use crate::ir::Program;

/// Errors produced by stage 6.
///
/// `run()` itself only fails with `FixpointDidNotConverge`, a
/// defensive pressure-release valve: each sub-pass strictly reduces
/// stmt count or use count, so the fixpoint provably converges on
/// well-formed input. The variant exists so a future bug can't
/// loop forever.
///
/// Shape-level invariants (no surviving identity Let, no
/// all-wildcard `Stmt::Let`, etc.) are output guarantees -- they
/// live on [`postcondition::PostconditionError`] and are checked
/// after `run()` completes (debug-asserted on every invocation).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Stage6Error {
    /// Fixpoint iteration did not converge within `FIXPOINT_LIMIT`
    /// iterations. Provably unreachable on well-formed input by the
    /// convergence proof in the impl plan; this guards against a
    /// future bug regressing the proof.
    FixpointDidNotConverge,
}

/// RAII guard that restores a swapped-out `Function::body` back into
/// `program.functions` on drop (normal exit or panic).
///
/// `run()` swaps a function's body out so sub-passes can borrow
/// `&Program` while mutating `&mut Block`. Without a guard, a panic
/// inside a sub-pass would leave the function with a placeholder
/// `Unit` body. The `Drop` impl puts the saved body back, restoring
/// the program to a consistent shape on the unwind path.
struct BodyGuard<'a> {
    program: &'a mut Program,
    fid: crate::ir::FunId,
    body: Option<crate::ir::Block>,
}

impl Drop for BodyGuard<'_> {
    fn drop(&mut self) {
        if let Some(body) = self.body.take() {
            if let Some(f) = self.program.functions.get_mut(&self.fid) {
                f.body = body;
            }
        }
    }
}

/// Run stage 6 over `program`.
///
/// For every non-native function:
///
/// 1. Pre-pass: `tuple_split::split_tuple_literals` once.
/// 2. Fixpoint loop (bounded by `FIXPOINT_LIMIT`):
///    - `copy_inline_once` (sub-pass 2a)
///    - `single_use_inline_once` (sub-pass 2b)
///    - `tuple_simplify_once` (sub-pass 2c)
///    - `eval_dce_once` (sub-pass 2d)
///
///    Break when no sub-pass reports a change.
///
/// ## Sub-pass order
///
/// The four sub-passes are interleaved per fixpoint iteration in the
/// order above. Each pass exposes work for the others: 2a substituting
/// a copy may drop a use count from 2 to 1 (enabling 2b on the next
/// iter); 2b inlining a pure-total Let may turn a binding\'s use count
/// to 0 (enabling 2c); 2c collapsing a let to `Stmt::Eval(pure)` exposes
/// a 2d candidate. The reverse direction holds less interestingly: 2d
/// dropping an Eval doesn\'t expose work for 2a-2c.
///
/// Reordering would change convergence speed but not the final
/// fixed point, since each pass strictly reduces stmt count or
/// substitutable-use count.
///
/// Native functions are skipped entirely (their hand-written
/// signatures and bodies are not under stage 6\'s purview).
///
/// ## Panic safety
///
/// The per-function body is swapped out of `program.functions` (so
/// sub-passes can hold a shared `&Program` while mutating
/// `&mut Block`) and restored via a [`BodyGuard`] -- on a sub-pass
/// panic the guard\'s `Drop` impl puts the swapped-out body back,
/// leaving the program in a consistent state.
pub fn run(program: &mut Program) -> Result<(), Stage6Error> {
    let fids: Vec<crate::ir::FunId> = program.functions.keys().copied().collect();
    for fid in fids {
        // Swap the body out so sub-passes can hold a shared
        // `&Program` while mutating `&mut Block`. The `BodyGuard`
        // restores it on Drop -- normal exit or panic.
        let placeholder = crate::ir::Block {
            stmts: Vec::new(),
            tail: crate::ir::BlockTail::Value(crate::ir::Expr::Unit),
        };
        let saved = std::mem::replace(
            &mut program.functions.get_mut(&fid).unwrap().body,
            placeholder,
        );
        let mut guard = BodyGuard {
            program,
            fid,
            body: Some(saved),
        };
        let body = guard.body.as_mut().expect("body present");

        // Pre-pass: literal-tuple split (once).
        tuple_split::split_tuple_literals(body, guard.program);

        // Fixpoint.
        let mut iter = 0;
        loop {
            if iter >= FIXPOINT_LIMIT {
                // Drop the guard to restore the body before
                // returning -- the caller sees the partial-progress
                // shape.
                drop(guard);
                return Err(Stage6Error::FixpointDidNotConverge);
            }
            let mut changed = false;
            changed |= copy_inline::copy_inline_once(body);
            changed |= single_use::single_use_inline_once(body, guard.program);
            changed |= tuple_simplify::tuple_simplify_once(body, guard.program);
            changed |= eval_dce::eval_dce_once(body, guard.program);
            if !changed {
                break;
            }
            iter += 1;
        }

        // Drop the guard explicitly to restore the body before the
        // postcondition check (which needs a consistent program).
        drop(guard);
    }

    #[cfg(debug_assertions)]
    {
        if let Err(_e) = postcondition::check(program) {
            // Same model as stage 4: stage 6's algorithm doesn't
            // fail (Stage6Error's `Fixpoint`/wildcard variants are
            // for defensive shape rejects); a postcondition failure
            // is a programmer-visible bug. Assert rather than return.
            debug_assert!(false, "stage 6 postcondition check failed: {_e:?}");
        }
    }
    Ok(())
}
