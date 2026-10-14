//! Stage 5 -- SSA: full alpha-rename, explicit phi via Tuple-Let,
//! explicit loop-carried state via the `loop_state` tuple.
//!
//! See `plans/lean-pipeline/stage-05-ssa.md` for the design and
//! `plans/lean-pipeline/stage-05-ssa-impl.md` for the phased plan.
//!
//! Inputs:
//! - Post-stage-3 (mut-to-let) `Program`. `Type::MutableRef`,
//!   `Expr::BorrowLoc`, `BorrowField`, `ReadRef`, `WriteRef` (in
//!   value position), `WriteBack` (in value position) all survive
//!   and are opaque to stage 5.
//! - Bodies may contain shadowing `Stmt::Let` rebinds (the let-rebind
//!   form stage 3 emits for `WriteRef` / `WriteBack`). Stage 5
//!   alpha-renames the shadows into fresh names (`r_0`, `r_1`, ...).
//! - Augmented `Stmt::Let` destructures from stage 3 (call-site
//!   augmentation) and augmented `BlockTail::Return` / `Value`
//!   tuples flow through unchanged -- they are ordinary
//!   pattern/tuple shapes for stage 5.
//!
//! Outputs:
//! - No shadowing anywhere in any `Function::body`.
//! - Every `Expr::If` / `Match` whose continuation references vars
//!   defined in any arm is wrapped in a `Stmt::Let { pattern:
//!   [phi_vars], value: If/Match { ... } }`. Value arms emit
//!   `Tuple([phi_vars])`; terminator-tailed arms keep their tails.
//! - Every `Expr::While` carries `iter_locals: Vec<(VarId, Expr)>`
//!   -- one `(binder, init)` pair per loop-carried-state slot.
//!   Each `init` is evaluated in the OUTER scope at loop entry;
//!   each `binder` is in scope for `header`, `cond`, and `body`.
//! - `BlockTail::Break / Continue { level: k, value }` carries the
//!   target loop's `loop_state` shape (resolved via the
//!   `level`-th enclosing `While`'s `iter_locals`).
//! - The body's outermost tail is normalized: a former
//!   `BlockTail::Continue { level: 0, value: V }` becomes
//!   `BlockTail::Value(V)` (implicit-continue convention). Inner
//!   `Continue { level: 0 }` inside If / Match arms stays explicit.

mod ctx;
pub mod postcondition;
mod var_types;
mod walk;

#[cfg(test)]
mod tests;

pub use ctx::{Ctx, LoopFrame};

use crate::ir::{Program, VarId};

/// Errors produced by stage 5 (SSA).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Stage5Error {
    /// A `Var(v)` was referenced but no enclosing binder defines it.
    /// Either a pre-existing IR bug or a stage-3 boundary glitch.
    UnboundReference {
        function: crate::ir::FunId,
        var: VarId,
    },

    /// A `loop_state` var (a body-bound var referenced in
    /// header / cond / post-loop continuation) is not in outer
    /// scope. Stage 5 can't construct a valid `init` expression
    /// for the matching iter_local in that case. Defensive --
    /// well-formed pre-stage-5 IR shouldn't produce it.
    UninitFromZeroIterLoop {
        function: crate::ir::FunId,
        vars: Vec<VarId>,
    },

    /// An `Expr::While` was found in a value (sub-expression)
    /// position rather than at statement level. Stage 2 lifts every
    /// loop to a `Stmt::Eval(While)` / `Stmt::Let { value: While }`,
    /// which `rewrite_block` intercepts for `loop_state` synthesis; a
    /// `While` reaching the expression renamer therefore means
    /// unexpected IR. Surfaced (per-function isolation skips it)
    /// rather than handled, since `loop_state` can't be synthesized
    /// without the post-loop continuation.
    WhileInValuePosition { function: crate::ir::FunId },
}

/// Run stage 5 over `program`.
///
/// Walks every non-native function body: alpha-renames every
/// binding, introduces explicit phi via Tuple-Let at `If`/`Match`
/// merges, threads `loop_state` tuples through every `While`.
pub fn run(program: &mut Program) -> Result<(), Stage5Error> {
    walk::rewrite_program(program)?;
    #[cfg(debug_assertions)]
    {
        if let Err(_e) = postcondition::check(program) {
            debug_assert!(false, "stage 5 (SSA) postcondition failed: {_e:?}");
        }
        // Separate from `check` so the render-held stage-5 umbrella
        // invariant doesn't re-run it on transformed IR (false-positive
        // trap). Reaches here only on a zero-skip rewrite (the `?`
        // above returns early otherwise), so every function checked was
        // SSA-processed.
        if let Err(_e) = postcondition::check_readref_inner_is_reference(program) {
            debug_assert!(false, "stage 5 (SSA) ReadRef postcondition failed: {_e:?}");
        }
    }
    Ok(())
}
