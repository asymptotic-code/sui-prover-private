//! Stage 4 -- Erase residual `&mut` ops and types from post-stage-3 IR.
//!
//! Eliminates every residual `Type::MutableRef`, `Expr::BorrowLoc`,
//! `Expr::BorrowField`, and `Expr::ReadRef` from function bodies that
//! survive stage 3. Stage 3 removed every mutation operation
//! (`WriteRef` / `WriteBack`) and demoted signatures; this stage is
//! mechanical syntactic cleanup of the read-side mutref ops.
//!
//! See `plans/lean-pipeline/stage-04-erase-mut.md` for the algorithm
//! and `plans/lean-pipeline/stage-04-erase-mut-impl.md` for the phase
//! plan.
//!
//! This is the full last pre-deletion prototype, with its tests and known
//! deferred container-edge cases, retained with `stage_03_demut`. The active
//! pipeline uses the Mutation-prelude path; [`run`] is not wired into
//! `run_pipeline`.
//!
//! ## Pipeline order
//!
//! Per `stage-04-erase-mut-impl.md`:
//!
//! 1. **Rewrite 1** -- substitute every `Expr::ReadRef(Var(r))` with
//!    `path_to_expr(source, edges)` where `(source, edges)` is `r`'s
//!    borrow chain (recovered from `Stmt::Let { value: BorrowLoc | BorrowField }`
//!    bindings via stage 3's `BorrowState`).
//! 2. **Rewrite 2** -- drop dead `Stmt::Let { value: BorrowLoc | BorrowField }`
//!    bindings whose `VarId` no longer has any consumers.
//! 3. **Rewrite 3** -- strip residual `Type::MutableRef` from body
//!    locals and from non-pattern-4b signatures.
//!
//! Pattern 4b (sub-field-mutref-returning) functions survive
//! untouched: their tail-position `BorrowField` / `BorrowLoc` chain
//! is preserved, and `Type::MutableRef` remains in their return type.

mod drop_dead;
pub mod path_to_expr;
pub mod postcondition;
mod read_ref;
mod strip_types;

#[cfg(test)]
mod tests;

pub use drop_dead::drop_dead_borrows;
pub use path_to_expr::path_to_expr;
pub use read_ref::rewrite_read_refs;
pub use strip_types::strip_mutable_ref_types;

use crate::ir::Program;

/// Reserved error surface for the inactive prototype. The current
/// implementation does not return errors, but unsupported `VecIndex` and
/// `MapKey` read paths panic; [`run`] is not activation-ready until those
/// paths become explicit errors or are implemented.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Stage4Error {}

/// Run stage 4 over `program`.
///
/// Pipeline order (per `stage-04-erase-mut-impl.md`):
///
/// 1. `rewrite_read_refs` -- substitute `ReadRef(Var(r))` with
///    `path_to_expr(root, edges)`.
/// 2. `drop_dead_borrows` -- drop dead `BorrowLoc` / `BorrowField`
///    `Stmt::Let` bindings.
/// 3. `strip_mutable_ref_types` -- strip residual `Type::MutableRef`
///    from non-pattern-4b signatures and from `type_args` /
///    `binder_type` slots in expressions.
///
/// After the three rewrites, the stage-4 postcondition holds: zero
/// `Expr::ReadRef`, zero `Expr::BorrowLoc` / `Expr::BorrowField`
/// outside pattern-4b tails, and no `Type::MutableRef` outside
/// pattern-4b returns. Debug builds enforce this.
pub fn run(program: &mut Program) -> Result<(), Stage4Error> {
    rewrite_read_refs(program);
    drop_dead_borrows(program);
    strip_mutable_ref_types(program);

    #[cfg(debug_assertions)]
    {
        if let Err(_e) = postcondition::check(program) {
            // Same model as the inactive demut prototype: the reserved
            // error surface is empty, so postcondition failures assert.
            debug_assert!(false, "stage 4 postcondition check failed: {_e:?}");
        }
    }
    Ok(())
}
