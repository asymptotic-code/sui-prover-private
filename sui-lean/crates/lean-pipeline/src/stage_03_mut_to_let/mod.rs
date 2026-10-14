//! Stage 3 -- mut-to-let: lower in-body mutations to value-form
//! let-rebinds, and explicitly thread the post-call state of every
//! `&mut` argument through call sites, function tails, and signature
//! return types.
//!
//! Six transformations in pipeline order (see
//! `plans/lean-pipeline/stage-03-mut-to-let.md` for the design and
//! `plans/lean-pipeline/stage-03-mut-to-let-impl.md` for the phased
//! plan):
//!
//! 1. **WriteRef position-shift** (`write_ref::rewrite_write_refs`).
//! 2. **WriteBack position-shift** (`write_back::rewrite_write_backs`).
//! 3. **Signature return-type augmentation** (`signatures::augment_signatures`).
//! 4. **Call-site augmentation** (`call_augment::augment_call_sites`).
//! 5. **Body-tail augmentation** (`body_tail::augment_body_tails`).
//!
//! (Numbering follows the design doc -- WriteRef + WriteBack are
//! Transforms 1+2; signatures/body-tail/call-augment are 4-6. The
//! gap exists because the original plan numbered position-shift's two
//! WriteBack flavours separately.)
//!
//! Parameter types stay `Type::MutableRef` (= Lean `Mutation T` at
//! render time). Only the return type is augmented at the signature
//! level. See `plans/lean-pipeline/mutable-references.md` for the
//! Boogie-style passthrough strategy.

mod body_tail;
mod call_augment;
mod common;
pub mod postcondition;
mod signatures;
mod write_back;
mod write_ref;

#[cfg(test)]
mod tests;

pub use body_tail::augment_body_tails;
pub use call_augment::augment_call_sites;
pub use signatures::augment_signatures;
pub use write_back::rewrite_write_backs;
pub use write_ref::rewrite_write_refs;

use crate::ir::Program;

/// Errors produced by stage 3 (mut-to-let). Most paths are infallible
/// over well-formed input; the variants below catch upstream invariant
/// violations during dev.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Stage3Error {
    /// First-class frontend global nodes must be lowered to hidden parameters
    /// before stage 3. Keeping them here would bypass mutation-return
    /// threading or silently drop a global-root writeback.
    ResidualGlobal {
        function: crate::ir::FunId,
        global: crate::ir::GlobalId,
    },
    /// A `Stmt::Eval(Expr::WriteRef { reference, .. })` had a non-`Var`
    /// reference. Stage 2 should emit `Var($t_n)` here.
    WriteRefNonVar { function: crate::ir::FunId },
    /// A call site to a function with `&mut` params had a non-`Var`
    /// expression at a `&mut` argument position. Stage 2 should hoist
    /// any complex expression into a named temp before the call.
    CallMutArgNonVar { function: crate::ir::FunId },
    /// A call site's argument list was shorter than the callee's
    /// `&mut`-param index list. Indicates a stage-2 / signature
    /// mismatch.
    CallMutArgOutOfRange { function: crate::ir::FunId },
    /// A `Call` to a mut-taking function appeared in a compound
    /// expression position (e.g. as a sub-expression of another op),
    /// not as `Stmt::Eval(Call ..)` or `Stmt::Let { value: Call .. }`.
    /// Stage 2 typically hoists these into named temps; if one slips
    /// through, the call-site augmentation can't attach a destructure
    /// pattern.
    CallInExpressionPosition { function: crate::ir::FunId },
}

/// Run stage 3 over `program`.
pub fn run(program: &mut Program) -> Result<(), Stage3Error> {
    if let Some((function, global)) = crate::global_threading::first_residual_global(program) {
        return Err(Stage3Error::ResidualGlobal { function, global });
    }
    // Validate the complete mutating-call placement contract before any
    // write/signature rewrite. Tail or nested calls are rejected atomically in
    // v1 because they have nowhere to bind the callee's returned mutations.
    call_augment::validate_mutating_call_shapes(program)?;

    // 1-2: WriteRef + WriteBack position-shifts.
    rewrite_write_refs(program)?;
    rewrite_write_backs(program)?;

    // 3: signature return-type augmentation. Must run BEFORE
    // body-tail augmentation so the postcondition can validate the
    // tail shape against the new signature.
    augment_signatures(program)?;

    // 4: call-site augmentation. Walks each non-native function body,
    // wrapping calls to &mut-taking functions in Stmt::Let
    // destructures. Must run BEFORE body-tail augmentation so a
    // direct tail `Value(Call(mut-taking, ..))` cannot get silently
    // hidden inside body_tail's wrapping Tuple. The stage-entry
    // precheck rejects it atomically; call_augment retains the same
    // defense for callers that invoke this transform directly.
    augment_call_sites(program)?;

    // 5: body-tail augmentation. Walks each &mut-taking function's
    // body, augmenting Return tails (anywhere) and the body's
    // top-level fall-off Value tail. By the time this runs, the
    // body's tail is either Var/Tuple/non-Call (safe to wrap) or
    // has already been rejected by call_augment.
    augment_body_tails(program)?;

    #[cfg(debug_assertions)]
    {
        if let Err(_e) = postcondition::check(program) {
            debug_assert!(false, "stage 3 (mut-to-let) postcondition failed: {_e:?}");
        }
    }
    Ok(())
}
