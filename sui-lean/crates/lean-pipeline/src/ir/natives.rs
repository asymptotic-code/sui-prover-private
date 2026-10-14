//! Native function declarations.
//!
//! `program.functions` holds *translated* user Move functions only. Any
//! function the pipeline does not own a body for -- framework natives
//! (`std::vector::push_back`, `sui::transfer::transfer`, ...),
//! user-declared `native fun` in spec sources, and pipeline-synthesized
//! "natives" with prelude-provided implementations (stage 10's
//! `BoundedU{N}_<op>` family) -- lives here as a [`NativeDecl`].
//!
//! See `plans/lean-pipeline/no-stubs-templated-natives.md` for the
//! design rationale ("no stubs, no `sorry`d natives") and migration
//! plan.

use std::collections::BTreeMap;

use super::function::{Effects, Function, Signature};
use super::{FunId, ModId};

/// All native declarations in a [`Program`](super::program::Program).
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct NativeRegistry {
    pub decls: BTreeMap<FunId, NativeDecl>,
}

/// Metadata for a single native function.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct NativeDecl {
    pub module: ModId,
    /// Human-readable Lean name -- matches the source Move function's
    /// name (e.g. `push_back`) or the synthesised stage-10 name
    /// (e.g. `BoundedU64_add`).
    pub name: String,
    pub signature: Signature,
    /// 4-dimensional side-effect classification. See
    /// [`Effects`] for the dimensions and lattice. Populated by
    /// stage 2's `native_effects` allowlist (with
    /// [`Effects::CONSERVATIVE`] as the fallback for unknown
    /// entries).
    pub effects: Effects,
    /// `true` when the user explicitly annotated the function with
    /// `#[ext(pure)]`.
    pub explicit_pure: bool,
    /// `true` when this native lives in a lemma package
    /// (Sui, MoveStdlib, Prover) and the hand-written
    /// `.lean` file under `lemmas/natives/...` provides its
    /// definition. `false` for user-declared `native fun` in spec
    /// sources.
    pub is_framework: bool,
    /// `Some(target_fid)` when this native is a spec companion
    /// (currently only stage-10's synthesised `.aborts` companions).
    /// `None` for plain natives.
    pub spec_target: Option<FunId>,
    /// User-declared `native fun` marker. `Some(is_spec_only)` iff this
    /// native was declared with the Move `native` keyword in a
    /// **user** (non-framework-allowlisted) module -- a hand-defined
    /// datatype-invariant predicate or similar. When rendered code references
    /// one, the pipeline emits no fallback body. It imports a hand-written
    /// `<Module>Natives.lean` copied from the flat
    /// `<package-root>/lean/natives/` path for the root package, or from
    /// `<package-root>/lean/natives/<Package>/` for a dependency package.
    /// Unreferenced declarations require no file and emit no definition. The
    /// wrapped bool records whether the native carries `#[spec_only]` (on the
    /// function or its module). An exact root-package Lean definition for a
    /// spec-only native is accepted as authored specification vocabulary; a
    /// root runtime native or dependency native still needs an explicit,
    /// identity-matched native-model trust rule.
    /// `None` for framework-allowlisted natives (their Lean defs live
    /// in `lemmas/natives/`) and pipeline-synthesised natives
    /// (connectives, `.aborts` companions, stage-10 `BoundedU*`, ghost
    /// opaque outputs).
    pub user_native: Option<bool>,
}

/// A resolved callee. Returned by
/// [`Program::lookup_callee`](super::program::Program::lookup_callee).
#[derive(Debug, Clone, Copy)]
pub enum CalleeRef<'a> {
    Translated(&'a Function),
    Native(&'a NativeDecl),
}

impl<'a> CalleeRef<'a> {
    pub fn module(self) -> ModId {
        match self {
            CalleeRef::Translated(f) => f.module,
            CalleeRef::Native(d) => d.module,
        }
    }

    pub fn name(self) -> &'a str {
        match self {
            CalleeRef::Translated(f) => &f.name,
            CalleeRef::Native(d) => &d.name,
        }
    }

    pub fn signature(self) -> &'a Signature {
        match self {
            CalleeRef::Translated(f) => &f.signature,
            CalleeRef::Native(d) => &d.signature,
        }
    }

    pub fn effects(self) -> Effects {
        match self {
            CalleeRef::Translated(f) => f.effects,
            CalleeRef::Native(d) => d.effects,
        }
    }

    pub fn explicit_pure(self) -> bool {
        match self {
            CalleeRef::Translated(f) => f.explicit_pure,
            CalleeRef::Native(d) => d.explicit_pure,
        }
    }

    /// Post step 5 of `no-stubs-templated-natives.md`: `Function::is_native`
    /// has been removed; the invariant "no Function in `program.functions`
    /// is native" holds structurally, and this method reduces to a
    /// variant match.
    pub fn is_native(self) -> bool {
        matches!(self, CalleeRef::Native(_))
    }
}
