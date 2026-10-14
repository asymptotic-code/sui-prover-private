//! Function shapes.
//!
//! See `plans/lean-pipeline/ir.md` "Function structure" section.

use super::expr::Block;
use super::ty::Type;
use super::{FunId, ModId, VarId};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Param {
    /// User-visible name (for human-readable Lean output).
    pub name: String,
    /// Unique SSA id.
    pub var: VarId,
    pub ty: Type,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Signature {
    pub type_params: Vec<String>,
    pub params: Vec<Param>,
    pub return_type: Type,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Function {
    pub module: ModId,
    /// Human-readable Lean name (`f`, `f.aborts`, `f.while_0`, ...).
    pub name: String,
    pub signature: Signature,
    pub body: Block,
    /// Structural role. The renderer dispatches on this; the pipeline
    /// uses it to track relationships (loop helpers <-> their parent,
    /// spec companions <-> their target).
    pub kind: FunctionKind,
    /// Side-effect classification along four orthogonal axes
    /// (aborts / det / mutation / world writes). Computed by stage 2's pre-pass
    /// over the dependency graph (`classify_effects`) and
    /// re-classified after stage 3 by stage 4. Replaces the
    /// (Total / Det / NoMut as the cleanest point.)
    pub effects: Effects,
    /// `true` when the user explicitly annotated the function as
    /// pure with `#[ext(pure)]`.
    pub explicit_pure: bool,
}

/// Side-effect classification of a function. Computed by stage 2's
/// pre-pass over the dependency graph. Four orthogonal bits, each
/// with its own lattice:
///
/// - [`AbortBit`] -- does this function always terminate with a
///   value, or can it abort / loop forever?
/// - [`DetBit`] -- is its output a deterministic function of its
///   explicit parameters, or does it depend on a hidden source
///   (currently: only the chain's RNG via `random::*`)?
/// - [`MutLevel`] -- does it mutate caller-owned storage through a
///   `&mut` parameter only (LocalMut, absorbed by stage 3's value-form
///   augmentation), or state not captured by any `&mut` parameter
///   (GlobalMut, requires stage 4 to thread `world: World`)?
/// - `world_writes` -- can the function change a threaded `World`, as
///   opposed to only reading it and returning it unchanged? This is
///   independent of [`MutLevel`]: both read-only and writing World
///   functions use `GlobalMut` to request World threading.
///
/// The fixpoint in
/// [`crate::stage_02_ir_cfg::classify_effects`] narrows each
/// dimension independently via [`Effects::meet`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Effects {
    pub aborts: AbortBit,
    pub det: DetBit,
    pub mutation: MutLevel,
    /// Conservative may-write bit for the threaded World value.
    pub world_writes: bool,
}

/// Termination / abort axis. `Total` means the function always
/// terminates with a value; `Partial` covers any panic source --
/// arithmetic overflow, cast truncation, bounds check, explicit
/// `abort`, or a potentially non-terminating loop.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum AbortBit {
    Total,
    Partial,
}

/// Determinism axis. `NonDet` means the function's output depends on
/// state not captured by its explicit parameters. In Move today the
/// only sources are `random::*` natives that consume from a hidden
/// entropy source -- but the dimension is here so oracle reads /
/// clock advances can land cleanly when they appear.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum DetBit {
    Det,
    NonDet,
}

/// Mutation axis with three levels, declared narrow-to-wide so the
/// derived `Ord` matches the lattice direction.
///
/// - `NoMut` -- no observable post-state change of anything.
/// - `LocalMut` -- mutates only through `&mut` parameters. Stage 3's
///   value-form return augmentation absorbs the mutation; no world
///   threading needed.
/// - `GlobalMut` -- depends on external state not captured by any `&mut`
///   parameter. Stage 4 must thread `world: World` through every caller.
///   This includes readers as well as transfer/event/delete/random writers;
///   [`Effects::world_writes`] distinguishes whether the World may change.
///
/// Quantifier bodies (`forall!` / `map!`) reject `LocalMut` and any callee
/// with `world_writes`. A read-only GlobalMut callee may inspect the fixed
/// quantifier-entry World snapshot.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum MutLevel {
    NoMut,
    LocalMut,
    GlobalMut,
}

impl Effects {
    /// All four dimensions at their cleanest: total, deterministic,
    /// no mutation, and no World writes. Used as the body-walker seed for non-native
    /// functions, the `#[ext(pure)]` lock target, and the
    /// classification of pure readers (collection getters, hash,
    /// arithmetic comparisons).
    pub const PURE: Self = Effects {
        aborts: AbortBit::Total,
        det: DetBit::Det,
        mutation: MutLevel::NoMut,
        world_writes: false,
    };

    /// World-reading classification for `#[ext(world)]` natives
    /// (hand-written datatype-invariant predicates over df-backed
    /// state). Reads global/dynamic-field state -- so `GlobalMut` on
    /// the mutation axis, which seeds `compute_needs_world` and threads
    /// `world` through every caller -- but neither aborts (`Total`) nor
    /// is non-deterministic (`Det`): the Lean body returns the world
    /// unchanged. Distinct from [`Effects::CONSERVATIVE`], which would
    /// mis-classify the predicate as `Partial`/`NonDet`.
    pub const WORLD: Self = Effects {
        aborts: AbortBit::Total,
        det: DetBit::Det,
        mutation: MutLevel::GlobalMut,
        world_writes: false,
    };

    /// Maximum-conservative classification: may abort, non-det,
    /// touches global state. The default for natives missing from the
    /// classification table, validate-time stubs, and fixture
    /// stand-ins.
    pub const CONSERVATIVE: Self = Effects {
        aborts: AbortBit::Partial,
        det: DetBit::NonDet,
        mutation: MutLevel::GlobalMut,
        world_writes: true,
    };

    /// Point-wise lattice meet across all four dimensions. Narrows
    /// the caller's classification toward the callee's: a function
    /// that calls a Partial callee becomes (at least) Partial on the
    /// abort axis, regardless of what other axes either side carries.
    ///
    /// Idempotent, commutative, associative; [`Effects::PURE`] is the
    /// identity and [`Effects::CONSERVATIVE`] is the absorber.
    pub fn meet(self, other: Self) -> Self {
        Effects {
            aborts: self.aborts.max(other.aborts),
            det: self.det.max(other.det),
            mutation: self.mutation.max(other.mutation),
            world_writes: self.world_writes || other.world_writes,
        }
    }
}

impl Default for Effects {
    fn default() -> Self {
        Self::CONSERVATIVE
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum FunctionKind {
    Source,
    Spec {
        kind: SpecKind,
        target: FunId,
    },
    LoopBody {
        parent: FunId,
        slot: u32,
    },
    LoopAfter {
        parent: FunId,
        slot: u32,
    },
    Test {
        expectation: TestExpectation,
    },
    Synthetic,
    /// A generated proof obligation (`stage_12_obligations`): its
    /// `body` is the Bool-encoded statement about `target` (the
    /// prove-target function it constrains). The render layer emits it
    /// in two places (phase 8): in the module file as a named
    /// proposition `def NAME (params) : Prop := <body as Prop>`, and in
    /// a durable sibling `<Mod>_Proofs.lean` as a module-qualified
    /// `<pkg>.<mod>_Proofs.NAME` theorem referencing that prop by name.
    /// The proof module exports the short name for compatibility with
    /// sibling proof imports. Carries no proof in the IR -- the proof
    /// file's `by sorry` is the human-editable seed.
    Theorem {
        target: FunId,
        /// Spec wrapper from which stage 12 synthesized this obligation.
        /// Kept separately from `target` so the rendered manifest can be
        /// checked against the authoritative PackageTargets roster.
        source: FunId,
    },
    /// A generated *trusted* obligation (`stage_12_obligations`): same
    /// Bool-encoded statement shape as [`FunctionKind::Theorem`], but its
    /// truth is ASSUMED, not proven. Synthesized for trusted specs
    /// (`Program::trusted_spec_to_impl`): `#[spec(target=...)]` without
    /// `prove` or with `skip`, and `run_on="boogie"` specs (proven on the
    /// Boogie side of the hybrid flow). The render layer emits it in the
    /// module file only: the named proposition `def NAME (params) : Prop`
    /// followed by `axiom NAME_holds (params) : <module_ns>.NAME args`.
    /// Never seeded into `<Mod>_Proofs.lean` -- there is nothing to
    /// prove. The trust boundary stays auditable via `#print axioms`.
    Axiom {
        target: FunId,
        /// Trusted spec wrapper from which stage 12 synthesized this
        /// obligation. Used for proof-manifest completeness checks.
        source: FunId,
        reason: TrustReason,
    },
}

/// Why a trusted obligation is ASSUMED rather than proven. Carried from
/// the upstream `PackageTargets` classification through
/// `Program::trusted_spec_to_impl` into `FunctionKind::Axiom` and the
/// rendered `obligations.toml`, so proof-status reports can split the
/// trust surface (lean-proven vs boogie-proven vs skipped).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TrustReason {
    /// `#[spec(target=...)]` without `prove`.
    NonProve,
    /// `#[spec(prove, skip)]`.
    Skip,
    /// `#[spec(prove, run_on="boogie")]` -- proven by the Boogie backend.
    Boogie,
}

impl FunctionKind {
    /// Parent `FunId` of a loop helper (`LoopBody`/`LoopAfter`), else `None`.
    pub fn loop_parent(&self) -> Option<FunId> {
        match self {
            FunctionKind::LoopBody { parent, .. } | FunctionKind::LoopAfter { parent, .. } => {
                Some(*parent)
            }
            _ => None,
        }
    }

    /// Slot index of a loop helper (`LoopBody`/`LoopAfter`), else `None`.
    pub fn loop_slot(&self) -> Option<u32> {
        match self {
            FunctionKind::LoopBody { slot, .. } | FunctionKind::LoopAfter { slot, .. } => {
                Some(*slot)
            }
            _ => None,
        }
    }

    /// True iff this is a loop helper (`LoopBody` or `LoopAfter`).
    pub fn is_loop_helper(&self) -> bool {
        self.loop_parent().is_some()
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SpecKind {
    Aborts,
    Requires,
    Ensures,
    /// The conjunction of the spec wrapper's `prover::asserts(p)`
    /// predicates, as a standalone Bool companion (`<f>.asserts`). The
    /// asserts are *also* folded into `.aborts` by `aborts_variant`;
    /// this exposes them separately so the abort-faithfulness theorem
    /// (`impl.aborts <-> not asserts`) and the functional theorem
    /// (`requires -> asserts -> ensures`) can reference them directly.
    Asserts,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TestExpectation {
    MustSucceed,
    MustAbort,
}

#[cfg(test)]
mod effects_tests {
    use super::*;

    #[test]
    fn pure_constant_is_pure() {
        assert_eq!(Effects::PURE.aborts, AbortBit::Total);
        assert_eq!(Effects::PURE.det, DetBit::Det);
        assert_eq!(Effects::PURE.mutation, MutLevel::NoMut);
        assert!(!Effects::PURE.world_writes);
    }

    #[test]
    fn conservative_constant_is_conservative() {
        assert_eq!(Effects::CONSERVATIVE.aborts, AbortBit::Partial);
        assert_eq!(Effects::CONSERVATIVE.det, DetBit::NonDet);
        assert_eq!(Effects::CONSERVATIVE.mutation, MutLevel::GlobalMut);
        assert!(Effects::CONSERVATIVE.world_writes);
    }

    #[test]
    fn world_constant_reads_world_without_aborting() {
        // `#[ext(world)]` classification: world-reading (GlobalMut, so
        // it seeds `compute_needs_world`) but abort-free + deterministic.
        assert_eq!(Effects::WORLD.aborts, AbortBit::Total);
        assert_eq!(Effects::WORLD.det, DetBit::Det);
        assert_eq!(Effects::WORLD.mutation, MutLevel::GlobalMut);
        assert!(!Effects::WORLD.world_writes);
    }

    #[test]
    fn default_is_conservative() {
        assert_eq!(Effects::default(), Effects::CONSERVATIVE);
    }

    #[test]
    fn ord_matches_lattice_direction_aborts() {
        assert!(AbortBit::Total < AbortBit::Partial);
    }

    #[test]
    fn ord_matches_lattice_direction_det() {
        assert!(DetBit::Det < DetBit::NonDet);
    }

    #[test]
    fn ord_matches_lattice_direction_mutation() {
        assert!(MutLevel::NoMut < MutLevel::LocalMut);
        assert!(MutLevel::LocalMut < MutLevel::GlobalMut);
    }

    #[test]
    fn meet_is_pointwise() {
        let a = Effects {
            aborts: AbortBit::Total,
            det: DetBit::Det,
            mutation: MutLevel::NoMut,
            world_writes: false,
        };
        let b = Effects {
            aborts: AbortBit::Partial,
            det: DetBit::Det,
            mutation: MutLevel::LocalMut,
            world_writes: true,
        };
        let m = a.meet(b);
        assert_eq!(m.aborts, AbortBit::Partial);
        assert_eq!(m.det, DetBit::Det);
        assert_eq!(m.mutation, MutLevel::LocalMut);
        assert!(m.world_writes);
    }

    #[test]
    fn meet_is_idempotent() {
        let e = Effects {
            aborts: AbortBit::Partial,
            det: DetBit::NonDet,
            mutation: MutLevel::LocalMut,
            world_writes: true,
        };
        assert_eq!(e.meet(e), e);
    }

    #[test]
    fn meet_is_commutative() {
        let a = Effects {
            aborts: AbortBit::Total,
            det: DetBit::NonDet,
            mutation: MutLevel::LocalMut,
            world_writes: false,
        };
        let b = Effects {
            aborts: AbortBit::Partial,
            det: DetBit::Det,
            mutation: MutLevel::GlobalMut,
            world_writes: true,
        };
        assert_eq!(a.meet(b), b.meet(a));
    }

    #[test]
    fn meet_is_associative() {
        let a = Effects::PURE;
        let b = Effects {
            aborts: AbortBit::Partial,
            det: DetBit::Det,
            mutation: MutLevel::LocalMut,
            world_writes: false,
        };
        let c = Effects {
            aborts: AbortBit::Total,
            det: DetBit::NonDet,
            mutation: MutLevel::GlobalMut,
            world_writes: true,
        };
        assert_eq!(a.meet(b).meet(c), a.meet(b.meet(c)));
    }

    #[test]
    fn pure_is_meet_identity() {
        let e = Effects {
            aborts: AbortBit::Partial,
            det: DetBit::NonDet,
            mutation: MutLevel::LocalMut,
            world_writes: true,
        };
        assert_eq!(Effects::PURE.meet(e), e);
        assert_eq!(e.meet(Effects::PURE), e);
    }

    #[test]
    fn conservative_is_meet_absorber() {
        let e = Effects::PURE;
        assert_eq!(Effects::CONSERVATIVE.meet(e), Effects::CONSERVATIVE);
        assert_eq!(e.meet(Effects::CONSERVATIVE), Effects::CONSERVATIVE);
    }
}
