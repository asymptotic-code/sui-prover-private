// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

use indexmap::IndexMap;
use move_model::model::{DatatypeId, FunId, ModuleId, QualifiedId};
use std::borrow::Borrow;
use std::collections::BTreeMap;

use crate::analysis::{collect_imports, fold_constants, order_by_dependencies};
use crate::data::ir::IRNode;
use crate::{FunctionID, Type};

pub use structure::StructID;

pub mod conversion;
pub mod functions;
pub mod ir;
pub mod structure;
pub mod types;
pub mod variables;

pub type ModuleID = usize;

/// Trait for items that can have dependencies on other items of the same type
pub trait Dependable {
    type Id: Copy + Eq + std::hash::Hash + Ord + std::fmt::Debug;
    type MoveKey: Copy + Eq + std::hash::Hash + Ord + std::fmt::Debug;

    fn dependencies(&self) -> impl Iterator<Item = Self::Id>;
    fn with_recursion_info(self, mutual_group_id: Option<usize>, is_recursive: bool) -> Self;
    fn get_mutual_group_id(&self) -> Option<usize>;
}

// ============================================================================
// Program Item Storage
// ============================================================================

/// Storage for program items with ID allocation
#[derive(Debug, Clone)]
pub struct ItemStore<MoveKey: Ord, Item> {
    ids: BTreeMap<MoveKey, usize>,
    pub items: IndexMap<usize, Item>,
}

impl<MoveKey: Ord, Item> Default for ItemStore<MoveKey, Item> {
    fn default() -> Self {
        Self {
            ids: BTreeMap::new(),
            items: IndexMap::new(),
        }
    }
}

impl<MoveKey: Ord + Copy, Item> ItemStore<MoveKey, Item> {
    /// Look up the ID for a key, creating one if it doesn't exist
    pub fn id_for_key(&mut self, key: MoveKey) -> usize {
        let next_id = self.ids.len();
        *self.ids.entry(key).or_insert(next_id)
    }

    pub fn has(&self, id: usize) -> bool {
        self.items.contains_key(&id)
    }
    pub fn create(&mut self, key: MoveKey, item: Item) {
        let id = self.id_for_key(key);
        self.items.insert(id, item);
    }
    pub fn get(&self, id: impl Borrow<usize>) -> &Item {
        let id = id.borrow();
        self.items.get(id).unwrap_or_else(|| {
            panic!(
                "Item {} should exist, but only have IDs: {:?}",
                id,
                self.items.keys().collect::<Vec<_>>()
            )
        })
    }
    pub fn get_mut(&mut self, id: impl Borrow<usize>) -> &mut Item {
        self.items.get_mut(id.borrow()).expect("Item should exist")
    }
    pub fn iter(&self) -> impl Iterator<Item = (&usize, &Item)> {
        self.items.iter()
    }
    pub fn iter_mut(&mut self) -> impl Iterator<Item = &mut Item> {
        self.items.values_mut()
    }
    pub fn iter_ids(&self) -> impl Iterator<Item = usize> + '_ {
        self.items.keys().copied()
    }
    pub fn values(&self) -> impl Iterator<Item = &Item> {
        self.items.values()
    }
    pub fn len(&self) -> usize {
        self.items.len()
    }
    pub fn is_empty(&self) -> bool {
        self.items.is_empty()
    }

    pub fn get_id_for_key(&self, key: &MoveKey) -> Option<usize> {
        self.ids.get(key).copied()
    }
}

impl<'a, MoveKey: Ord, Item> IntoIterator for &'a ItemStore<MoveKey, Item> {
    type Item = (&'a usize, &'a Item);
    type IntoIter = indexmap::map::Iter<'a, usize, Item>;
    fn into_iter(self) -> Self::IntoIter {
        self.items.iter()
    }
}

// ============================================================================
// Function Storage — flat list of functions
// ============================================================================

/// Flat storage for all functions. Every function (defs, aborts, requires,
/// ensures, theorems) is stored the same way. Move-keyed functions get an
/// entry in the key lookup for bytecode call resolution. All other functions
/// are just appended with auto-assigned IDs.
#[derive(Debug, Clone, Default)]
pub struct FunctionStore {
    /// Maps Move qualified IDs to function IDs (for bytecode call resolution)
    ids: BTreeMap<QualifiedId<FunId>, usize>,
    /// All functions, keyed by ID
    functions: IndexMap<usize, functions::Function>,
    /// Next ID to assign
    next_id: usize,
}

impl FunctionStore {
    /// Look up the ID for a Move key, creating one if it doesn't exist
    pub fn id_for_key(&mut self, key: QualifiedId<FunId>) -> usize {
        let next = self.next_id;
        let id = *self.ids.entry(key).or_insert(next);
        if id == next {
            self.next_id += 1;
        }
        id
    }

    /// Check if a function exists
    pub fn has(&self, id: usize) -> bool {
        self.functions.contains_key(&id)
    }

    /// Create a function with a Move key
    pub fn create(&mut self, key: QualifiedId<FunId>, func: functions::Function) {
        let id = self.id_for_key(key);
        self.functions.insert(id, func);
    }

    /// Add a function without a Move key (aborts, requires, ensures, etc.)
    /// Returns the assigned ID.
    pub fn add(&mut self, func: functions::Function) -> usize {
        let id = self.next_id;
        self.next_id += 1;
        self.functions.insert(id, func);
        id
    }

    /// Reserve a function ID without inserting a function.
    /// Use `insert` later to fill it in.
    pub fn reserve_id(&mut self) -> usize {
        let id = self.next_id;
        self.next_id += 1;
        id
    }

    /// Insert a function at a previously reserved ID.
    pub fn insert(&mut self, id: usize, func: functions::Function) {
        self.functions.insert(id, func);
    }

    /// Look up the ID for a Move key without creating one
    pub fn get_id_for_move_key(&self, key: &QualifiedId<FunId>) -> Option<usize> {
        self.ids.get(key).copied()
    }

    /// Get a function by ID
    pub fn get(&self, id: &usize) -> &functions::Function {
        self.functions.get(id).unwrap_or_else(|| {
            panic!(
                "Function {} should exist, but only have IDs: {:?}",
                id,
                self.functions.keys().collect::<Vec<_>>()
            )
        })
    }

    /// Try to get a function by ID
    pub fn try_get(&self, id: &usize) -> Option<&functions::Function> {
        self.functions.get(id)
    }

    /// Get a mutable reference to a function by ID
    pub fn get_mut(&mut self, id: usize) -> &mut functions::Function {
        self.functions.get_mut(&id).expect("Function should exist")
    }

    /// Iterate over Move qualified IDs and their corresponding IDs
    pub fn iter_move_keys(&self) -> impl Iterator<Item = (QualifiedId<FunId>, usize)> + '_ {
        self.ids.iter().map(|(qid, &id)| (*qid, id))
    }

    /// Iterate over all functions with their IDs
    pub fn iter(&self) -> impl Iterator<Item = (usize, &functions::Function)> {
        self.functions.iter().map(|(&id, f)| (id, f))
    }

    /// Iterate mutably over all functions
    pub fn iter_mut(&mut self) -> impl Iterator<Item = (usize, &mut functions::Function)> {
        self.functions.iter_mut().map(|(&id, f)| (id, f))
    }

    /// Number of functions
    pub fn len(&self) -> usize {
        self.functions.len()
    }

    /// Check if empty
    pub fn is_empty(&self) -> bool {
        self.functions.is_empty()
    }

    /// Get mutable access to the inner map (for dependency sorting)
    pub fn functions_mut(&mut self) -> &mut IndexMap<usize, functions::Function> {
        &mut self.functions
    }

    /// Iterate over all function values
    pub fn values(&self) -> impl Iterator<Item = &functions::Function> {
        self.functions.values()
    }

    /// Delete a function
    pub fn delete_function(&mut self, id: usize) {
        self.functions.swap_remove(&id);
    }

    /// Iterate over function IDs
    pub fn iter_ids(&self) -> impl Iterator<Item = usize> + '_ {
        self.functions.keys().copied()
    }
}

// ============================================================================
// Complete Program IR
// ============================================================================

/// Which "face" of the IR the pipeline is producing.
///
/// Most passes are mode-independent (mutable threading, dynamic-field
/// rewriting, type inference). A handful of passes — abort stripping,
/// spec extraction, dead-param elimination — are designed for the
/// **Spec** face and would erase information the **Test** face needs
/// (notably `IRNode::Abort` nodes inside the body and parameters that
/// are only consumed by abort conditions). `Program::finalize_with_mode`
/// gates those passes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BuildMode {
    /// Default Spec rendering mode. Bodies are stripped to pure forms,
    /// aborts moved to companion `.aborts` predicates, dead params
    /// removed.
    Spec,
    /// Test rendering mode for `--test`. Preserves `IRNode::Abort`
    /// inline so the monadic Test renderer evaluates them, and keeps
    /// parameters live since the body still references them through
    /// the abort condition.
    Test,
}

impl Default for BuildMode {
    fn default() -> Self {
        BuildMode::Spec
    }
}

#[derive(Debug, Clone, Default)]
pub struct Program {
    pub modules: ItemStore<ModuleId, Module>,
    pub structs: ItemStore<QualifiedId<DatatypeId>, structure::Struct>,
    pub functions: FunctionStore,
    /// Conversion functions between spec and implementation types
    pub conversions: conversion::ConversionRegistry,
    /// Namespace overrides for modules whose names collide across packages.
    pub namespace_overrides: std::collections::HashMap<ModuleID, String>,
    /// Function ID for the prover::requires intrinsic (if encountered)
    pub requires_function_id: Option<FunctionID>,
    /// Function ID for the prover::ensures intrinsic (if encountered)
    pub ensures_function_id: Option<FunctionID>,
    /// Function ID for the prover::asserts intrinsic (if encountered)
    pub asserts_function_id: Option<FunctionID>,
    /// Maps spec module IDs to their corresponding impl module IDs.
    /// Used when spec modules are merged into impl modules during rendering.
    /// When calling a function from a merged spec module, the impl module's namespace should be used.
    pub spec_to_impl: std::collections::HashMap<ModuleID, ModuleID>,
    /// Maps module IDs to their actual file location (package_name, file_stem).
    /// For modules in an import cycle (SCC), this points to the merged file.
    /// Used to resolve import paths during rendering.
    pub module_to_file: std::collections::HashMap<ModuleID, (String, String)>,
    /// Synthetic TypedMap function IDs for rewritten dynamic field operations.
    /// Set by the dynamic_field_rewriting pass.
    pub typed_map_functions: Option<crate::analysis::dynamic_field_rewriting::TypedMapFunctions>,
    /// Maps a loop-bearing function's base name (e.g. `pool_token_exchange_rate_at_epoch`)
    /// to the FunctionID of its `#[spec_only(loop_inv(target=...))]` invariant.
    /// Set by the program builder from the loop_inv attribute. Used to thread the
    /// invariant as a hypothesis parameter onto generated `while_*`/`after_*`
    /// helpers so loop termination can be discharged instead of `sorry`d.
    /// Keyed by the *target* function's qualified Move name so the while-helper
    /// emitter (which runs while translating the target) can look it up.
    pub loop_invariants: std::collections::HashMap<String, FunctionID>,
    /// Maps a generated loop helper's `FunctionID` (the `while_*` helper, or its
    /// `.aborts` companion) to the loop-invariant hypothesis parameter injected
    /// onto it. `<hook_name>` is a user-provided `Prop` predicate (defined in a
    /// `Proofs/`/`Termination/` file) capturing the loop-invariant fact the
    /// `decreasing_by` proof needs in scope. Set by `emit_while` for loops whose
    /// target carries a `#[spec_only(loop_inv(...))]` (see [`loop_invariants`]).
    /// This is a finalize-internal recording table: `materialize_proof_params`
    /// drains it into each helper's `FunctionSignature::proof_params`, which is
    /// the single source of truth every later consumer reads. Keyed by ID (not
    /// name) so option-shape aborts duplicates with a shared name stay distinct.
    pub loop_inv_hyps: std::collections::HashMap<FunctionID, LoopInvHyp>,
    /// Extra proof-typed parameters threaded by the loop-invariant entry
    /// cascade. Keyed by `FunctionID` → list of `(param_name, prop_text)`, where
    /// the prop text is a verbatim applied predicate (e.g. `f.precond pool
    /// epoch`). Threads a precondition hypothesis (`hpre`) onto a loop_inv
    /// target impl and every same-module spec function that references it — the
    /// precondition the user's entry lemma derives the loop invariant from. Like
    /// [`loop_inv_hyps`], this is a finalize-internal recording table drained by
    /// `materialize_proof_params` into `FunctionSignature::proof_params`. Keyed
    /// by ID (not name) so two distinct functions sharing a name — which the
    /// option-shape aborts composition can produce — never collide into one
    /// bucket (the source of the historical duplicate-`hpre` bug).
    pub fn_proof_params: std::collections::HashMap<FunctionID, Vec<(String, String)>>,
    /// Display names of generated loop_inv target impls (functions containing a
    /// loop-helper entry call). The renderer emits their loop-guarding `if` as a
    /// dependent `if h : cond` and replaces the entry call's placeholder proof
    /// with `<helper>.loop_entry <args> <hpre> <h>` (a user lemma). See the
    /// loop-invariant entry cascade in `analysis/loop_inv_entry.rs`.
    pub loop_inv_entry_impls: std::collections::HashSet<String>,
    /// Lean-side termination declarations harvested from the client's
    /// `Termination/<module>.lean` files (the `def <name>.loop_hyp` / `def
    /// <name>.precond` headers). Drives `thread_lean_terminations`: a generic,
    /// name-free replacement for the old per-function `max_heapify`/`derive_gas`
    /// passes. A recursive helper whose name appears in `loop_hyp` carries the
    /// `hinv` invariant; `precond` is the client contract that the size/entry
    /// preconditions propagated to external callers resolve against. Stashed by
    /// the backend's `pre_finalize` hook before `finalize` runs the threading.
    pub lean_termination_decls: LeanTerminationDecls,
    /// IDs of functions threaded by the callee-`requires` entry cascade (they
    /// gained an `hpre` proof param for a callee's `requires`). A caller that
    /// cannot supply that precondition forwards an `IRNode::Abort` placeholder in
    /// the proof slot; the renderer emits `sorry` there (a `Prop` inhabitant)
    /// rather than the `MoveAbort` value an `Abort` would otherwise render as.
    /// See `analysis/callee_requires_entry.rs`.
    pub callee_requires_impls: std::collections::HashSet<FunctionID>,
    /// IDs of caller functions threaded by the callee-`requires` PRECOND cascade
    /// (`analysis/callee_requires_precond.rs`). These are `.while_`/`.after_`
    /// loop helpers or plain value defs / `.aborts` whose call into a
    /// `callee_requires_impls` callee G passes a `requires`-slot argument that
    /// references loop-body temps / rebound locals (not the caller's params), so
    /// no param-typed `hpre` for G can name it. Instead the caller carries a
    /// client-declared `hpre : <caller-base>.precond <params>`, and at G's call
    /// site the renderer emits the client `(by <G-namespace>_<G-base>_requires)`
    /// macro (which discharges G's `requires` from the in-scope precond) rather
    /// than the bare `sorry` the plain `callee_requires_impls` slot would emit.
    /// Keyed by ID (NOT name) to avoid the cross-module same-name collision the
    /// `render.rs:360` warning calls out.
    pub callee_requires_precond_callers: std::collections::HashSet<FunctionID>,
    /// `.aborts` functions decomposed into side-car segment chains by
    /// `analysis/decompose_aborts.rs`: `(aborts_id, seg_1_id)`. The renderer
    /// emits a `<fn>.aborts.decompose ... := rfl` recomposition lemma for each.
    pub aborts_decompositions: Vec<(FunctionID, FunctionID)>,
    /// Obligation bundles (verification-condition form) for oversized
    /// `.aborts` functions: named leaf obligations plus a generator-built
    /// structural proof that they imply `.aborts = none`. Produced by
    /// `analysis/decompose_aborts.rs`; rendered as `<fn>.aborts.ob_k` defs and
    /// a `<fn>.aborts_none_of` theorem whose proof term mirrors the body.
    pub aborts_bundles: Vec<AbortsBundle>,
    /// Obligation bundles for `.ensures` companions (unified-backend design
    /// §5.1, Phase 3.1): the `.aborts` bundle machinery generalized to the
    /// ensures spine (Let spine → `&&`/`ite`/Prop-leaf terminals). Produced by
    /// `analysis/decompose_aborts.rs` under the per-package `ensures_bundles`
    /// module_options gate; rendered as `<fn>.ensures*.ob_k` defs and a
    /// `<fn>.ensures*_of` theorem with a generator-built structural proof.
    pub ensures_bundles: Vec<AbortsBundle>,
    /// Equation/projection lemma sets for impl defs rendered `@[irreducible]`
    /// under the per-MODULE `irreducible_defs` module_options gate (unified-
    /// backend design §5.3, Phase 3.2). Produced by
    /// `analysis/equation_lemmas.rs`; the renderer suppresses `@[reducible]`
    /// on member defs, emits the lemma block (each proven at generation time,
    /// BEFORE the attribute applies), then `attribute [irreducible] <fn>`.
    pub equation_lemmas: Vec<EquationLemmaSet>,
    /// Stored-value data-invariant hypotheses threaded onto SPEC functions by
    /// `analysis/stored_value_invariants.rs` (the assume half of the
    /// discipline). Like [`fn_proof_params`], a finalize-internal recording
    /// table drained by `materialize_proof_params` — hdinv params are appended
    /// AFTER any hpre params so client proof references are stable.
    pub fn_data_inv_params: std::collections::HashMap<FunctionID, Vec<functions::ProofParam>>,
    /// Preservation obligations (the assert half): one per (spec fn, slot,
    /// updated-container result component). Rendered into the Correctness file
    /// next to the spec's own obligation. Keyed by the `<base>_spec.aborts`
    /// spec function id.
    pub data_inv_goals: std::collections::HashMap<FunctionID, Vec<DataInvGoal>>,
    /// World-mode preservation obligations (unified-backend design §7,
    /// Phase 5): one per (spec fn, invariant parent source, world-returning
    /// impl). Concludes `Prover.World.World.allDf ((impl …)<proj>)
    /// (World.uidNat <parent_expr>) <pred>`. Keyed like [`data_inv_goals`].
    pub data_inv_world_goals: std::collections::HashMap<FunctionID, Vec<WorldDataInvGoal>>,
    /// Per-native ghost-marker seed for the upstream spec-global mechanism:
    /// `(K, V)` marker pairs a ghost-writing native's `#[spec(target=...)]`
    /// spec declares (K a marker struct type, V the value type). Derived by
    /// the backend from the Move model (gated to markers some target-package
    /// spec declares) and handed to `ProgramBuilder`; consumed (drained) by
    /// `analysis/ghost_threading.rs` in `finalize`. Empty for programs whose
    /// specs never declare ghost markers — the pass is then a no-op and the
    /// output is byte-identical.
    pub ghost_native_seed: BTreeMap<FunctionID, Vec<(Type, Type)>>,
    /// The threaded ghost-variable sets after `ghost_threading` ran: every
    /// function (value defs, `.aborts` faces, loop helpers, spec wrappers)
    /// that transitively reaches a seeded ghost-writing native, mapped to
    /// the `(K, V)` markers it threads (sorted by marker struct name).
    /// Kept on `Program` for debugging / downstream inspection.
    pub ghost_vars: BTreeMap<FunctionID, Vec<(Type, Type)>>,
    /// IDs of the synthetic `World` module/struct + typed-view natives
    /// registered by `analysis/world_threading.rs` (Phase A). `Some` exactly
    /// when the package opted into `world_mode`; the renderer keys the
    /// `World` type special-case, `Generated/World.lean` emission, the
    /// `import Generated.World` injection, and DF-universe collection off it.
    pub world_functions: Option<crate::analysis::world_threading::WorldFunctions>,
    /// Functions whose mutref return is PAIR-kinded (`Mutable T (S × World)`,
    /// from heterogeneous-phi unification in `world_threading`). Persisted so
    /// the caller-side pair-writeback fixup can re-run at the END of finalize:
    /// the in-threading run rewrites value-nested occurrences that later
    /// optimize passes revert, so the fixup must have the last word over the
    /// final body shape.
    pub pair_mut_fns: std::collections::BTreeSet<FunctionID>,
    /// Frame-lemma sets (unified-backend design §5.4, Phase 4): per threaded
    /// value face, the df footprint + generator-built `FrameDf` proof tree.
    /// Produced by `analysis/frame_lemmas.rs` in world-mode packages only;
    /// the renderer emits `<fn>.dfFootprint` / `<fn>.frame_thm` /
    /// `<fn>.frame_df_out` right after the def. Inexpressible shapes are
    /// dropped LOUDLY at generation (stderr warning naming the function) —
    /// never emitted unprovable or `sorry`'d.
    pub frame_lemmas: Vec<crate::analysis::frame_lemmas::FrameLemmaSet>,
    /// Per-function type-parameter indices that flow into World typed-view
    /// ops (unified-backend design Phase 5, generic state ops). The renderer
    /// emits `[HasCode TyCode <tp>]` instance binders for them. Computed by
    /// `analysis/world_threading::compute_hascode_params`; empty off
    /// world-mode.
    pub fn_hascode_params: BTreeMap<FunctionID, std::collections::BTreeSet<u16>>,
    /// Set by `finalize_for_test`. World-mode frame lemmas (`<fn>.frame_thm` /
    /// `dfFootprint` / `frame_df_out`) are spec/correctness-proof artifacts the
    /// per-test drivers never evaluate (they only run each function's `.aborts`
    /// companion). Suppressing them in test mode avoids compiling frame-proof
    /// combinator trees whose composition can fail on world-mode wrappers
    /// (e.g. `staking_pool::process_pending_stakes_and_withdraws` over
    /// `Table.add`) — unblocking the world-mode test build without affecting
    /// what the drivers execute.
    pub for_test: bool,
    /// Per-function type-param indices that flow (bare or nested) into a
    /// heterogeneous-`bag` / `object_bag` op, directly or transitively. These
    /// need a `[HasCode BagU <tp>]` instance binder so the bag op's `HasCode`
    /// constraint on a generic value type (e.g. `Bag.borrow (Balance T)`)
    /// discharges via the `Generated/BagUInterp` wrapper instance. The `bag`
    /// universe (`BagU`) is separate from the World/df universe (`TyCode`) — a
    /// param may need both binders. Computed by
    /// `analysis/world_threading::compute_bagu_params`.
    pub fn_bagu_params: BTreeMap<FunctionID, std::collections::BTreeSet<u16>>,
}

/// One generated `_data_inv` preservation-goal theorem. All the expression
/// pieces are pre-built over the SPEC function's value-parameter names (the
/// same binders the Correctness obligation uses), so the renderer only
/// formats text. See `analysis/stored_value_invariants.rs`.
#[derive(Debug, Clone)]
pub struct DataInvGoal {
    /// Suffix distinguishing multiple goals per spec (`""`, `"_1"`, ...).
    pub goal_suffix: String,
    /// The impl VALUE function whose result must preserve the invariant.
    pub impl_fn_id: FunctionID,
    /// Number of leading spec value-parameter names to apply the impl to
    /// (the impl's value arity — dead-param elimination can drop trailing
    /// spec params such as `ctx`).
    pub n_args: usize,
    /// Tuple-projection text applied to the impl application (`""`, `".2"`, ...).
    pub proj_expr: String,
    /// Field path from the projected component to the ghost map, including the
    /// leading dot (e.g. `.validators.validator_candidates.dynamic_fields`).
    pub map_tail: String,
    pub key_type: Type,
    pub value_type: Type,
    pub pred: String,
}

/// One generated world-mode `_data_inv` preservation-goal theorem
/// (unified-backend design §7, Phase 5). Stated over the SPEC function's
/// binder names, concluding that the impl's RESULT WORLD still satisfies
/// `allDf` at the invariant's parent uid.
#[derive(Debug, Clone)]
pub struct WorldDataInvGoal {
    /// Suffix distinguishing multiple goals per spec (`""`, `"_1"`, ...).
    pub goal_suffix: String,
    /// The impl VALUE function whose result world must preserve the invariant.
    pub impl_fn_id: FunctionID,
    /// Number of leading spec value-parameter names to apply the impl to
    /// (includes the trailing `__world`).
    pub n_args: usize,
    /// Projection from the impl result to its world component (`""` when the
    /// result IS the world, `".2"` for the augmented pair).
    pub world_proj: String,
    /// The parent-uid expression over the spec's value params
    /// (e.g. `(c.id)`), wrapped by the renderer in `World.uidNat`.
    pub parent_expr: String,
    pub pred: String,
}

/// One leaf verification condition of an `.aborts` obligation bundle.
#[derive(Debug, Clone)]
pub struct AbortsObligation {
    /// Short name (`ob_<k>`); rendered as `<fn>.aborts.ob_<k>`.
    pub name: String,
    /// Typed parameters (a subset of the parent's value parameters).
    pub parameters: Vec<crate::data::functions::Parameter>,
    /// Path conditions guarding the check: `(bool_expr, required_polarity)`.
    /// Rendered as `<expr> = true → …` / `<expr> = false → …` premises.
    pub path: Vec<(IRNode, bool)>,
    /// The check itself.
    pub leaf: AbortsLeaf,
}

/// The conclusion shape of an obligation.
#[derive(Debug, Clone)]
pub enum AbortsLeaf {
    /// A boolean abort guard that must be false: `<expr> = false`.
    GuardFalse(IRNode),
    /// A boolean guard that must be true (abort sits on the else side).
    GuardTrue(IRNode),
    /// An `Option MoveAbort` expression that must be `none` (callee aborts,
    /// or an opaque segment covering a subtree the fine-grained walk skips).
    OptionNone(IRNode),
    /// A Prop-typed expression that must hold (ensures-bundle leaves: the
    /// expression renders directly as the obligation's conclusion — `ToProp`
    /// already renders `(e) = true`, quantifiers render `spec_forall …`, an
    /// opaque Prop segment renders as its call).
    PropHolds(IRNode),
    /// Requires-slot leaf (unified-backend design §5.2, deferred item 2.2,
    /// behind the `requires_leaves` gate): the callee's declared `requires`
    /// hypothesis instantiated at this call site — the renderer substitutes
    /// the callee's param names in its verbatim proof-param type with the
    /// rendered `args`. Paired with [`AbortsLeaf::CalleeNoneUnderRequires`]
    /// via [`AbortsProofNode::RequiresApp`].
    RequiresHolds {
        callee: FunctionID,
        args: Vec<IRNode>,
    },
    /// The callee-aborts leaf under the requires hypothesis:
    /// `∀ (hpre__ : <requires instance>), callee.aborts args hpre__ = none`.
    /// Recomposition against the body's `sorry`-slotted call is definitional
    /// by proof irrelevance.
    CalleeNoneUnderRequires {
        callee: FunctionID,
        args: Vec<IRNode>,
    },
}

/// Structural recomposition proof, mirroring the `.aborts` body. Rendered as
/// a direct term over the `MoveAbort.*_none_*` prelude combinators.
#[derive(Debug, Clone)]
pub enum AbortsProofNode {
    /// The expression is literally (or definitionally) `Option.none`.
    Rfl,
    /// `MoveAbort.orElse_none_of <left> <right>`.
    OrElse(Box<AbortsProofNode>, Box<AbortsProofNode>),
    /// `MoveAbort.bite_none_of_false (h_ob …) <rest>` — abort guard is false.
    GuardFalse {
        ob: usize,
        rest: Box<AbortsProofNode>,
    },
    /// `MoveAbort.bite_none_of_true (h_ob …) <rest>` — abort on the else side.
    GuardTrue {
        ob: usize,
        rest: Box<AbortsProofNode>,
    },
    /// `MoveAbort.bite_none_split (fun hb<d> => <then>) (fun hb<d> => <else>)`.
    BIte(Box<AbortsProofNode>, Box<AbortsProofNode>),
    /// `MoveAbort.bdite_none_split …` — dependent `if h : (c) = true` branch.
    DIte(Box<AbortsProofNode>, Box<AbortsProofNode>),
    /// `h_ob <path binders>` — the obligation is the whole sub-proof.
    Leaf { ob: usize },
    /// `SpecEnsures.and_of <left> <right>` — ensures-bundle split of a
    /// Bool conjunction terminal `(a && b) = true`.
    AndBool(Box<AbortsProofNode>, Box<AbortsProofNode>),
    /// `SpecEnsures.ite_of (fun hb<d> => <then>) (fun hb<d> => <else>)` —
    /// ensures-bundle split of a Prop-branched `if (c : Bool) then P else Q`.
    PIte(Box<AbortsProofNode>, Box<AbortsProofNode>),
    /// `SpecEnsures.bite_eq_true_of …` — ensures-bundle split of a Bool ite
    /// under `= true`: `(if c then a else b) = true`.
    BIteBool(Box<AbortsProofNode>, Box<AbortsProofNode>),
    /// `h_ob_<call> hb… (h_ob_<req> hb…)` — the requires-slot pair (§5.2,
    /// `requires_leaves` gate): the precondition leaf feeds the ∀-bound
    /// callee-aborts leaf; proof irrelevance closes the defeq against the
    /// body's placeholder slot.
    RequiresApp { req_ob: usize, call_ob: usize },
}

/// A complete obligation bundle for one `.aborts` function.
#[derive(Debug, Clone)]
pub struct AbortsBundle {
    pub fn_id: FunctionID,
    pub obligations: Vec<AbortsObligation>,
    pub proof: AbortsProofNode,
}

/// Equation/projection lemmas for one impl def rendered `@[irreducible]`
/// under the `irreducible_defs` gate (unified-backend design §5.3). All
/// expressions are let-substituted (projection-folded) forms closed over the
/// function's own parameters, so the lemma statements never mention body
/// temps. Lemma names deviate from the doc's `F.eq_1`/`F.eq_b`: Lean reserves
/// the autogenerated `<fn>.eq_<n>`/`<fn>.eq_def` equation-lemma namespace, so
/// the generator emits `<fn>.eq_body` / `<fn>.eq_then` / `<fn>.eq_else` /
/// `<fn>.result_<k>` instead.
#[derive(Debug, Clone)]
pub struct EquationLemmaSet {
    pub fn_id: FunctionID,
    /// Whether the whole-body `<fn>.eq_body : <fn> args = <body> := rfl`
    /// lemma is emitted (suppressed for oversized bodies).
    pub unfold: bool,
    /// Terminal-`if` branch lemmas: `(cond', then', else')` — rendered as
    /// `<fn>.eq_then (h : cond' = true) : <fn> args = then'` and the `eq_else`
    /// dual, proven via the `SpecEnsures.ite_then/ite_else` prelude lemmas.
    pub branches: Option<(IRNode, IRNode, IRNode)>,
    /// Tuple-result projection lemmas: `(component index, component expr)` —
    /// rendered as `<fn>.result_<k+1> : (<fn> args)<proj> = expr := rfl`.
    pub projections: Vec<(usize, IRNode)>,
}

/// A loop-invariant hypothesis parameter injected onto a `while_*`/`after_*`
/// helper so its termination proof has the invariant in scope. See
/// [`Program::loop_inv_hyps`].
#[derive(Debug, Clone)]
pub struct LoopInvHyp {
    /// The parameter name (e.g. `hinv`).
    pub hyp_param: String,
    /// The user-provided `Prop` predicate applied to the helper's value params.
    pub hook_name: String,
}

/// Lean-declared termination hooks scanned from `Termination/<module>.lean`.
/// `loop_hyp` holds the names of functions for which the client wrote a
/// `def <name>.loop_hyp` (so the generated helper should carry an `hinv` typed
/// by it); `precond` holds the names for which a `def <name>.precond` exists
/// (the entry/size precondition threaded onto external callers of a loop helper).
#[derive(Debug, Clone, Default)]
pub struct LeanTerminationDecls {
    pub loop_hyp: std::collections::HashSet<String>,
    pub precond: std::collections::HashSet<String>,
    /// Full names of loop helpers for which the client provides a Lean
    /// termination measure (`def <name>.termination`). Such a loop renders with
    /// the real `termination_by <name>.termination` / decreasing macro instead
    /// of the `sorry` default, so its per-iteration body must stay inline for
    /// the decreasing proof to see the loop variable's progress — loop-body
    /// extraction must skip it.
    pub termination: std::collections::HashSet<String>,
    /// Stems of client `def <stem>.data_inv` stored-value invariant
    /// declarations (`<Module>.<Struct>` type-wide, or
    /// `<Module>.<Struct>.<field>` slot-scoped). Scanned from the same
    /// `sources/lean/**/*.lean` sweep as the termination hooks; consumed by
    /// `analysis/stored_value_invariants.rs`.
    pub data_inv: std::collections::BTreeSet<String>,
    /// Per-module option gates from `def <Module>.module_options` hook
    /// declarations (`<stem> → {quoted option strings on the decl line}`).
    /// Currently consumed for the per-package `world_mode` gate
    /// (`analysis/world_threading.rs`); the unified-backend design (§8) adds
    /// `honest_df_aborts` / `irreducible_defs` / … on the same surface.
    pub module_options: std::collections::BTreeMap<String, std::collections::BTreeSet<String>>,
}

impl Program {
    pub fn finalize(&mut self) {
        self.finalize_with_mode(BuildMode::Spec)
    }

    /// Test-mode finalization. The abort derivation is identical to the Spec
    /// pipeline (`.aborts` companions are always `Option MoveAbort`); the
    /// only difference is the body shape produced by `build_inner` in
    /// `BuildMode::Test` (preserves `#[test]` items and inline
    /// `IRNode::Abort`s), which is why the Test path routes here.
    pub fn finalize_for_test(&mut self) {
        self.for_test = true;
        self.finalize_with_mode(BuildMode::Spec);
    }

    pub fn finalize_with_mode(&mut self, mode: BuildMode) {
        order_by_dependencies(self);

        // World-mode (unified-backend design Phase 1): the per-package
        // `world_mode` gate selects the World lowering (Phase A here, the
        // interprocedural Phase B in ghost_threading's slot below) and skips
        // BOTH dynamic_field_rewriting phases — Phase A produces the same
        // MutableBorrow bracketing shape for `thread_mutables` that
        // `rewrite_df_borrow_mut_pre_threading` produces today, with
        // `__world` as the reconstructed parent. Gate off ⇒ both calls
        // return on their first line and the slot-mode passes run unchanged
        // (byte-identical output).
        let world_mode = crate::analysis::world_threading::world_mode_enabled(self);
        if world_mode {
            crate::analysis::world_threading::lower_state_ops_pre_threading(self);
        } else {
            crate::analysis::dynamic_field_rewriting::rewrite_df_borrow_mut_pre_threading(self);
        }

        crate::analysis::mutable_threading::thread_mutables(self);

        if !world_mode {
            crate::analysis::dynamic_field_rewriting::rewrite_dynamic_fields(self);
        }

        // Fix `Let { pattern: [], value: WriteRef { reference: Var(X) } }`
        // by binding the WriteRef to X. Lean's `Mutable.set` is pure;
        // discarding its result via `let _ := Mutable.set X v` silently
        // loses the write. Run before phi-lift so phi detection sees
        // a real `Let { pattern: [X] }` rebind to thread X through
        // surrounding If / Match.
        for func_id in self.functions.iter_ids().collect::<Vec<_>>() {
            let body = std::mem::take(&mut self.functions.get_mut(func_id).body);
            self.functions.get_mut(func_id).body =
                crate::analysis::fix_writeref_empty_patterns(body);
        }

        // Propagate WriteBack-to-snapshot-temp updates upstream to the
        // owning struct. Cases like `let $t5 := self.contents; ...
        // WriteBack { child: __mut_ret, parent: $t5 }; ... use self`
        // would otherwise leave `self` unchanged because the IR
        // translator emits `WriteBackEdge::Direct` rather than
        // `WriteBackEdge::Field` for ordinary struct fields. The pass
        // appends `let self := { self with contents := __mut_ret }`
        // after the WriteBack so the mutation reaches `self`.
        for func_id in self.functions.iter_ids().collect::<Vec<_>>() {
            let body = std::mem::take(&mut self.functions.get_mut(func_id).body);
            self.functions.get_mut(func_id).body =
                crate::analysis::propagate_field_snapshot_writebacks(body);
        }

        // Post-threading phi lift: mutable_threading rewrites WriteBack
        // ops into `let X := <new value>` shadow self-updates inside
        // `If` / `Match` branches. When upstream phi detection had
        // wrapped the control-flow node in `let _ := <If> ; <body>` at
        // translation time (because no var was rebound back then), the
        // post-threading rebinding is now lexically scoped to the branch
        // and never escapes — `<body>` continues to see the parameter
        // value, silently dropping the mutation. This lifts re-bindings
        // referenced by `<body>` into a real phi pattern.
        for func_id in self.functions.iter_ids().collect::<Vec<_>>() {
            let body = std::mem::take(&mut self.functions.get_mut(func_id).body);
            self.functions.get_mut(func_id).body = crate::analysis::lift_post_threading_phis(body);
        }

        // Peephole: coalesce the shadow-update + self-noop UpdateField
        // pattern emitted by mutable_threading + the IR translator. Runs
        // in BOTH Spec and Test modes because the bug is structural — the
        // self-noop on `Y` swallows an update that should have landed on
        // `Y` from a shadow alias `X`. Spec / Test renderers both consume
        // the corrected IR.
        for func_id in self.functions.iter_ids().collect::<Vec<_>>() {
            let body = std::mem::take(&mut self.functions.get_mut(func_id).body);
            self.functions.get_mut(func_id).body =
                crate::analysis::coalesce_shadow_self_noop_updates(body);
        }

        // Model the stateful `sui::tx_context` VM natives (`fresh_id` /
        // `native_sender`) from the threaded `TxContext` struct fields so
        // world-mode object identity is faithful: distinct fresh uids
        // (`derive_id ctx.tx_hash ctx.ids_created`, incrementing `ids_created`)
        // and a real `sender` (`self.sender`). Runs after `thread_mutables`
        // (so `fresh_object_address` already returns `(address, TxContext)`)
        // and before `dead_param_elimination` (so `sender`'s `self` survives).
        // No-op off world_mode.
        if world_mode {
            crate::analysis::tx_context_natives::model_tx_context_natives(self);
        }

        // Ghost threading (spec-global markers): thread each declared
        // `(K, V)` ghost marker as a `__ghost_<K>` value param + trailing
        // return slot through the transitive caller cone of the seeded
        // ghost-writing natives, then lower `ghost::global/set/borrow_mut`
        // onto the threaded vars. Runs AFTER mutable threading (so the
        // shapes it appends extend the already-augmented return tuples and
        // spec preambles later pick up the rebinds) and BEFORE the aborts
        // derivation + spec extraction below (so `.aborts` bodies derived
        // from threaded impl bodies see consistent call shapes, and
        // extracted `.ensures` carry the ghost params + rebinds). No-op
        // when `ghost_native_seed` is empty (inertness gate).
        // World-mode transfer-ghost retirement: lower `ghost::global` reads
        // on the transfer markers onto the World transfer-marker slots BEFORE
        // ghost threading, so world-mode user spec faces carry no `__ghost_*`
        // binders (the ghost cone shrinks to the transfer modules themselves).
        // No-op unless world_mode (inertness gate).
        crate::analysis::world_threading::lower_transfer_ghosts(self);

        crate::analysis::ghost_threading::thread_ghosts(self);

        // World threading Phase B (unified-backend design §4.1): the
        // interprocedural half of world-mode. Runs in the same slot family
        // as ghost threading — AFTER mutable threading + its fixups (the
        // call shapes it appends extend the mut-augmented tuples) and
        // BEFORE the aborts derivation + spec extraction below (so callee
        // `.aborts` faces and extracted spec companions carry the `__world`
        // param). Spec-only ghost slots, when both mechanisms are active,
        // are ordered before `__world` by pass order (ghost_threading runs
        // first); the doc's world-first ordering applies once transfer
        // ghost seeding is retired in world-mode packages. No-op unless
        // `world_mode` seeded `Program::world_functions` (inertness gate).
        crate::analysis::world_threading::thread_world(self);

        // The next four passes are Spec-only: they shape `.aborts`
        // companions, extract requires/ensures specs out of bodies, and
        // generate cross-face type conversions — none of which the Test
        // face consumes. Skipping them also keeps `IRNode::Abort` nodes
        // inline in bodies, which the Test face depends on.
        if matches!(mode, BuildMode::Spec) {
            // Option-shape `.aborts`: a single pass derives the whole abort
            // condition. `inject_arithmetic_aborts` walks each function's
            // implementation body once, emitting arithmetic aborts, explicit
            // `assert!` aborts, AND a callee-abort check at every `Call`.
            //
            // Pre-mark IR functions shadowed by hand-written natives as
            // `is_native = true` so the walk treats them like the native
            // `.aborts` (authored as `Option MoveAbort`) they render to.
            crate::analysis::mark_native_shadowed_auto(self);
            crate::analysis::inject_arithmetic_aborts(self);

            // Re-sort functions: the compose pass introduces new .aborts → .aborts
            // dependencies that may require different ordering.
            order_by_dependencies(self);

            // Extract requires/ensures specs from function bodies.
            // This runs AFTER mutable threading so that spec preambles include
            // mutation rebindings (e.g. `let table := __mut_ret_0`).
            crate::analysis::extract_all_specs(self);

            // Give `&mut` post-call rebinds in `.ensures` a distinct `_post`
            // name instead of shadowing the parameter, so a pre-state snapshot
            // can never be inlined into a post-state read by `optimize_all`.
            crate::analysis::distinguish_param_rebinds_in_ensures(self);

            crate::analysis::generate_spec_type_conversions(self);
        }

        // Quantifier lifting is performed upstream by
        // `QuantifierIteratorAnalysisProcessor` (wired into `build_lean_pipeline`),
        // which converts begin_*_lambda / end_*_lambda call patterns into
        // `Operation::Quantifier` bytecode that `translate_quantifier` consumes.

        // In Prop-returning functions (.aborts, .ensures), wrap Bool-typed tail
        // expressions with ToProp (rendered as `expr = true`).  Without this,
        // calls to Bool-returning functions (e.g. `has_rule`) are left as Bool
        // in a Prop context, which Lean cannot unify.
        {
            let prop_func_ids: Vec<usize> = self
                .functions
                .iter()
                .filter(|(_, f)| !f.is_native && f.signature.return_type == Type::Prop)
                .map(|(id, _)| id)
                .collect();
            for func_id in prop_func_ids {
                let func = self.functions.get(&func_id);
                let new_body = {
                    let mut registry = func.param_registry(self);
                    let body = func.body.clone();
                    crate::analysis::lift_bool_tails_to_prop(body, &mut registry)
                };
                self.functions.get_mut(func_id).body = new_body;
            }
        }

        collect_imports(self);
        self.optimize_all(mode);

        // Fix `wrap_tail`'s discarded-reconstruct anti-pattern
        // (`let P := (let () := WriteBack{parent:P}; P)`), which drops the
        // receiver reconstruction when `self` is mutated through a
        // mutref-returning helper's result (sui-system
        // `validator_set::request_add_stake`: the staked validator never lands
        // back in `self.active_validators`). Runs after `optimize_all`, which
        // is what materializes the wrapped shape.
        //
        // Gated off in world-mode: there `thread_world` (which ran earlier)
        // has already threaded a `__world` out of the tail, and a receiver
        // borrowed through a heterogeneous phi (`get_candidate_or_active_
        // validator_mut`: candidate = World-df-backed, active = value-backed)
        // has a WORLD-PAIRED `Mutable.apply` (state `S × World`). Rebinding
        // `let self := Mutable.apply child` there mistypes `self` as the pair.
        // Keeping the world-safe discarded form is the documented M1
        // heterogeneous-phi cut; the World-store transfer/take path (what the
        // inventory tests need) is unaffected.
        if !world_mode {
            for func_id in self.functions.iter_ids().collect::<Vec<_>>() {
                let body = std::mem::take(&mut self.functions.get_mut(func_id).body);
                self.functions.get_mut(func_id).body =
                    crate::analysis::fix_discarded_reconstruct_writebacks(body);
            }
        }

        // A pure quantifier never aborts, so replace `forall!`/`exists!` in
        // `.aborts` companions with `false` — keeps abort bodies computable Bool
        // and out of the Prop world.
        crate::analysis::strip_quantifiers_in_aborts(self);

        // A `bool` spec helper whose body is logical (a `forall!`/`exists!` or a
        // `&&`/`||`/`if` combination of one — now in `BinOp::And/Or` form after
        // optimize_all's boolean-if conversion) is really a `Prop` predicate.
        // Promote it so the quantifier sits in Prop position and renders as a
        // native `∀`/`∃` (no opaque fallback). No-op without quantifiers.
        let promoted_to_prop = crate::analysis::infer_prop_returns(self);

        // Re-lift Bool tails to Prop for the just-promoted functions, so their
        // Bool sub-terms get `= true` coercion.
        {
            for func_id in promoted_to_prop {
                let new_body = {
                    let func = self.functions.get(&func_id);
                    let mut registry = func.param_registry(self);
                    let body = func.body.clone();
                    crate::analysis::lift_bool_tails_to_prop(body, &mut registry)
                };
                self.functions.get_mut(func_id).body = new_body;
            }
        }

        // Re-sort: optimize_all may have removed Calls that previously formed
        // SCCs (e.g., a recursive call that constant-folded to a non-recursive
        // tail). Stale mutual_group_id values would cause the renderer to wrap
        // unrelated functions in the same `mutual` block, breaking forward
        // references between actual SCCs.
        order_by_dependencies(self);

        // Remove unused function parameters and update all call sites.
        // Run in both Spec and Test modes so synthetic loop helpers
        // (`<f>.while_*`, `<f>.after_*`) end up with identical signatures
        // across IR builds. The Test driver imports those helpers from
        // the Spec-rendered file but generates its own call sites from
        // a fresh Test-mode IR — if Spec eliminates dead params and Test
        // doesn't, the driver passes too many args to the rendered def.
        // Synthetic helpers don't carry abort conditions in their bodies
        // (those live in `.aborts` companions), so the elimination
        // converges to the same set of params in both modes; project
        // functions get re-inlined as `_test` companions in Test mode,
        // so any per-mode signature drift is internal to each driver.
        crate::analysis::dead_param_elimination::eliminate_dead_params(self);

        // Final re-sort after dead-param elimination, which may also have
        // removed uses (and thus changed the dep graph).
        order_by_dependencies(self);

        // Wrap bare `UpdateField` branch terminals in `WriteRef` when the
        // enclosing `Let([X], If, body)` binds X (a Mutable). Test-mode
        // `.aborts` companions commonly leave this exact shape after
        // inject_arithmetic_aborts (the abort derivation strips the
        // WriteRef around a trailing Mutable.set, leaving the inner
        // UpdateField as the branch terminal). Without wrapping, branches
        // return bare struct values, breaking unification with Mutable
        // and stripping `Mutable.val` from every later field access on X.
        //
        // Runs LAST — after optimize_all (which can inline a let-bound
        // UpdateField into the branch's terminal position via
        // temp_inlining, swapping `Var($tmp)` for the actual UpdateField)
        // and after dead_param_elimination — so the wrap sees the final
        // IR shape that the renderer will consume.
        for func_id in self.functions.iter_ids().collect::<Vec<_>>() {
            let body = std::mem::take(&mut self.functions.get_mut(func_id).body);
            let new_body = {
                let func = self.functions.get(&func_id);
                let mut registry = func.param_registry(self);
                crate::analysis::wrap_mutable_if_branch_terminals(body, &mut registry)
            };
            self.functions.get_mut(func_id).body = new_body;
        }

        // Re-run Inhabited elimination on `.aborts` bodies. A discarded value
        // computation that bottoms out in the module's nullary `default()`
        // function (rendered as Lean's `default` / `Inhabited.default`) survives
        // into the nested match-on-aborts shape — `let tmp := default; Option.none`
        // or `let tmp := (if c then <typed> else default); Option.none` — where the
        // bound temp is unused, so its type is unconstrained and Lean gets stuck
        // synthesizing `Inhabited ?m`. The `default` here is a `Call` to the
        // empty-tuple `default` function, NOT an `IRNode::Inhabited`, so first
        // rewrite those calls to `Inhabited`, then flatten any let-value that now
        // contains one to `false` (giving the discarded binding a concrete type).
        // Runs after `compose_callee_aborts` / `optimize_all`, which materialize
        // this shape. Idempotent on bodies with no such default.
        let default_fn_ids: std::collections::HashSet<usize> = self
            .functions
            .iter()
            .filter(|(_, f)| {
                f.name == "default" && matches!(&f.body, crate::IRNode::Tuple(v) if v.is_empty())
            })
            .map(|(id, _)| id)
            .collect();
        for func_id in self.functions.iter_ids().collect::<Vec<_>>() {
            if !self.functions.get(&func_id).name.ends_with(".aborts") {
                continue;
            }
            let body = std::mem::take(&mut self.functions.get_mut(func_id).body);
            let body = body.map(&mut |n| match n {
                crate::IRNode::Call { function, .. } if default_fn_ids.contains(&function) => {
                    crate::IRNode::Inhabited
                }
                other => other,
            });
            self.functions.get_mut(func_id).body =
                crate::analysis::replace_inhabited_let_values(body);
        }

        // Loop-invariant entry cascade: thread the precondition hypothesis onto
        // loop_inv target impls + their spec references so the entry call can be
        // discharged (vs `sorry`d). Runs after dead-param elimination so the
        // injected proof params reflect the final value-param list of each
        // loop helper / impl.
        crate::analysis::thread_loop_inv_entry(self);

        // Callee-`requires` entry cascade: thread a precondition hypothesis onto
        // plain value defs / `.aborts` (e.g. the `Validator.pool_token_exchange_rate_at_epoch`
        // wrapper, and `frozen_after_deactivation_spec.aborts`) that call a
        // loop-inv entry impl carrying a `requires`, so the call site forwards a
        // real `hpre` instead of the `<G>_requires` sorry macro. Runs after the
        // loop-inv entry cascade (which populates `loop_inv_entry_impls`, the set
        // this pass keys off) and before `materialize_proof_params`.
        crate::analysis::thread_callee_requires_entry(self);

        // Callee-`requires` PRECOND cascade: for the cases the param-forwarding
        // pass above could not thread — `.while_`/`.after_` loop helpers and
        // plain defs / `.aborts` whose call into a `callee_requires_impls` callee
        // passes a `requires`-slot arg over loop-body temps / rebound locals — a
        // client-declared `<F-base>.precond` is threaded onto F (and propagated up
        // its caller chain to the spec boundary) so the call site renders the
        // client `(by <G>_requires)` macro instead of bare `sorry`. Inert unless
        // the client declared a `.precond` (scanned into `lean_termination_decls`)
        // for such an F. Runs right after the param-forwarding pass (so it sees
        // the final `callee_requires_impls` set) and before
        // `materialize_proof_params`.
        crate::analysis::thread_callee_requires_precond(self);

        // Nested-loop termination: detect the three-member `while_0`/`while_1`/
        // `while_1.after` shape and thread the outer guard `i < n` onto the
        // inner members so their lexicographic decreasing proof closes. Runs
        // after the entry cascade (so it never feeds synthetic loops into the
        // hpre threading) and before `materialize_proof_params` (which drains
        // the `hinv` recordings into signatures).
        crate::analysis::thread_nested_loop_termination(self);

        // Generic loop-termination threading driven by the client's Lean
        // `Termination/<module>.lean` declarations (`def <name>.loop_hyp` /
        // `def <name>.precond`, scanned into `lean_termination_decls`). Threads
        // `hinv` onto a declared self-recursive helper and propagates the entry
        // precond to its external callers — the name-free replacement for the old
        // hard-coded `max_heapify` / `derive_gas` passes. Same placement
        // contract: after the entry cascade, before materialize_proof_params.
        crate::analysis::thread_lean_terminations(self);

        // Stored-value data invariants: for each client `def <stem>.data_inv`
        // declaration, thread a membership-conditioned container hypothesis
        // (`hdinv : TypedMap.all K V P (path.dynamic_fields)`) onto the spec
        // functions whose impl closure touches the declared slot, and record
        // the `_data_inv` preservation goals the Correctness renderer emits.
        // Inert (byte-identical output) without declarations. Runs before
        // `materialize_proof_params`, which drains the recordings.
        crate::analysis::thread_stored_value_invariants(self);

        // Materialize proof parameters into signatures. MUST be the final step:
        // it reads the now-final value-param lists and the entry-cascade
        // recordings, then writes each function's `signature.proof_params` — the
        // single source of truth that the validator (scope + arity) and the
        // renderer both consume. Nothing after this may reorder parameters.
        self.materialize_proof_params();

        // Side-car decomposition of oversized `.aborts` bodies into
        // `<fn>.aborts.seg_k` chains (bodies untouched; proofs opt in via the
        // rendered `.decompose` rfl lemma). Runs after
        // `materialize_proof_params` so copied `hpre` binders are final.
        // Under the per-package `contract_aborts` module_options gate
        // (unified-backend design §5.1/§5.2, Phase 2), obligation bundles
        // additionally become the default interface for small `.aborts`:
        // ≥ 2-leaf bundles fire below MIN_TOTAL, and leaf-free (total)
        // bundles render their `aborts_none_of` tagged `@[contract]` for the
        // callee-contract registry. Inert without the gate.
        crate::analysis::decompose_aborts(self);

        // Ensures bundles (unified-backend design §5.1, Phase 3.1): the same
        // machinery generalized to `.ensures` companions, behind the
        // per-package `ensures_bundles` module_options gate. First-line
        // inertness return when the gate is off.
        crate::analysis::decompose_ensures(self);

        // Equation/projection lemma sets for the per-MODULE `irreducible_defs`
        // gate (§5.3, Phase 3.2). Pure recording pass — bodies untouched; the
        // renderer emits the lemmas + `attribute [irreducible]` lines. Inert
        // when no module opts in.
        crate::analysis::compute_equation_lemmas(self);

        // HasCode-requirement analysis (Phase 5, generic state ops): record
        // which type params of each function flow into World typed-view ops;
        // the renderer emits `[HasCode TyCode <tp>]` binders for them. Runs
        // after every derived face exists and BEFORE frame lemmas (which
        // admit generic candidates only when fully HasCode-covered). Inert
        // off world-mode.
        crate::analysis::world_threading::compute_hascode_params(self);
        // BagU analog: which type params flow into `bag`/`object_bag` ops; the
        // renderer emits `[HasCode BagU <tp>]` binders for them. Separate
        // universe from the World/TyCode threading above.
        crate::analysis::world_threading::compute_bagu_params(self);

        // Frame lemmas (§5.4, Phase 4): footprints + generator-built FrameDf
        // proof trees for world-mode value faces. Pure recording pass over
        // FINAL bodies (value faces are untouched by the decompose passes
        // above). First-line inertness return unless `world_mode` seeded
        // `Program::world_functions`. Skipped in test mode — the drivers only
        // evaluate `.aborts`, never the frame proofs.
        if !self.for_test {
            crate::analysis::compute_frame_lemmas(self);
        }

        // Loop-body extraction: hoist a heavy per-iteration body out of a
        // self-recursive `<f>.while_N` helper into a sibling non-recursive
        // `<f>.while_N.step` def. Lean's well-founded-recursion elaboration
        // (fixpoint + equational-lemma generation) scales with the recursive
        // body's term size, so a heavy loop body hangs type-check AND `lean -c`
        // codegen for minutes/GB (sui-system `Voting_power_tests`). Shrinking
        // the WF body to a guard + one `step` call + the recursive call fixes
        // it while keeping a real (sorry-terminated but unfoldable) `def`.
        // Semantics-preserving; only touches value-form non-generic sorry-
        // fallback loops of the canonical shape (see the pass docstring).
        //
        // Runs LAST — after every body-shaping pass — so it reads each loop's
        // FINAL body (e.g. the writeback rebind `let ctx := __mut_ret_N` that
        // later passes materialize is present, so the threaded value is captured
        // as a live-out of the step helper). The new `.step` helpers are plain
        // value defs needing no proof params / lemmas; the renderer's per-module
        // topological sort places each ahead of its loop's mutual block.
        // Inline calls to abort-only `<while>.after` loop-continuation helpers.
        // Such a helper's body is a bare `abort` (the Move loop falls through to
        // `abort`), so the demotion in `mutable_threading` strips the Mutable
        // wrapper off its return type while its `<while>` sibling keeps it
        // (its found-branch has a real `Mutable.compose`) — leaving the sibling's
        // tail `let r := <while>.after …; (r.1, …)` expecting `Mutable` from a
        // `.after` typed plain ("Application type mismatch", cetus
        // `borrow_mut_rewarder`). Since the call always aborts, replace it (and
        // the now-unreachable destructure that follows) with an inline `Abort`,
        // which Lean unifies with the found-branch's inferred `Mutable` type — no
        // annotation, no unreliable state placeholder. Runs before
        // `extract_loop_bodies` so the loop's final body is the inlined form.
        crate::analysis::inline_abort_only_after_calls(self);

        // Re-run the pair-writeback fixup over FINAL bodies (world-mode only;
        // inert when `pair_mut_fns` is empty). The threading-time run rewrites
        // value-nested pair writebacks, but later optimize passes can revert
        // those, leaving the discarded `let _ := Mutable.apply m; let self :=
        // self` shape that drops the mutated pair state (sui-system
        // `Validator_set.request_add_stake` losing candidate stake). Idempotent.
        crate::analysis::world_threading::run_pair_writeback_fixup(self);

        crate::analysis::extract_loop_bodies(self);

        // Enforce the no-opaque-fallback invariant: every `forall!`/`exists!`
        // must have ended up in a `Prop` position. A quantifier still stuck in
        // a `Bool`-returning function is a hard error (panics with guidance).
        crate::analysis::validate_sorts(self);
    }

    /// Drain the finalize-internal proof-parameter recording tables
    /// ([`Program::loop_inv_hyps`], [`Program::fn_proof_params`]) into each
    /// function's [`FunctionSignature::proof_params`]. After this runs, the
    /// signature is the single authoritative description of a function's binders
    /// — value parameters followed by proof parameters — so the validator, the
    /// arity check, the function renderer, and goal-statement rendering all read
    /// one place and cannot drift. Runs as the last finalize step (after
    /// dead-param elimination and the entry cascade) so a loop helper's value
    /// params are final and the `hinv` hook application covers exactly the
    /// params that survive.
    fn materialize_proof_params(&mut self) {
        use crate::data::functions::{ProofParam, ProofParamType};

        // `hinv` — loop-invariant hypothesis, one per loop helper. Its type is
        // the hook applied to the helper's type + value params; that application
        // is deferred (`LoopInvHook`) to the renderer, which owns identifier
        // escaping and sees the final signature.
        let mut hinv: Vec<(FunctionID, LoopInvHyp)> = self
            .loop_inv_hyps
            .iter()
            .map(|(id, h)| (*id, h.clone()))
            .collect();
        hinv.sort_by_key(|(id, _)| *id);
        for (id, hyp) in hinv {
            self.functions
                .get_mut(id)
                .signature
                .proof_params
                .push(ProofParam {
                    name: hyp.hyp_param,
                    param_type: ProofParamType::LoopInvHook(hyp.hook_name),
                });
        }

        // `hpre` — precondition hypothesis threaded by the entry cascade. Its
        // prop text is already a complete Lean term, so it is stored verbatim.
        let mut hpre: Vec<(FunctionID, Vec<(String, String)>)> = self
            .fn_proof_params
            .iter()
            .map(|(id, v)| (*id, v.clone()))
            .collect();
        hpre.sort_by_key(|(id, _)| *id);
        for (id, params) in hpre {
            for (name, prop) in params {
                self.functions
                    .get_mut(id)
                    .signature
                    .proof_params
                    .push(ProofParam {
                        name,
                        param_type: ProofParamType::Verbatim(prop),
                    });
            }
        }

        // `hdinv` — stored-value data-invariant hypotheses. Appended after any
        // `hpre` so binder order is stable (`hpre` first, `hdinv_*` after).
        let mut hdinv: Vec<(FunctionID, Vec<ProofParam>)> = self
            .fn_data_inv_params
            .iter()
            .map(|(id, v)| (*id, v.clone()))
            .collect();
        hdinv.sort_by_key(|(id, _)| *id);
        for (id, params) in hdinv {
            self.functions
                .get_mut(id)
                .signature
                .proof_params
                .extend(params);
        }
    }

    fn optimize_all(&mut self, mode: BuildMode) {
        // Test mode skips optimization entirely. The Spec passes
        // (constant folding through stripped temps, dead-code removal
        // tuned for `()`-returning bodies, etc.) collapse If/Abort
        // patterns the Test face needs to render. The post-translation
        // IR is already clean enough for the monadic Test renderer.
        if matches!(mode, BuildMode::Test) {
            return;
        }
        let func_ids: Vec<usize> = self
            .functions
            .iter()
            .filter(|(_, f)| !f.is_native)
            .map(|(id, _)| id)
            .collect();
        for func_id in func_ids {
            let new_body = {
                let func = self.functions.get(&func_id);
                let mut registry = func.param_registry(self);
                let mut body = func.body.clone();
                if matches!(func.signature.return_type, Type::Bool) {
                    body = crate::analysis::normalize_unit_branches(body);
                }
                // `.aborts` bodies are Bool expressions proved (never computed); inline
                // heavy multi-use temps so the kernel-cheap `conv`-localized proof works.
                // See CLAUDE.md "Kernel deep-recursion on heavy `BoundedNat` obligations".
                let aborts = func.name.contains(".aborts");
                crate::analysis::optimize_with(body, &mut registry, aborts, Some(func_id))
            };
            self.functions.get_mut(func_id).body = new_body;
        }

        self.fold_constant_calls();
    }

    fn fold_constant_calls(&mut self) {
        for (_, func) in self.functions.iter_mut() {
            func.body = fold_constants(std::mem::take(&mut func.body));
            func.body = crate::analysis::logical_simplify(std::mem::take(&mut func.body));
        }
    }
}

#[derive(Debug, Clone)]
pub struct Module {
    pub name: String,
    pub package_name: String,
    pub required_imports: Vec<ModuleID>,
    /// If true, this module is provided by the prelude or another static source
    /// and should not be rendered by the backend.
    pub is_native: bool,
}
