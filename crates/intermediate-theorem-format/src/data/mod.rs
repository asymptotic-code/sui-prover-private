// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

use indexmap::IndexMap;
use move_model::model::{DatatypeId, FunId, ModuleId, QualifiedId};
use std::borrow::Borrow;
use std::collections::BTreeMap;

use crate::analysis::{collect_imports, fold_constants, order_by_dependencies};
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
    /// Bare spec-function names (e.g. `abs_spec`) marked
    /// `#[spec(prove, run_on="boogie")]`: trusted to be proven by the Boogie
    /// backend. The renderer emits their correctness obligations as a trusted
    /// `axiom` instead of `theorem ... := by sorry`, so a hybrid Boogie+Lean
    /// pipeline only hands the remainder to the Lean proof agent. Populated by
    /// the backend from `FunctionTargetsHolder::is_boogie_proven`.
    pub boogie_proven_specs: std::collections::HashSet<String>,
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
        self.finalize_with_mode(BuildMode::Spec);
    }

    pub fn finalize_with_mode(&mut self, mode: BuildMode) {
        order_by_dependencies(self);

        crate::analysis::dynamic_field_rewriting::rewrite_df_borrow_mut_pre_threading(self);

        crate::analysis::mutable_threading::thread_mutables(self);

        crate::analysis::dynamic_field_rewriting::rewrite_dynamic_fields(self);

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

        // Loop-invariant entry cascade: thread the precondition hypothesis onto
        // loop_inv target impls + their spec references so the entry call can be
        // discharged (vs `sorry`d). Runs after dead-param elimination so the
        // injected proof params reflect the final value-param list of each
        // loop helper / impl.
        crate::analysis::thread_loop_inv_entry(self);

        // Materialize proof parameters into signatures. MUST be the final step:
        // it reads the now-final value-param lists and the entry-cascade
        // recordings, then writes each function's `signature.proof_params` — the
        // single source of truth that the validator (scope + arity) and the
        // renderer both consume. Nothing after this may reorder parameters.
        self.materialize_proof_params();

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
