// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Renders complete Program to Lean files.
//! Dumb renderer — one file per module, each function rendered in order.

use super::function_renderer::{
    must_skip_function, render_aborts_bundles, render_decompose_theorems, render_ensures_bundles,
    render_equation_lemmas, render_frame_lemmas, render_function,
};
use super::lean_writer::LeanWriter;
use super::struct_renderer::render_struct;
use crate::{copy_if_changed, escape, write_if_changed, WrittenFiles};
use intermediate_theorem_format::{ModuleID, Program, StructID, Type};
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet, VecDeque};
use std::fs;
use std::path::Path;

/// Compute strongly connected components of the module dependency graph using
/// Tarjan's algorithm. Returns a list of SCCs; each SCC is a Vec of module IDs.
/// Single-module SCCs (no cycle) are included as length-1 vectors.
fn compute_module_sccs(
    module_ids: &[ModuleID],
    adjacency: &HashMap<ModuleID, Vec<ModuleID>>,
) -> Vec<Vec<ModuleID>> {
    struct TarjanState {
        index_counter: usize,
        stack: Vec<ModuleID>,
        on_stack: HashSet<ModuleID>,
        index: HashMap<ModuleID, usize>,
        lowlink: HashMap<ModuleID, usize>,
        sccs: Vec<Vec<ModuleID>>,
    }

    fn strongconnect(v: ModuleID, adj: &HashMap<ModuleID, Vec<ModuleID>>, state: &mut TarjanState) {
        state.index.insert(v, state.index_counter);
        state.lowlink.insert(v, state.index_counter);
        state.index_counter += 1;
        state.stack.push(v);
        state.on_stack.insert(v);

        if let Some(neighbors) = adj.get(&v) {
            for &w in neighbors {
                if !state.index.contains_key(&w) {
                    strongconnect(w, adj, state);
                    let w_low = state.lowlink[&w];
                    let v_low = state.lowlink[&v];
                    state.lowlink.insert(v, v_low.min(w_low));
                } else if state.on_stack.contains(&w) {
                    let w_idx = state.index[&w];
                    let v_low = state.lowlink[&v];
                    state.lowlink.insert(v, v_low.min(w_idx));
                }
            }
        }

        if state.lowlink[&v] == state.index[&v] {
            let mut scc = Vec::new();
            loop {
                let w = state.stack.pop().expect("stack underflow in Tarjan");
                state.on_stack.remove(&w);
                scc.push(w);
                if w == v {
                    break;
                }
            }
            state.sccs.push(scc);
        }
    }

    let mut state = TarjanState {
        index_counter: 0,
        stack: Vec::new(),
        on_stack: HashSet::new(),
        index: HashMap::new(),
        lowlink: HashMap::new(),
        sccs: Vec::new(),
    };

    for &mid in module_ids {
        if !state.index.contains_key(&mid) {
            strongconnect(mid, adjacency, &mut state);
        }
    }

    state.sccs
}

/// Topologically sort functions so dependencies come before dependents.
/// Uses Kahn's algorithm. Functions not in the module are treated as external.
fn topological_sort_functions(func_ids: &[usize], program: &Program) -> Vec<usize> {
    let func_set: HashSet<usize> = func_ids.iter().copied().collect();

    // Build adjacency list: func_id -> functions it calls (within module)
    let mut deps: HashMap<usize, Vec<usize>> = HashMap::new();
    let mut in_degree: HashMap<usize, usize> = HashMap::new();

    for &fid in func_ids {
        deps.entry(fid).or_default();
        in_degree.entry(fid).or_insert(0);
    }

    for &fid in func_ids {
        let func = program.functions.get(&fid);
        for called in func.body.calls() {
            if func_set.contains(&called) && called != fid {
                deps.entry(called).or_default().push(fid);
                *in_degree.entry(fid).or_insert(0) += 1;
            }
        }
    }

    // Kahn's algorithm — use sorted queues for deterministic output
    let mut initial: Vec<usize> = in_degree
        .iter()
        .filter(|(_, &deg)| deg == 0)
        .map(|(&id, _)| id)
        .collect();
    initial.sort();
    let mut queue: VecDeque<usize> = initial.into_iter().collect();

    let mut result = Vec::new();

    while let Some(fid) = queue.pop_front() {
        result.push(fid);
        if let Some(dependents) = deps.get(&fid) {
            let mut newly_free = Vec::new();
            for &dep in dependents {
                let degree = in_degree.get_mut(&dep).unwrap();
                *degree -= 1;
                if *degree == 0 {
                    newly_free.push(dep);
                }
            }
            newly_free.sort();
            for dep in newly_free {
                queue.push_back(dep);
            }
        }
    }

    // If there are cycles (mutual recursion), add remaining functions in original order
    if result.len() < func_ids.len() {
        for &fid in func_ids {
            if !result.contains(&fid) {
                result.push(fid);
            }
        }
    }

    result
}

/// Get the Lean namespace for a module, using override if one exists.
/// Returns the *full* namespace including the namespace-vs-struct collision
/// suffix (`_M`) when present. Use `get_namespace_file_stem` for filenames /
/// imports / natives lookup so the on-disk layout stays decoupled from the
/// collision-avoidance suffix.
pub fn get_namespace(program: &Program, module_id: usize) -> String {
    if let Some(ns) = program.namespace_overrides.get(&module_id) {
        ns.clone()
    } else {
        let module = program.modules.get(module_id);
        escape::module_name_to_namespace(&module.name)
    }
}

/// File stem to use for a module's generated `.lean` file (and for imports
/// pointing at it). This intentionally strips the `_M` suffix introduced by
/// the namespace-vs-struct collision rename: that suffix only exists to keep
/// Lean from confusing `Ns.field` with `Ns.S.field`, it doesn't need to leak
/// into filenames or import paths. Cross-package overrides (e.g.
/// `Pyth_Price_info`) DO leak into filenames, since multiple packages would
/// otherwise produce colliding files.
/// Resolve the `import` line that brings the file DEFINING `struct_id` into
/// scope, for use from a struct-bearing file (`_types_skeleton` / `_types` /
/// main). This is the single source of truth for cross-file struct-dependency
/// imports: every struct reference imports the precise file that defines it,
/// never the dependency's whole module. That keeps the type-universe import
/// layering acyclic — in particular a bag-free skeleton (which, by the
/// transitive bag-taint invariant in `collect_bag_containing_struct_ids`, only
/// ever references bag-free structs) resolves its deps to other skeletons /
/// Whether a user hook file exists for `stem`: the legacy
/// `Termination/<stem>.lean` path or the unified `Hooks/<stem>.lean` surface
/// (unified-backend design §8). Either forces the `_types` split and the
/// matching import on the module file. Returns `(termination, hooks)`.
fn user_hook_files(termination_dir: &Path, stem: &str) -> (bool, bool) {
    let term = termination_dir.join(format!("{}.lean", stem)).exists();
    let hooks = termination_dir
        .parent()
        .map(|p| p.join("Hooks").join(format!("{}.lean", stem)).exists())
        .unwrap_or(false);
    (term, hooks)
}

/// non-bag type files and never to a `TyCodeInterp`-importing module file.
/// Returns `None` when the struct is defined in the current file (same stem).
#[allow(clippy::too_many_arguments)]
fn struct_defining_import(
    program: &Program,
    struct_id: StructID,
    current_stem: &str,
    termination_dir: &Path,
    module_to_file: &HashMap<ModuleID, (String, String)>,
    bag_ids: &HashSet<StructID>,
    bag_stems: &HashSet<String>,
    tci_stems: &HashSet<String>,
    native_struct_keys: &HashSet<(ModuleID, String)>,
) -> Option<String> {
    if !program.structs.has(struct_id) {
        return None;
    }
    let mid = program.structs.get(&struct_id).module_id;
    if !program.modules.has(mid) {
        return None;
    }
    let module = program.modules.get(&mid);
    let pkg = if module.package_name.is_empty() {
        "Lean".to_string()
    } else {
        module.package_name.clone()
    };
    // Native modules provide their structs from the hand-written `*Natives` file.
    if module.is_native {
        let stem = get_namespace_file_stem(program, mid);
        return Some(format!("import {}.{}Natives", pkg, stem));
    }
    // A NATIVE STRUCT of an otherwise-non-native module also lives in the
    // `*Natives` file, not in any generated `_types` split. The `_types`/skeleton
    // logic below only governs GENERATED structs, so resolve native structs to
    // the natives file directly — otherwise a module that has a Termination file
    // (or a bag) but whose relevant struct is native would emit a dangling
    // `import <stem>_types` (the emitter, gated on `has_own_structs`, never wrote
    // it). This is what lets native-struct modules (e.g. Vec_map / Vec_set) carry
    // a user Termination file.
    let struct_name = program.structs.get(&struct_id).name.clone();
    if native_struct_keys.contains(&(mid, struct_name)) {
        let stem = get_namespace_file_stem(program, mid);
        return Some(format!("import {}.{}Natives", pkg, stem));
    }
    let stem = match module_to_file.get(&mid) {
        Some((_, s)) => s.clone(),
        None => return None,
    };
    // Already defined in the importing file (same module or same SCC merge).
    if stem == current_stem {
        return None;
    }
    // Mirror the emitter's split decision: a file splits into `_types` (with a
    // `_types_skeleton` half iff it has a bag-bearing struct) when it has a user
    // termination file or a bag-bearing struct. `has_own_structs` is implied —
    // we are resolving a struct that lives in this module.
    let module_has_bag = bag_stems.contains(&stem);
    let module_imports_tci = tci_stems.contains(&stem);
    let (has_term, has_hooks) = user_hook_files(termination_dir, &stem);
    let has_termination_file = has_term || has_hooks;
    if !(has_termination_file || module_has_bag || module_imports_tci) {
        // Unsplit module: structs live in the main file. Such a module does not
        // import `TyCodeInterp`, so importing it directly is acyclic.
        return Some(format!("import {}.{}", pkg, stem));
    }
    if module_has_bag && !bag_ids.contains(&struct_id) {
        // Bag-free struct of a bag-bearing module -> the skeleton half.
        Some(format!("import {}.{}_types_skeleton", pkg, stem))
    } else {
        // Bag-bearing struct, or a termination-split non-bag module (a single
        // `_types` holding all structs).
        Some(format!("import {}.{}_types", pkg, stem))
    }
}

pub fn get_namespace_file_stem(program: &Program, module_id: usize) -> String {
    let ns = get_namespace(program, module_id);
    if program.namespace_overrides.contains_key(&module_id)
        && ns.ends_with(escape::NAMESPACE_COLLISION_SUFFIX)
    {
        // This override came from the namespace-vs-struct rename. Strip the
        // suffix; the on-disk filename uses the original namespace name.
        let module = program.modules.get(module_id);
        escape::module_name_to_namespace(&module.name)
    } else {
        ns
    }
}

/// True iff `ty` (transitively) references one of the given struct ids.
fn type_mentions_struct(ty: &Type, ids: &HashSet<usize>) -> bool {
    match ty {
        Type::Struct {
            struct_id,
            type_args,
        } => ids.contains(struct_id) || type_args.iter().any(|a| type_mentions_struct(a, ids)),
        Type::Vector(inner) | Type::Reference(inner) | Type::Option(inner) => {
            type_mentions_struct(inner, ids)
        }
        Type::MutableReference(inner, state) => {
            type_mentions_struct(inner, ids) || type_mentions_struct(state, ids)
        }
        Type::Tuple(ts) => ts.iter().any(|t| type_mentions_struct(t, ids)),
        _ => false,
    }
}

/// True iff any struct/function in `module_ids` references a heterogeneous bag
/// (in a field, a signature, or a call to a `bag`/`object_bag` native). Such a
/// file needs `import Generated.TyCodeInterp` for the `Universe`/`HasCode`
/// instances the bag operations resolve against.
fn file_uses_bag(program: &Program, module_ids: &[usize]) -> bool {
    let bag_struct_ids: HashSet<usize> = program
        .structs
        .iter()
        .filter(|(_, s)| {
            s.qualified_name == "bag::Bag" || s.qualified_name == "object_bag::ObjectBag"
        })
        .map(|(id, _)| *id)
        .collect();
    if bag_struct_ids.is_empty() {
        return false;
    }
    let bag_module_ids: HashSet<usize> = program
        .modules
        .iter()
        .filter(|(_, m)| m.package_name == "Sui" && (m.name == "bag" || m.name == "object_bag"))
        .map(|(id, _)| *id)
        .collect();
    let bag_fn_ids: HashSet<usize> = program
        .functions
        .iter()
        .filter(|(_, f)| bag_module_ids.contains(&f.module_id))
        .map(|(id, _)| id)
        .collect();
    // Every module whose structs / signatures / bodies mention a heterogeneous
    // bag needs TyCodeInterp for the `Universe` / `HasCode` instances the bag
    // operations resolve against — INCLUDING the `bag` / `object_bag` container
    // modules themselves, whose bodies reference `Bag TyCode`. They were once
    // excluded to avoid a cycle, but cross-file struct imports now resolve to
    // bag-free `_types_skeleton` files (see `struct_defining_import`), so no
    // skeleton imports a container module's main file and `<container> ->
    // TyCodeInterp` is acyclic.
    let in_file: HashSet<usize> = module_ids.iter().copied().collect();
    for (_, s) in program.structs.iter() {
        if in_file.contains(&s.module_id)
            && s.fields
                .iter()
                .any(|f| type_mentions_struct(&f.field_type, &bag_struct_ids))
        {
            return true;
        }
    }
    for (fid, f) in program.functions.iter() {
        if !in_file.contains(&f.module_id) {
            continue;
        }
        if f.signature
            .parameters
            .iter()
            .any(|p| type_mentions_struct(&p.param_type, &bag_struct_ids))
            || type_mentions_struct(&f.signature.return_type, &bag_struct_ids)
            || f.body.calls().any(|c| bag_fn_ids.contains(&c))
            // Needs BagU for a threaded `[HasCode BagU T]` binder (bag op or
            // `type_name::get<T>`), or CALLS a function that does — the call
            // site must resolve the `Universe BagU` / concrete `HasCode BagU`
            // instances. Without this, `type_name`-using files (that touch no
            // Bag struct directly) miss the `Generated.BagUInterp` import.
            || program.fn_bagu_params.contains_key(&fid)
            || f.body
                .calls()
                .any(|c| program.fn_bagu_params.contains_key(&c))
        {
            return true;
        }
    }
    false
}

/// Module IDs whose emitted FULL module file transitively imports
/// `Generated.BagUInterp`. A full module file imports `Generated.BagUInterp`
/// directly iff `file_uses_bag`; and it imports the full module files of every
/// module in its `required_imports`. So a module whose file re-imports
/// `BagUInterp` only through a dependency chain (e.g. cetus `Position_snapshot`,
/// which imports `Position`, which uses bag) is still a transitive importer even
/// though it uses no bag itself. Computed as reverse reachability over the
/// `required_imports` graph seeded by the direct bag-users.
/// Modules whose full emitted file transitively reaches `Generated.World`:
/// direct World users (world-typed signatures / world-fn body calls) plus the
/// reverse `required_imports` reachability closure — the world-side analogue
/// of `full_file_bagu_importers`.
fn full_file_world_importers(program: &Program) -> HashSet<ModuleID> {
    let mut importers: HashSet<ModuleID> = HashSet::new();
    for (mid, _) in program.modules.iter() {
        if super::dyn_type_universe::module_uses_world(program, *mid) {
            importers.insert(*mid);
        }
    }
    let mut changed = true;
    while changed {
        changed = false;
        for (mid, module) in program.modules.iter() {
            if importers.contains(mid) {
                continue;
            }
            if module
                .required_imports
                .iter()
                .any(|imp| importers.contains(imp))
            {
                importers.insert(*mid);
                changed = true;
            }
        }
    }
    importers
}

fn full_file_bagu_importers(program: &Program) -> HashSet<ModuleID> {
    let mut importers: HashSet<ModuleID> = HashSet::new();
    for (mid, _) in program.modules.iter() {
        if file_uses_bag(program, &[*mid]) {
            importers.insert(*mid);
        }
    }
    // A module's full file imports the full files of its `required_imports`;
    // propagate membership backwards along that edge to a fixed point.
    let mut changed = true;
    while changed {
        changed = false;
        for (mid, module) in program.modules.iter() {
            if importers.contains(mid) {
                continue;
            }
            if module
                .required_imports
                .iter()
                .any(|imp| importers.contains(imp))
            {
                importers.insert(*mid);
                changed = true;
            }
        }
    }
    importers
}

/// File stems whose emitted module file imports `Generated.TyCodeInterp`
/// (because some struct field, signature, or function body in that file uses a
/// heterogeneous bag). A struct living in such a file must be imported via its
/// bag-free split file (`_types_skeleton` / `_types`), never the full module
/// file, or any importer (e.g. `TyCodeInterp` itself) closes a build cycle.
/// Generalizes the bag-bearing-struct case to also cover modules that touch a
/// bag only in function bodies -- e.g. `*_tests` modules in `--test` mode.
pub fn tycodeinterp_importing_stems(
    program: &Program,
    native_struct_keys: &HashSet<(ModuleID, String)>,
) -> HashSet<String> {
    let mut stems: HashSet<String> = HashSet::new();
    if super::dyn_type_universe::program_uses_bag(program) {
        // The cycle only forms for a module that BOTH defines a struct named in the
        // `TyCode` universe (so `TyCodeInterp` imports it) AND imports `TyCodeInterp`
        // itself (so the back-edge closes). Restrict to that intersection -- a bag
        // container or a bag-using impl module that `TyCodeInterp` never imports must
        // NOT be split, or its consumers resolve to a `_types` file that was never
        // emitted.
        let universe = super::dyn_type_universe::collect(program);
        let mut universe_struct_ids: HashSet<StructID> = HashSet::new();
        for leaf in &universe.leaves {
            for sid in leaf.struct_ids() {
                universe_struct_ids.insert(sid);
            }
        }
        for w in &universe.wrappings {
            universe_struct_ids.insert(w.struct_id);
        }
        // `BagUInterp` imports the DEFINING file of every struct in its
        // DecidableEq derive-target closure, not just leaves/wrappings. If such
        // a struct's module also uses bag (so its own file imports
        // `BagUInterp`), a `BagUInterp -> <module> -> BagUInterp` build cycle
        // forms unless the struct is split into a bag-free `_types` file that
        // never imports `BagUInterp`. Include those derive-target modules so the
        // split fires -- mirroring the World-mode branch below. (Non-world-mode
        // bag packages like cetus clmm hit this: the cycle was
        // `BagUInterp -> CetusClmm.Position -> BagUInterp`.)
        for sid in super::dyn_type_universe::decidable_eq_derive_targets(
            &universe,
            program,
            native_struct_keys,
        ) {
            universe_struct_ids.insert(sid);
        }
        let universe_mids: HashSet<usize> = program
            .structs
            .iter()
            .filter(|(sid, _)| universe_struct_ids.contains(sid))
            .map(|(_, s)| s.module_id)
            .collect();
        // A module's FULL file transitively imports `Generated.BagUInterp` iff it
        // directly uses a bag (`file_uses_bag`) OR it (transitively, through the
        // full-module-file import graph) imports a module that does. Splitting
        // only DIRECT bag-users misses the case where `BagUInterp` imports a
        // derive-target module whose full file re-imports `BagUInterp` only via a
        // dependency chain: e.g. cetus `BagUInterp -> Position_snapshot ->
        // Position -> BagUInterp`. `Position_snapshot` uses no bag itself, so it
        // was never split, and importing its full file closed the cycle. Compute
        // the full transitive-importer closure so EVERY universe/derive-target
        // module that reaches `BagUInterp` back is split into its bag-free
        // `_types` half.
        let transitive_bag_importers = full_file_bagu_importers(program);
        let mut stem_mids: HashMap<String, Vec<usize>> = HashMap::new();
        for (mid, (_, stem)) in program.module_to_file.iter() {
            stem_mids.entry(stem.clone()).or_default().push(*mid);
        }
        stems.extend(
            stem_mids
                .into_iter()
                .filter(|(_, mids)| {
                    mids.iter().any(|m| universe_mids.contains(m))
                        && mids.iter().any(|m| transitive_bag_importers.contains(m))
                })
                .map(|(stem, _)| stem),
        );
    }
    // World-mode: the same hazard class through `Generated/World.lean` — a
    // module that defines a DF-universe member struct (`TyCodeInterp`
    // imports its defining file) AND uses World ops (its module file imports
    // `Generated.World`, which imports `TyCodeInterp`). Splitting its
    // structs into `<stem>_types` breaks the cycle exactly like the bag
    // case; `universe_struct_import` then resolves member structs to the
    // `_types` half.
    if program.world_functions.is_some() {
        // The import closure of `TyCodeInterp`/`BagUInterp` is the universe
        // members PLUS the DecidableEq derive-target field closure (both
        // universes) — any world-using module defining one of those structs
        // closes the cycle through `Generated/World.lean`. Native structs are
        // excluded: they resolve to `*Natives` files, which never use World.
        let mut member_sids: HashSet<StructID> = HashSet::new();
        for uni in [
            super::dyn_type_universe::collect_df(program),
            super::dyn_type_universe::collect(program),
        ] {
            for leaf in &uni.leaves {
                for sid in leaf.struct_ids() {
                    member_sids.insert(sid);
                }
            }
            for w in &uni.wrappings {
                member_sids.insert(w.struct_id);
            }
            for sid in super::dyn_type_universe::decidable_eq_derive_targets(
                &uni,
                program,
                native_struct_keys,
            ) {
                member_sids.insert(sid);
            }
        }
        member_sids.retain(|sid| {
            let s = program.structs.get(sid);
            !native_struct_keys.contains(&(s.module_id, s.name.clone()))
        });
        let member_mids: HashSet<usize> = program
            .structs
            .iter()
            .filter(|(sid, _)| member_sids.contains(sid))
            .map(|(_, s)| s.module_id)
            .collect();
        let mut stem_mids: HashMap<String, Vec<usize>> = HashMap::new();
        for (mid, (_, stem)) in program.module_to_file.iter() {
            stem_mids.entry(stem.clone()).or_default().push(*mid);
        }
        // Transitive-importer closure, mirroring `full_file_bagu_importers`:
        // a module whose full file merely IMPORTS a world-using module (e.g.
        // Table_vec → Table) still reaches `Generated.World`, so importing it
        // from TyCodeInterp closes the cycle even though none of its own kept
        // functions mention World directly. The direct test alone is
        // filter-dependent — a narrow --test-filter can prune every
        // world-using function out of Table_vec while its structs remain
        // derive targets, leaving the split unfired and the build cyclic.
        let transitive_world_importers = full_file_world_importers(program);
        stems.extend(
            stem_mids
                .into_iter()
                .filter(|(_, mids)| {
                    mids.iter().any(|m| member_mids.contains(m))
                        && mids.iter().any(|m| transitive_world_importers.contains(m))
                })
                .map(|(stem, _)| stem),
        );
    }
    stems
}

/// Check if a package name indicates it's a spec package.
/// Matches patterns like "Specs", "FooSpecs", "specs", etc.
fn is_spec_package(package_name: &str) -> bool {
    let lower = package_name.to_lowercase();
    lower == "specs" || lower.ends_with("specs")
}

/// Extract the namespace declared in a native file.
fn extract_native_namespace(native_file_path: &Path) -> Option<String> {
    if let Ok(content) = fs::read_to_string(native_file_path) {
        for line in content.lines() {
            let trimmed = line.trim();
            if let Some(rest) = trimmed.strip_prefix("namespace ") {
                if let Some(name) = rest.split_whitespace().next() {
                    return Some(name.to_string());
                }
            }
        }
    }
    None
}

/// Extract function names defined in a native file.

/// Extract implicit parameter blocks from native function definitions.
fn extract_native_implicit_params(
    native_file_path: &Path,
) -> HashMap<String, Vec<(String, Vec<String>)>> {
    let mut map = HashMap::new();
    if let Ok(content) = fs::read_to_string(native_file_path) {
        for line in content.lines() {
            let line = line.trim();
            // Strip optional attributes like @[reducible] before looking for def
            let stripped = if let Some(after_attr) = line.strip_prefix("@[") {
                after_attr
                    .find(']')
                    .map(|i| after_attr[i + 1..].trim_start())
                    .unwrap_or(line)
            } else {
                line
            };
            let rest = if let Some(r) = stripped.strip_prefix("def ") {
                r
            } else if let Some(r) = stripped.strip_prefix("partial def ") {
                r
            } else {
                continue;
            };
            let name_end = match rest.find([' ', '(', ':', '{']) {
                Some(e) => e,
                None => continue,
            };
            let name = rest[..name_end].to_string();
            let after_name = rest[name_end..].trim_start();

            let mut implicits = Vec::new();
            let mut remaining = after_name;
            while remaining.starts_with('{') {
                if let Some(close) = remaining.find('}') {
                    let block = &remaining[..=close];
                    let inner = &remaining[1..close];
                    let param_names: Vec<String> = if let Some(colon_pos) = inner.find(':') {
                        inner[..colon_pos]
                            .split_whitespace()
                            .map(|s| s.to_string())
                            .collect()
                    } else {
                        vec![]
                    };
                    implicits.push((block.to_string(), param_names));
                    remaining = remaining[close + 1..].trim_start();
                } else {
                    break;
                }
            }

            if !implicits.is_empty() {
                if let Some(base) = name.split('.').next() {
                    map.entry(base.to_string())
                        .or_insert_with(|| implicits.clone());
                }
                map.entry(name).or_insert(implicits);
            }
        }
    }
    map
}

/// Extract function names defined in a native file.
fn extract_native_function_names(native_file_path: &Path) -> HashSet<String> {
    let mut names = HashSet::new();
    if let Ok(content) = fs::read_to_string(native_file_path) {
        for line in content.lines() {
            let line = line.trim();
            let stripped = if let Some(after_attr) = line.strip_prefix("@[") {
                after_attr
                    .find(']')
                    .map(|i| after_attr[i + 1..].trim_start())
                    .unwrap_or(line)
            } else {
                line
            };
            let rest = if let Some(r) = stripped.strip_prefix("def ") {
                r
            } else if let Some(r) = stripped.strip_prefix("partial def ") {
                r
            } else if let Some(r) = stripped.strip_prefix("nonrec def ") {
                r
            } else {
                continue;
            };
            let name_end = match rest.find([' ', '(', ':', '{']) {
                Some(e) => e,
                None => continue,
            };
            names.insert(rest[..name_end].to_string());
        }
    }
    names
}

/// Extract struct/type names defined in a native file.
pub fn extract_native_struct_names_pub(native_file_path: &Path) -> HashSet<String> {
    extract_native_struct_names(native_file_path)
}

fn extract_native_struct_names(native_file_path: &Path) -> HashSet<String> {
    let mut names = HashSet::new();
    if let Ok(content) = fs::read_to_string(native_file_path) {
        for line in content.lines() {
            let line = line.trim();
            if let Some(rest) = line.strip_prefix("structure ") {
                if let Some(name_end) = rest.find([' ', '.', '{']) {
                    names.insert(rest[..name_end].to_string());
                } else if !rest.is_empty() {
                    names.insert(rest.to_string());
                }
            }
            if let Some(rest) = line.strip_prefix("abbrev ") {
                if let Some(name_end) = rest.find([' ', ':', '{']) {
                    names.insert(rest[..name_end].to_string());
                } else if !rest.is_empty() {
                    names.insert(rest.to_string());
                }
            }
            if let Some(rest) = line.strip_prefix("export ") {
                if let Some(paren_start) = rest.find('(') {
                    if let Some(paren_end) = rest.find(')') {
                        let exports = &rest[paren_start + 1..paren_end];
                        for export_name in exports.split_whitespace() {
                            if export_name.chars().next().is_some_and(|c| c.is_uppercase()) {
                                names.insert(export_name.to_string());
                            }
                        }
                    }
                }
            }
        }
    }
    names
}

/// Populate `program.namespace_overrides` for any module name that
/// appears in multiple packages with overlapping struct/function
/// names. The override turns `<ns>` into `<package>_<ns>` so the
/// rendered Lean files in `<package>/<package>_<ns>.lean` declare
/// disambiguated namespaces (`MoveStdlib_Bcs` vs `Sui_Bcs`) and don't
/// collide on import.
///
/// Both the Spec renderer (via `render_to_directory`) and the Test
/// pipeline (when building its own `Program` with
/// `BuildMode::Test`) need the same override map so cross-module
/// references in inlined `_test` defs resolve to the right namespace.
pub fn compute_namespace_overrides(program: &mut Program) {
    let mut module_struct_names: HashMap<usize, HashSet<String>> = HashMap::new();
    for (_, s) in &program.structs {
        module_struct_names
            .entry(s.module_id)
            .or_default()
            .insert(s.name.clone());
    }

    let mut module_func_names: HashMap<usize, HashSet<String>> = HashMap::new();
    for (_, func) in program.functions.iter() {
        module_func_names
            .entry(func.module_id)
            .or_default()
            .insert(func.name.clone());
    }

    let mut name_to_modules: HashMap<String, Vec<(usize, String)>> = HashMap::new();
    for (&mid, m) in &program.modules {
        if module_struct_names.contains_key(&mid) || module_func_names.contains_key(&mid) {
            name_to_modules
                .entry(m.name.clone())
                .or_default()
                .push((mid, m.package_name.clone()));
        }
    }

    let mut overrides = HashMap::new();
    for (_name, modules) in &name_to_modules {
        let mut packages: HashSet<&str> = HashSet::new();
        for (_, pkg) in modules {
            packages.insert(pkg);
        }
        if packages.len() > 1 {
            let mut has_collision = false;
            'outer: for i in 0..modules.len() {
                for j in (i + 1)..modules.len() {
                    let empty = HashSet::new();
                    let structs_i = module_struct_names.get(&modules[i].0).unwrap_or(&empty);
                    let structs_j = module_struct_names.get(&modules[j].0).unwrap_or(&empty);
                    if !structs_i.is_disjoint(structs_j) {
                        has_collision = true;
                        break 'outer;
                    }
                    let funcs_i = module_func_names.get(&modules[i].0).unwrap_or(&empty);
                    let funcs_j = module_func_names.get(&modules[j].0).unwrap_or(&empty);
                    if !funcs_i.is_disjoint(funcs_j) {
                        has_collision = true;
                        break 'outer;
                    }
                }
            }
            if has_collision {
                for (mid, pkg) in modules {
                    let ns = escape::module_name_to_namespace_qualified(_name, pkg);
                    overrides.insert(*mid, ns);
                }
            }
        }
    }

    // Additionally, override the namespace for any module whose would-be
    // namespace name collides with one of its own struct names. This
    // resolves Lean's extended-dot ambiguity for the affected modules
    // uniformly via a namespace suffix.
    let module_ids: Vec<usize> = program.modules.iter().map(|(&mid, _)| mid).collect();
    for mid in module_ids {
        if overrides.contains_key(&mid) {
            continue;
        }
        if escape::module_namespace_collides_with_struct(mid, program) {
            let module = program.modules.get(mid);
            let base = escape::module_name_to_namespace(&module.name);
            overrides.insert(
                mid,
                format!("{}{}", base, escape::NAMESPACE_COLLISION_SUFFIX),
            );
        }
    }

    program.namespace_overrides = overrides;
}

/// One-time migration from the legacy flat `sources/lean/*.lean` layout to the
/// `sources/lean/{Proofs,Termination}/` layout that lake builds directly (via
/// per-lib `srcDir`). Routing rule is the same one the old copy step used: a
/// file whose stem matches a generated module file is a termination file,
/// everything else is a proof file.
fn migrate_user_sources_layout(
    user_sources_dir: &Path,
    module_stems: &HashSet<String>,
) -> anyhow::Result<()> {
    let Ok(entries) = fs::read_dir(user_sources_dir) else {
        return Ok(());
    };
    for entry in entries.flatten() {
        let path = entry.path();
        if !path.is_file() || path.extension().and_then(|e| e.to_str()) != Some("lean") {
            continue;
        }
        let stem = path
            .file_stem()
            .and_then(|s| s.to_str())
            .expect("non-utf8 file name in sources/lean")
            .to_string();
        let subdir = if module_stems.contains(&stem) {
            "Termination"
        } else {
            "Proofs"
        };
        let dest_dir = user_sources_dir.join(subdir);
        fs::create_dir_all(&dest_dir)?;
        let dest = dest_dir.join(path.file_name().expect("file has no name"));
        assert!(
            !dest.exists(),
            "cannot migrate {}: {} already exists",
            path.display(),
            dest.display()
        );
        fs::rename(&path, &dest)?;
        eprintln!(
            "  📁 migrated sources/lean/{0}.lean -> sources/lean/{1}/{0}.lean",
            stem, subdir
        );
    }
    Ok(())
}

/// Render program to directory structure.
/// One Lean file per module containing all structs and functions.
pub fn render_to_directory(
    program: &mut Program,
    output_dir: &Path,
    prelude_imports: &[String],
    package_dir: &Path,
    user_package_name: Option<&str>,
    written: &mut WrittenFiles,
) -> anyhow::Result<()> {
    fs::create_dir_all(output_dir)?;
    let user_sources_dir = package_dir.join("sources").join("lean");
    let termination_dir = user_sources_dir.join("Termination");

    compute_namespace_overrides(program);

    copy_native_packages(program, output_dir, written)?;

    // Pre-compute which modules are specs that should be merged into their impl modules.
    // A spec module with package_name ending in "Specs" (or just "specs") gets merged into the same-named
    // impl module (package_name NOT ending in "Specs") if one exists.
    // Example: CetusCLMMSpecs::rewarder merges into CetusClmm::rewarder
    //          specs::vault_specs merges into upshift_vaults::vault
    let mut spec_to_impl: HashMap<usize, usize> = HashMap::new();
    let mut impl_to_specs: HashMap<usize, Vec<usize>> = HashMap::new();
    for (&mid, m) in &program.modules {
        if is_spec_package(&m.package_name) {
            // Extract the base package name (remove "Specs" suffix, normalize case)
            let spec_base = m
                .package_name
                .to_lowercase()
                .trim_end_matches("specs")
                .trim_end_matches('_')
                .to_string();
            // Find the corresponding impl module
            for (&other_id, other) in &program.modules {
                // Match spec module to impl module by comparing module names
                // (removing _specs suffix from spec module name if present)
                let spec_module_base = m.name.trim_end_matches("_specs");
                if (other.name == m.name || other.name == spec_module_base)
                    && !is_spec_package(&other.package_name)
                    && (spec_base.is_empty()
                        || other.package_name.to_lowercase().replace('_', "")
                            == spec_base.replace('_', ""))
                {
                    spec_to_impl.insert(mid, other_id);
                    impl_to_specs.entry(other_id).or_default().push(mid);
                    break;
                }
            }
        }
    }

    // Store the spec_to_impl mapping in the program for use by the renderer.
    // This allows function calls to merged spec modules to use the correct namespace.
    program.spec_to_impl = spec_to_impl.clone();

    // =========================================================================
    // Compute strongly connected components (SCCs) of the module dependency
    // graph to detect import cycles. Modules in the same SCC form a cycle and
    // must be rendered into a single merged file.
    // =========================================================================

    // Build adjacency list for the module dependency graph.
    // Only include non-spec modules (spec modules are already merged into impl).
    let renderable_module_ids: Vec<ModuleID> = program
        .modules
        .iter_ids()
        .filter(|mid| !spec_to_impl.contains_key(mid))
        .filter(|mid| !program.modules.get(*mid).is_native)
        .collect();

    let mut adjacency: HashMap<ModuleID, Vec<ModuleID>> = HashMap::new();
    for &mid in &renderable_module_ids {
        let module = program.modules.get(mid);
        let merged_spec_mids: Vec<usize> = impl_to_specs.get(&mid).cloned().unwrap_or_default();

        // Collect all imports (including from merged spec modules)
        let mut deps: HashSet<ModuleID> = module.required_imports.iter().copied().collect();
        for &spec_mid in &merged_spec_mids {
            let spec_module = program.modules.get(spec_mid);
            for &imp in &spec_module.required_imports {
                if imp != mid {
                    let actual_imp = spec_to_impl.get(&imp).copied().unwrap_or(imp);
                    deps.insert(actual_imp);
                }
            }
        }
        // Remove self-imports and merged spec module imports
        deps.remove(&mid);
        for &spec_mid in &merged_spec_mids {
            deps.remove(&spec_mid);
        }

        adjacency.insert(mid, deps.into_iter().collect());
    }

    let sccs = compute_module_sccs(&renderable_module_ids, &adjacency);

    // Native struct keys across ALL renderable modules. A native struct lives in
    // the module's hand-written `*Natives.lean`, never in a generated `_types`
    // split, so `struct_defining_import` must resolve it to the natives file even
    // when the module carries a Termination file or a bag. Computed once up front
    // because import resolution is cross-module (the per-SCC `native_infos` below
    // only covers the current SCC).
    let native_struct_keys: HashSet<(ModuleID, String)> = {
        let mut set = HashSet::new();
        for &mid in &renderable_module_ids {
            let module = program.modules.get(mid);
            let natives_stem = get_namespace_file_stem(program, mid);
            let natives_path = output_dir
                .join(&module.package_name)
                .join(format!("{}Natives.lean", natives_stem));
            if natives_path.exists() {
                for name in extract_native_struct_names(&natives_path) {
                    set.insert((mid, name));
                }
            }
        }
        set
    };

    // Build mapping: module_id -> (file_package, file_stem) for import resolution.
    // For singleton SCCs: the original package/namespace.
    // For multi-module SCCs: a merged file in the first module's package directory.
    let mut module_to_file: HashMap<ModuleID, (String, String)> = HashMap::new();
    // Track which modules are in the same SCC (for suppressing intra-SCC imports)
    let mut module_to_scc: HashMap<ModuleID, usize> = HashMap::new();

    for (scc_idx, scc) in sccs.iter().enumerate() {
        for &mid in scc {
            module_to_scc.insert(mid, scc_idx);
        }
        if scc.len() == 1 {
            let mid = scc[0];
            let module = program.modules.get(mid);
            let file_stem = get_namespace_file_stem(program, mid);
            module_to_file.insert(mid, (module.package_name.clone(), file_stem));
        } else {
            // Multi-module SCC: merged file.
            // Sort SCC members by file stem for deterministic naming.
            let mut sorted_scc: Vec<ModuleID> = scc.clone();
            sorted_scc.sort_by_key(|&mid| get_namespace_file_stem(program, mid));

            let raw_merged_stem: String = sorted_scc
                .iter()
                .map(|&mid| get_namespace_file_stem(program, mid))
                .collect::<Vec<_>>()
                .join("__");

            // Cap the merged filename to stay within ext4's 255-byte
            // filename limit (with margin for `.lean`, `.olean`, `.ilean`,
            // `.olean.hash`, etc. siblings lake creates). Keep a readable
            // prefix and suffix-hash the full content for uniqueness.
            const MAX_STEM_LEN: usize = 200;
            let merged_stem: String = if raw_merged_stem.len() <= MAX_STEM_LEN {
                raw_merged_stem
            } else {
                use std::collections::hash_map::DefaultHasher;
                use std::hash::{Hash, Hasher};
                let mut h = DefaultHasher::new();
                raw_merged_stem.hash(&mut h);
                let hash_suffix = format!("__h{:016x}", h.finish());
                let prefix_len = MAX_STEM_LEN.saturating_sub(hash_suffix.len());
                let mut prefix: String = raw_merged_stem.chars().take(prefix_len).collect();
                while prefix.ends_with('_') {
                    prefix.pop();
                }
                format!("{}{}", prefix, hash_suffix)
            };

            // Use the first module's package for the file location
            let first_pkg = program.modules.get(sorted_scc[0]).package_name.clone();

            for &mid in scc {
                module_to_file.insert(mid, (first_pkg.clone(), merged_stem.clone()));
            }

            let scc_namespaces: Vec<String> = sorted_scc
                .iter()
                .map(|&mid| get_namespace(program, mid))
                .collect();
            eprintln!(
                "  📦 Merging cyclic modules into {}/{}.lean: {:?}",
                first_pkg, merged_stem, scc_namespaces
            );
        }
    }

    // Store the module_to_file mapping in the program for use during rendering.
    // This lets type/call rendering resolve imports to the correct merged file.
    program.module_to_file = module_to_file.clone();

    // Lake builds sources/lean/{Proofs,Termination}/ directly (per-lib srcDir);
    // move any legacy flat-layout files into place first.
    let module_stems: HashSet<String> = module_to_file.values().map(|(_, s)| s.clone()).collect();
    migrate_user_sources_layout(&user_sources_dir, &module_stems)?;

    // Delete stale individual module files for modules that are now merged into SCC groups.
    // Lake uses `globs := #[.submodules]` which picks up ALL .lean files in a directory,
    // so leftover files from previous runs would cause duplicate/conflicting declarations.
    for scc in &sccs {
        if scc.len() > 1 {
            for &mid in scc {
                let module = program.modules.get(mid);
                let namespace = get_namespace(program, mid);
                let old_file = output_dir
                    .join(&module.package_name)
                    .join(format!("{}.lean", namespace));
                if old_file.exists() {
                    let _ = fs::remove_file(&old_file);
                }
            }
        }
    }

    // =========================================================================
    // Render each SCC as a single file (singleton or merged)
    // =========================================================================

    // Precomputed once for the type-universe import layering (consumed by
    // `struct_defining_import`): the bag-bearing struct ids, and the file stems
    // that contain at least one bag-bearing struct (and therefore emit a
    // `_types_skeleton`). These drive the per-struct defining-file resolver so
    // every struct reference imports the exact file that defines it.
    let bag_ids: HashSet<StructID> =
        super::dyn_type_universe::collect_bag_containing_struct_ids(program);
    let bag_stems: HashSet<String> = bag_ids
        .iter()
        .filter_map(|sid| {
            program
                .structs
                .has(*sid)
                .then(|| module_to_file.get(&program.structs.get(sid).module_id))
                .flatten()
        })
        .map(|(_, stem)| stem.clone())
        .collect();
    let tci_stems: HashSet<String> = tycodeinterp_importing_stems(program, &native_struct_keys);

    for scc in &sccs {
        // Determine the modules in this rendering unit.
        // For a singleton SCC, this is just one module.
        // For a multi-module SCC, we render all modules into one file.
        let scc_set: HashSet<ModuleID> = scc.iter().copied().collect();

        // Order SCC members by dependencies: modules that are depended upon should
        // come first so their structs/defs are visible to later namespaces.
        // Since this is an SCC (cycle), a perfect topological sort is impossible,
        // but we use a greedy approach: repeatedly pick the module with the fewest
        // unsatisfied intra-SCC dependencies, breaking ties alphabetically.
        let ordered_scc: Vec<ModuleID> = {
            let scc_members: HashSet<ModuleID> = scc.iter().copied().collect();
            // Build intra-SCC in-degree: for each module, count how many SCC siblings it depends on
            let mut intra_deps: HashMap<ModuleID, HashSet<ModuleID>> = HashMap::new();
            for &mid in scc {
                let deps_of_mid = adjacency.get(&mid).cloned().unwrap_or_default();
                let intra: HashSet<ModuleID> = deps_of_mid
                    .into_iter()
                    .filter(|d| scc_members.contains(d))
                    .collect();
                intra_deps.insert(mid, intra);
            }

            let mut remaining: HashSet<ModuleID> = scc_members.clone();
            let mut result: Vec<ModuleID> = Vec::with_capacity(scc.len());

            while !remaining.is_empty() {
                // Find module with fewest unsatisfied intra-SCC dependencies
                let best = remaining
                    .iter()
                    .copied()
                    .min_by_key(|&mid| {
                        let unsatisfied = intra_deps[&mid]
                            .iter()
                            .filter(|d| remaining.contains(d))
                            .count();
                        (unsatisfied, get_namespace(program, mid))
                    })
                    .expect("remaining is non-empty");
                result.push(best);
                remaining.remove(&best);
            }
            result
        };

        // Collect all imports for the entire SCC
        let mut all_imports: HashSet<ModuleID> = HashSet::new();
        for &mid in &ordered_scc {
            let module = program.modules.get(mid);
            let merged_spec_mids: Vec<usize> = impl_to_specs.get(&mid).cloned().unwrap_or_default();

            for &imp in &module.required_imports {
                all_imports.insert(imp);
            }
            for &spec_mid in &merged_spec_mids {
                let spec_module = program.modules.get(spec_mid);
                for &imp in &spec_module.required_imports {
                    let actual_imp = spec_to_impl.get(&imp).copied().unwrap_or(imp);
                    all_imports.insert(actual_imp);
                }
            }

            // Also remove merged spec modules from imports
            for &spec_mid in &merged_spec_mids {
                all_imports.remove(&spec_mid);
            }
        }

        // Remove self-references (modules within this SCC)
        for &mid in &ordered_scc {
            all_imports.remove(&mid);
        }

        // Build file output
        let mut file_output = String::new();

        // Header comment
        let module_names: Vec<String> = ordered_scc
            .iter()
            .map(|&mid| program.modules.get(mid).name.clone())
            .collect();
        if module_names.len() == 1 {
            file_output.push_str(&format!("-- Module: {}\n\n", module_names[0]));
        } else {
            file_output.push_str(&format!("-- Modules: {}\n\n", module_names.join(", ")));
        }

        // Prelude imports
        for prelude_import in prelude_imports {
            file_output.push_str(&format!("import {}\n", prelude_import));
        }

        // Heterogeneous-bag closed universe: a file that uses Bag needs the
        // per-project `Universe`/`HasCode` instances. (A file that itself
        // defines a struct interpreted by TyCodeInterp would form a cycle --
        // the bag-in-struct case, not yet handled by the legacy _types split.)
        if super::dyn_type_universe::program_uses_bag(program)
            && file_uses_bag(program, &ordered_scc)
        {
            file_output.push_str("import Generated.BagUInterp\n");
        }

        // World-mode: a file whose functions carry the threaded `__world`
        // param or call `World.*` typed views needs the per-project
        // `Generated/World.lean` pin (abbrev + wrappers).
        if program.world_functions.is_some()
            && ordered_scc
                .iter()
                .any(|&mid| super::dyn_type_universe::module_uses_world(program, mid))
        {
            file_output.push_str("import Generated.World\n");
        }

        // Module imports (deduplicated, redirected to merged files)
        let mut import_stmts: HashSet<String> = HashSet::new();
        for &required_module_id in &all_imports {
            let Some((file_pkg, file_stem)) = module_to_file.get(&required_module_id) else {
                continue;
            };
            import_stmts.insert(format!("import {}.{}", file_pkg, file_stem));
        }
        let mut import_stmts: Vec<String> = import_stmts.into_iter().collect();
        import_stmts.sort();
        for stmt in &import_stmts {
            file_output.push_str(stmt);
            file_output.push('\n');
        }

        // Native imports for all modules in this SCC
        // Collect native info per module
        struct NativeInfo {
            struct_names: HashSet<String>,
            function_names: HashSet<String>,
            namespace: Option<String>,
        }
        let mut native_infos: HashMap<ModuleID, NativeInfo> = HashMap::new();

        for &mid in &ordered_scc {
            let module = program.modules.get(mid);
            let natives_stem = get_namespace_file_stem(program, mid);
            let natives_path = output_dir
                .join(&module.package_name)
                .join(format!("{}Natives.lean", natives_stem));

            let module_has_content = program.structs.values().any(|s| s.module_id == mid)
                || program.functions.iter().any(|(_, f)| f.module_id == mid);

            if natives_path.exists() && module_has_content {
                file_output.push_str(&format!(
                    "import {}.{}Natives\n",
                    module.package_name, natives_stem
                ));
                native_infos.insert(
                    mid,
                    NativeInfo {
                        struct_names: extract_native_struct_names(&natives_path),
                        function_names: extract_native_function_names(&natives_path),
                        namespace: extract_native_namespace(&natives_path),
                    },
                );
            }
        }

        // Check if a user-provided termination file exists for this module:
        // sources/lean/Termination/<stem>.lean, built by lake in place.
        let first_mid = ordered_scc[0];
        let (file_pkg_first, file_stem) = module_to_file[&first_mid].clone();
        let termination_file = termination_dir.join(format!("{}.lean", file_stem));
        let (has_term_file, has_hooks_file) = user_hook_files(&termination_dir, &file_stem);
        let has_termination_file = has_term_file || has_hooks_file;

        // Parse the termination file (if any) for the set of measure definitions it
        // provides — lines `def <name>.termination ...`. A loop helper only gets a
        // `termination_by <name>.termination` / user macro reference when the file
        // actually defines that measure; otherwise it falls back to the inline
        // `termination_by (0 : Nat); decreasing_by all_goals sorry` default. This lets
        // a termination file cover SOME loops in a module without forcing every other
        // recursive helper to reference a (nonexistent) user macro.
        let termination_measures: HashSet<String> = {
            let mut content = String::new();
            if has_term_file {
                content.push_str(&std::fs::read_to_string(&termination_file).unwrap_or_default());
            }
            if has_hooks_file {
                let hooks_file = termination_dir
                    .parent()
                    .expect("sources/lean has a parent")
                    .join("Hooks")
                    .join(format!("{}.lean", file_stem));
                content.push('\n');
                content.push_str(&std::fs::read_to_string(&hooks_file).unwrap_or_default());
            }
            content
                .lines()
                .filter_map(|line| {
                    let t = line.trim_start();
                    let rest = t.strip_prefix("def ")?;
                    let name = rest.split([' ', '(', '\t']).next()?;
                    name.strip_suffix(".termination")
                        .map(|stem| stem.to_string())
                })
                .collect()
        };

        // Factor struct definitions into a separate `*_types.lean` file (with a
        // bag-free `*_types_skeleton.lean` half for bag-bearing modules) in two
        // INDEPENDENT cases:
        //   - a user `Termination/<stem>.lean` exists — breaks the cycle between
        //     the main file (imports Termination) and that file (needs struct
        //     types for its measures); or
        //   - the module is bag-bearing — breaks the cycle between the main file
        //     and `Generated/TyCodeInterp` (which imports the bag-free skeleton).
        // These are orthogonal; either alone forces the split. Cross-file struct
        // dependencies are resolved per-struct via `struct_defining_import`, so a
        // skeleton imports only the *defining* files of its (always bag-free)
        // dependencies and never a `TyCodeInterp`-importing module file.
        let has_own_structs = ordered_scc.iter().any(|&mid| {
            let empty_native = NativeInfo {
                struct_names: HashSet::new(),
                function_names: HashSet::new(),
                namespace: None,
            };
            let ni = native_infos.get(&mid).unwrap_or(&empty_native);
            program
                .structs
                .values()
                .any(|s| s.module_id == mid && !ni.struct_names.contains(&s.name))
        });
        let module_has_bag = ordered_scc.iter().any(|&mid| {
            program
                .structs
                .iter()
                .any(|(sid, s)| s.module_id == mid && bag_ids.contains(sid))
        });
        let has_types_file = if (has_termination_file
            || module_has_bag
            || tci_stems.contains(&file_stem))
            && has_own_structs
        {
            // Prelude + native imports are common to the skeleton and types
            // files. Struct-dependency imports are computed SEPARATELY per
            // partition below, so the skeleton never pulls in a bag-bearing
            // dependency's `TyCodeInterp`-importing file.
            let mut common_imports = format!("-- Types for: {}\n\n", file_stem);
            for prelude_import in prelude_imports {
                common_imports.push_str(&format!("import {}\n", prelude_import));
            }
            for &mid in &ordered_scc {
                let natives_stem = get_namespace_file_stem(program, mid);
                let natives_path = output_dir
                    .join(&program.modules.get(mid).package_name)
                    .join(format!("{}Natives.lean", natives_stem));
                if natives_path.exists() {
                    let module = program.modules.get(mid);
                    common_imports.push_str(&format!(
                        "import {}.{}Natives\n",
                        module.package_name, natives_stem
                    ));
                }
            }

            // Partition each module's structs into bag-free (skeleton) and
            // bag-bearing (types), accumulating each partition's cross-file
            // struct-dependency imports via the defining-file resolver.
            let mut skeleton_body = String::new();
            let mut types_body = String::new();
            let mut skeleton_imports: BTreeSet<String> = BTreeSet::new();
            let mut types_imports: BTreeSet<String> = BTreeSet::new();
            for &mid in &ordered_scc {
                let namespace_name = get_namespace(program, mid);
                let empty_native = NativeInfo {
                    struct_names: HashSet::new(),
                    function_names: HashSet::new(),
                    namespace: None,
                };
                let ni = native_infos.get(&mid).unwrap_or(&empty_native);
                let module_has_structs = program
                    .structs
                    .values()
                    .any(|s| s.module_id == mid && !ni.struct_names.contains(&s.name));
                if !module_has_structs {
                    continue;
                }

                // Native re-exports are bag-free -> skeleton.
                let mut sk = String::new();
                if let Some(ref ns) = ni.namespace {
                    if ns != &namespace_name && !ni.struct_names.is_empty() {
                        sk.push_str(&format!("open {}\n", ns));
                        for struct_name in &ni.struct_names {
                            sk.push_str(&format!(
                                "abbrev {} := {}.{}\n",
                                struct_name, ns, struct_name
                            ));
                        }
                        sk.push('\n');
                    }
                }
                let mut ty = String::new();
                for (sid, struct_def) in &program.structs {
                    if struct_def.module_id == mid && !ni.struct_names.contains(&struct_def.name) {
                        let mut writer = LeanWriter::new(String::new());
                        render_struct(struct_def, program, &namespace_name, &mut writer);
                        let rendered = writer.into_inner();
                        let is_bag = bag_ids.contains(sid);
                        if is_bag {
                            ty.push_str(&rendered);
                        } else {
                            sk.push_str(&rendered);
                        }
                        // Cross-file struct deps go into the matching partition's
                        // import set, resolved to each dep's defining file.
                        let target = if is_bag {
                            &mut types_imports
                        } else {
                            &mut skeleton_imports
                        };
                        let mut fields_iter: Vec<_> = struct_def.fields.iter().collect();
                        if let Some(ref variants) = struct_def.variants {
                            for variant in variants {
                                fields_iter.extend(variant.fields.iter());
                            }
                        }
                        for field in fields_iter {
                            for dep_sid in field.field_type.struct_ids() {
                                if let Some(line) = struct_defining_import(
                                    program,
                                    dep_sid,
                                    &file_stem,
                                    &termination_dir,
                                    &module_to_file,
                                    &bag_ids,
                                    &bag_stems,
                                    &tci_stems,
                                    &native_struct_keys,
                                ) {
                                    target.insert(line);
                                }
                            }
                        }
                    }
                }
                if !sk.is_empty() {
                    skeleton_body.push_str(&format!("namespace {}\n\n", namespace_name));
                    skeleton_body.push_str(&sk);
                    skeleton_body.push_str(&format!("end {}\n\n", namespace_name));
                }
                if !ty.is_empty() {
                    types_body.push_str(&format!("namespace {}\n\n", namespace_name));
                    types_body.push_str(&ty);
                    types_body.push_str(&format!("end {}\n\n", namespace_name));
                }
            }

            let fmt_imports = |set: &BTreeSet<String>| -> String {
                let mut s = String::new();
                for line in set {
                    s.push_str(line);
                    s.push('\n');
                }
                s
            };

            let set_opt = "\nset_option linter.unusedVariables false\n\n";
            if module_has_bag {
                let skeleton_stem = format!("{}_types_skeleton", file_stem);
                let mut sk_out = common_imports.clone();
                sk_out.push_str(&fmt_imports(&skeleton_imports));
                sk_out.push_str("import Generated.BagU\n");
                sk_out.push_str(set_opt);
                sk_out.push_str(&skeleton_body);
                let sk_path = output_dir
                    .join(&file_pkg_first)
                    .join(format!("{}.lean", skeleton_stem));
                write_if_changed(&sk_path, &sk_out, written)?;

                let mut ty_out = common_imports.clone();
                ty_out.push_str(&fmt_imports(&types_imports));
                ty_out.push_str(&format!("import {}.{}\n", file_pkg_first, skeleton_stem));
                ty_out.push_str("import Generated.BagUInterp\n");
                ty_out.push_str(set_opt);
                ty_out.push_str(&types_body);
                let types_path = output_dir
                    .join(&file_pkg_first)
                    .join(format!("{}_types.lean", file_stem));
                write_if_changed(&types_path, &ty_out, written)?;
            } else {
                // No bag-bearing struct: every struct is bag-free and lands in a
                // single `_types` file (no skeleton); only `skeleton_imports`
                // was populated.
                let mut out = common_imports.clone();
                out.push_str(&fmt_imports(&skeleton_imports));
                out.push_str(set_opt);
                out.push_str(&skeleton_body);
                let types_path = output_dir
                    .join(&file_pkg_first)
                    .join(format!("{}_types.lean", file_stem));
                write_if_changed(&types_path, &out, written)?;
            }

            file_output.push_str(&format!("import {}.{}_types\n", file_pkg_first, file_stem));
            true
        } else {
            false
        };

        if has_term_file {
            file_output.push_str(&format!("import Termination.{}\n", file_stem));
        }
        if has_hooks_file {
            file_output.push_str(&format!("import Hooks.{}\n", file_stem));
        }

        file_output.push('\n');
        // 1M rec depth: chained `u128` arithmetic (e.g. `random.move`'s
        // multi-step seed mix) plus per-test driver inlining of every
        // transitive callee produces enormous let-spines that exceed
        // both Lean's default 512 and the previous 4K/100K caps on
        // bigger test files (ember-vaults' `Test_charge_*.lean` is
        // 8500+ lines). Tests still build in tens of seconds; the cap
        // affects only elaboration depth, not runtime.
        file_output.push_str("set_option maxRecDepth 1000000\n");
        // Heartbeats: 8M (default 200K, prior value 800K). Stdlib's
        // pathological `test_dos` macro produces auto-generated
        // mutual `.aborts` companions with 180+ params and 250+ body
        // lines per loop helper — Lean's whnf reduction needs more
        // budget than the conservative default to get through them.
        // Bumped from 800K to 8M after the cascade fix in
        // `inject_arithmetic_aborts::transform_existing` revealed the
        // (deterministic) timeout failures (and downstream "Unknown
        // constant" errors when timed-out defs in a mutual block fail
        // to register and dependents elsewhere look them up).
        file_output.push_str("set_option maxHeartbeats 8000000\n");
        file_output.push_str("set_option synthInstance.maxHeartbeats 4000000\n");
        file_output.push_str("set_option linter.unusedVariables false\n\n");

        // For multi-module SCCs (cyclic dependencies), we split rendering into
        // two phases: first all struct definitions across all namespaces, then all
        // function definitions. This ensures struct types are available before any
        // function body references them, avoiding forward-reference errors in Lean.
        // Lean allows reopening namespaces, so this is well-supported.
        let is_multi_scc = ordered_scc.len() > 1;

        // Phase 1 (for multi-SCC): Emit structs and native struct re-exports
        // Use struct-level dependency ordering: a module's structs may reference
        // struct types from other SCC modules, so those must be defined first.
        // Skip if structs are already in a types file.
        if is_multi_scc && !has_types_file {
            // Collect all structs from SCC modules and sort at individual struct level.
            // This handles circular module deps where module A's struct X depends on
            // module B's struct Y, but module B's struct Z depends on module A's struct W.
            // Module-level ordering can't resolve this, but struct-level ordering can.
            let scc_members: HashSet<ModuleID> = ordered_scc.iter().copied().collect();
            // Also include merged spec modules so ghost tag structs etc. are emitted.
            let scc_members_with_specs: HashSet<ModuleID> = scc_members
                .iter()
                .copied()
                .chain(scc_members.iter().flat_map(|mid| {
                    impl_to_specs
                        .get(mid)
                        .into_iter()
                        .flat_map(|v| v.iter().copied())
                }))
                .collect();

            // Collect (struct_id, module_id) for all non-native structs in the SCC
            let mut scc_structs: Vec<(usize, ModuleID)> = Vec::new();
            for (&sid, s) in &program.structs {
                if scc_members.contains(&s.module_id) {
                    let empty_native = NativeInfo {
                        struct_names: HashSet::new(),
                        function_names: HashSet::new(),
                        namespace: None,
                    };
                    let native_info = native_infos.get(&s.module_id).unwrap_or(&empty_native);
                    if !native_info.struct_names.contains(&s.name) {
                        scc_structs.push((sid, s.module_id));
                    }
                }
            }

            // Compute struct-to-struct deps within the SCC
            let scc_struct_ids: HashSet<usize> = scc_structs.iter().map(|&(sid, _)| sid).collect();
            let mut struct_deps: HashMap<usize, HashSet<usize>> = HashMap::new();
            for &(sid, _) in &scc_structs {
                let s = program.structs.get(&sid);
                let mut deps: HashSet<usize> = HashSet::new();
                for field in &s.fields {
                    for dep_sid in field.field_type.struct_ids() {
                        if dep_sid != sid && scc_struct_ids.contains(&dep_sid) {
                            deps.insert(dep_sid);
                        }
                    }
                }
                if let Some(ref variants) = s.variants {
                    for variant in variants {
                        for field in &variant.fields {
                            for dep_sid in field.field_type.struct_ids() {
                                if dep_sid != sid && scc_struct_ids.contains(&dep_sid) {
                                    deps.insert(dep_sid);
                                }
                            }
                        }
                    }
                }
                struct_deps.insert(sid, deps);
            }

            // Greedy topological sort at struct level
            let mut remaining: HashSet<usize> = scc_struct_ids;
            let mut ordered_structs: Vec<(usize, ModuleID)> = Vec::new();
            while !remaining.is_empty() {
                let best = remaining
                    .iter()
                    .copied()
                    .min_by_key(|&sid| {
                        let unsatisfied = struct_deps[&sid]
                            .iter()
                            .filter(|d| remaining.contains(d))
                            .count();
                        let s = program.structs.get(&sid);
                        (unsatisfied, get_namespace(program, s.module_id), &s.name)
                    })
                    .expect("remaining is non-empty");
                let mid = scc_structs.iter().find(|&&(s, _)| s == best).unwrap().1;
                ordered_structs.push((best, mid));
                remaining.remove(&best);
            }

            // Emit native struct re-exports first (grouped by module)
            let mut reexport_modules_done: HashSet<ModuleID> = HashSet::new();
            for &mid in &ordered_scc {
                if reexport_modules_done.contains(&mid) {
                    continue;
                }
                let namespace_name = get_namespace(program, mid);
                let empty_native = NativeInfo {
                    struct_names: HashSet::new(),
                    function_names: HashSet::new(),
                    namespace: None,
                };
                let native_info = native_infos.get(&mid).unwrap_or(&empty_native);
                if let Some(ref ns) = native_info.namespace {
                    if ns != &namespace_name && !native_info.struct_names.is_empty() {
                        file_output.push_str(&format!("namespace {}\n", namespace_name));
                        file_output.push_str(&format!("open {}\n", ns));
                        for struct_name in &native_info.struct_names {
                            file_output.push_str(&format!(
                                "abbrev {} := {}.{}\n",
                                struct_name, ns, struct_name
                            ));
                        }
                        file_output.push_str(&format!("end {}\n\n", namespace_name));
                    }
                }
                reexport_modules_done.insert(mid);
            }

            // Emit structs in dependency order, opening/closing namespaces as needed
            let mut current_ns: Option<String> = None;
            for &(sid, mid) in &ordered_structs {
                let namespace_name = get_namespace(program, mid);
                if current_ns.as_deref() != Some(&namespace_name) {
                    if let Some(ref ns) = current_ns {
                        file_output.push_str(&format!("end {}\n\n", ns));
                    }
                    file_output.push_str(&format!("namespace {}\n", namespace_name));
                    current_ns = Some(namespace_name.clone());
                }
                let struct_def = program.structs.get(&sid);
                let mut writer = LeanWriter::new(String::new());
                render_struct(struct_def, program, &namespace_name, &mut writer);
                file_output.push_str(&writer.into_inner());
            }
            if let Some(ref ns) = current_ns {
                file_output.push_str(&format!("end {}\n\n", ns));
            }
        }

        // Phase 2 (or only phase for singletons): Emit functions (and structs for singletons)
        //
        // For multi-module SCCs, we do a global cross-namespace topological sort of
        // all functions, then render them with dynamic namespace switching. This
        // minimizes forward references between namespaces.
        // For singletons, we use the original per-module approach.

        if is_multi_scc {
            // ------------------------------------------------------------------
            // Multi-SCC: global cross-namespace function rendering
            // ------------------------------------------------------------------

            // First, emit native function re-exports for each module
            for &module_id in &ordered_scc {
                let namespace_name = get_namespace(program, module_id);
                let empty_native = NativeInfo {
                    function_names: HashSet::new(),
                    struct_names: HashSet::new(),
                    namespace: None,
                };
                let native_info = native_infos.get(&module_id).unwrap_or(&empty_native);
                if let Some(ref ns) = native_info.namespace {
                    if ns != &namespace_name && !native_info.function_names.is_empty() {
                        file_output.push_str(&format!("namespace {}\n", namespace_name));
                        file_output.push_str(&format!("open {}\n", ns));
                        let mut sorted_fn_names: Vec<&String> =
                            native_info.function_names.iter().collect();
                        sorted_fn_names.sort();
                        for func_name in sorted_fn_names {
                            file_output.push_str(&format!(
                                "abbrev {} := @{}.{}\n",
                                func_name, ns, func_name
                            ));
                        }
                        file_output.push_str(&format!("end {}\n\n", namespace_name));
                    }
                }
            }

            // Collect ALL functions across ALL modules in this SCC
            let mut all_scc_func_ids: Vec<usize> = Vec::new();
            let mut func_to_module: HashMap<usize, ModuleID> = HashMap::new();
            // Build per-module imported-same-namespace-funcs and native info for filtering
            let mut module_imported_funcs: HashMap<ModuleID, HashSet<String>> = HashMap::new();
            let mut module_merged_specs: HashMap<ModuleID, Vec<usize>> = HashMap::new();

            for &module_id in &ordered_scc {
                let namespace_name = get_namespace(program, module_id);
                let merged_spec_modules: Vec<usize> =
                    impl_to_specs.get(&module_id).cloned().unwrap_or_default();

                let mut imported_same_namespace_funcs: HashSet<String> = HashSet::new();
                for &imp_id in &all_imports {
                    let imp_namespace = get_namespace(program, imp_id);
                    if imp_namespace == namespace_name {
                        for (_, func) in program.functions.iter() {
                            if func.module_id == imp_id {
                                imported_same_namespace_funcs
                                    .insert(escape::escape_identifier(&func.name));
                            }
                        }
                    }
                }

                let all_module_ids: Vec<usize> = std::iter::once(module_id)
                    .chain(merged_spec_modules.iter().copied())
                    .collect();

                let empty_native = NativeInfo {
                    struct_names: HashSet::new(),
                    function_names: HashSet::new(),
                    namespace: None,
                };
                let native_info = native_infos.get(&module_id).unwrap_or(&empty_native);
                let natives_path = output_dir
                    .join(&program.modules.get(module_id).package_name)
                    .join(format!(
                        "{}Natives.lean",
                        get_namespace_file_stem(program, module_id)
                    ));

                // Track rendered function names to skip duplicates from merged spec modules
                let mut seen_func_names: HashSet<String> = HashSet::new();
                for (fid, func) in program.functions.iter() {
                    if !all_module_ids.contains(&func.module_id) {
                        continue;
                    }
                    if func.is_native && natives_path.exists() {
                        continue;
                    }
                    let escaped = escape::escape_identifier(&func.name);
                    let final_rendered_name = escaped.clone();
                    if native_info.function_names.contains(&final_rendered_name) {
                        continue;
                    }
                    if imported_same_namespace_funcs.contains(&final_rendered_name) {
                        continue;
                    }
                    if must_skip_function(func) {
                        continue;
                    }
                    // Skip duplicate functions from merged spec modules
                    if !seen_func_names.insert(func.name.clone()) {
                        continue;
                    }
                    all_scc_func_ids.push(fid);
                    func_to_module.insert(fid, module_id);
                }

                module_imported_funcs.insert(module_id, imported_same_namespace_funcs);
                module_merged_specs.insert(module_id, merged_spec_modules);
            }

            // Emit native function re-exports per module
            for &module_id in &ordered_scc {
                let namespace_name = get_namespace(program, module_id);
                let empty_native = NativeInfo {
                    struct_names: HashSet::new(),
                    function_names: HashSet::new(),
                    namespace: None,
                };
                let native_info = native_infos.get(&module_id).unwrap_or(&empty_native);
                if let Some(ref ns) = native_info.namespace {
                    if ns != &namespace_name {
                        // Union of Move-source natives and natives-file `def`s.
                        // See singleton-path comment for the rationale.
                        let mut native_fn_set: std::collections::BTreeSet<String> =
                            native_info.function_names.iter().cloned().collect();
                        for (_, f) in program.functions.iter() {
                            if f.module_id == module_id && f.is_native {
                                native_fn_set.insert(escape::escape_identifier(&f.name));
                            }
                        }
                        let native_fn_names: Vec<String> = native_fn_set.into_iter().collect();
                        if !native_fn_names.is_empty() {
                            file_output.push_str(&format!("namespace {}\n", namespace_name));
                            for func_name in &native_fn_names {
                                file_output.push_str(&format!(
                                    "abbrev {} := @{}.{}\n",
                                    func_name, ns, func_name
                                ));
                            }
                            file_output.push_str(&format!("end {}\n\n", namespace_name));
                        }
                    }
                }
            }

            // Global topological sort across all SCC functions
            let sorted_funcs = topological_sort_functions(&all_scc_func_ids, program);

            // Build mutual group info
            let mut mutual_groups: BTreeMap<usize, Vec<usize>> = BTreeMap::new();
            let mut func_to_group: HashMap<usize, usize> = HashMap::new();
            for &func_id in &sorted_funcs {
                let func = program.functions.get(&func_id);
                if let Some(group_id) = func.mutual_group_id {
                    mutual_groups.entry(group_id).or_default().push(func_id);
                    func_to_group.insert(func_id, group_id);
                }
            }

            // Render functions with dynamic namespace switching
            let mut current_namespace: Option<String> = None;
            let mut rendered_groups: HashSet<usize> = HashSet::new();

            for func_id in sorted_funcs {
                let func = program.functions.get(&func_id);
                let module_id = func_to_module[&func_id];
                let namespace_name = get_namespace(program, module_id);
                let merged_spec_modules = module_merged_specs
                    .get(&module_id)
                    .cloned()
                    .unwrap_or_default();
                let merged_module_ids: HashSet<usize> =
                    merged_spec_modules.iter().copied().collect();

                // Handle mutual group (skip if already rendered)
                if let Some(&group_id) = func_to_group.get(&func_id) {
                    if !rendered_groups.insert(group_id) {
                        continue; // Already rendered this mutual group
                    }
                    let group = &mutual_groups[&group_id];

                    // Ensure correct namespace is open
                    if current_namespace.as_ref() != Some(&namespace_name) {
                        if let Some(ref ns) = current_namespace {
                            file_output.push_str(&format!("end {}\n\n", ns));
                        }
                        file_output.push_str(&format!("namespace {}\n", namespace_name));
                        current_namespace = Some(namespace_name.clone());
                    }

                    file_output.push_str("mutual\n");
                    for &gfid in group {
                        let f = program.functions.get(&gfid);
                        let writer = LeanWriter::new(String::new());
                        let writer = render_function(
                            f,
                            gfid,
                            program,
                            &namespace_name,
                            writer,
                            &merged_module_ids,
                            module_id,
                            termination_measures.contains(&f.name),
                        );
                        let rendered = writer.into_inner();
                        if !rendered.trim().is_empty() {
                            file_output.push_str(&rendered);
                            file_output.push('\n');
                        }
                    }
                    file_output.push_str("end\n\n");
                } else {
                    // Non-mutual function: ensure correct namespace
                    if current_namespace.as_ref() != Some(&namespace_name) {
                        if let Some(ref ns) = current_namespace {
                            file_output.push_str(&format!("end {}\n\n", ns));
                        }
                        file_output.push_str(&format!("namespace {}\n", namespace_name));
                        current_namespace = Some(namespace_name.clone());
                    }

                    let writer = LeanWriter::new(String::new());
                    let writer = render_function(
                        func,
                        func_id,
                        program,
                        &namespace_name,
                        writer,
                        &merged_module_ids,
                        module_id,
                        termination_measures.contains(&func.name),
                    );
                    let rendered = writer.into_inner();
                    if !rendered.trim().is_empty() {
                        file_output.push_str(&rendered);
                        file_output.push('\n');
                    }
                    // Frame lemmas (§5.4, Phase 4) — before any
                    // `attribute [irreducible]` from the equation block.
                    file_output.push_str(&render_frame_lemmas(program, func_id));
                    // `irreducible_defs` gate: equation/projection lemmas +
                    // `attribute [irreducible]`, right after the def.
                    file_output.push_str(&render_equation_lemmas(program, func_id));
                }
            }

            // Recomposition lemmas for decomposed `.aborts` bodies (must come
            // after both the `.aborts` def and its segment defs).
            for &module_id in &ordered_scc {
                let namespace_name = get_namespace(program, module_id);
                let mut theorems = render_decompose_theorems(program, module_id, &namespace_name);
                theorems.push_str(&render_aborts_bundles(program, module_id));
                theorems.push_str(&render_ensures_bundles(program, module_id));
                if theorems.is_empty() {
                    continue;
                }
                if current_namespace.as_ref() != Some(&namespace_name) {
                    if let Some(ref ns) = current_namespace {
                        file_output.push_str(&format!("end {}\n\n", ns));
                    }
                    file_output.push_str(&format!("namespace {}\n", namespace_name));
                    current_namespace = Some(namespace_name.clone());
                }
                file_output.push_str(&theorems);
            }

            // Close the last open namespace
            if let Some(ref ns) = current_namespace {
                if !file_output.ends_with("\n\n") {
                    file_output.push('\n');
                }
                file_output.push_str(&format!("end {}\n\n", ns));
            }
        } else {
            // ------------------------------------------------------------------
            // Singleton SCC: original per-module rendering
            // ------------------------------------------------------------------
            for &module_id in &ordered_scc {
                let namespace_name = get_namespace(program, module_id);

                let merged_spec_modules: Vec<usize> =
                    impl_to_specs.get(&module_id).cloned().unwrap_or_default();

                // Collect function names from imported modules sharing this namespace
                let mut imported_same_namespace_funcs: HashSet<String> = HashSet::new();
                for &imp_id in &all_imports {
                    let imp_namespace = get_namespace(program, imp_id);
                    if imp_namespace == namespace_name {
                        for (_, func) in program.functions.iter() {
                            if func.module_id == imp_id {
                                imported_same_namespace_funcs
                                    .insert(escape::escape_identifier(&func.name));
                            }
                        }
                    }
                }

                let empty_native = NativeInfo {
                    struct_names: HashSet::new(),
                    function_names: HashSet::new(),
                    namespace: None,
                };
                let native_info = native_infos.get(&module_id).unwrap_or(&empty_native);

                file_output.push_str(&format!("namespace {}\n", namespace_name));

                // Native namespace re-export (structs + native functions)
                if let Some(ref ns) = native_info.namespace {
                    if ns != &namespace_name {
                        file_output.push_str(&format!("open {}\n", ns));
                        // Re-export native functions FIRST. Use `_root_.<ns>` so
                        // the lookup isn't shadowed by the struct abbrev (which
                        // we emit after). E.g. inside `namespace Table_M`, after
                        // `abbrev Table := Table.Table`, the bare name `Table`
                        // resolves to the struct, not the natives namespace.
                        let mut native_fn_set: std::collections::BTreeSet<String> =
                            native_info.function_names.iter().cloned().collect();
                        for (_, f) in program.functions.iter() {
                            if f.module_id == module_id && f.is_native {
                                native_fn_set.insert(escape::escape_identifier(&f.name));
                            }
                        }
                        let native_fn_names: Vec<String> = native_fn_set.into_iter().collect();
                        for func_name in &native_fn_names {
                            file_output.push_str(&format!(
                                "abbrev {} := @_root_.{}.{}\n",
                                func_name, ns, func_name
                            ));
                        }
                        // Then struct abbrevs. After this point, the bare `<S>`
                        // name in this scope refers to the struct (via abbrev).
                        let mut sorted_struct_names: Vec<&String> =
                            native_info.struct_names.iter().collect();
                        sorted_struct_names.sort();
                        for struct_name in sorted_struct_names {
                            file_output.push_str(&format!(
                                "abbrev {} := _root_.{}.{}\n",
                                struct_name, ns, struct_name
                            ));
                        }
                        if !native_info.struct_names.is_empty() || !native_fn_names.is_empty() {
                            file_output.push('\n');
                        }
                    }
                }
                file_output.push('\n');

                // Structs (skip if already in types file)
                if !has_types_file {
                    for (_, struct_def) in &program.structs {
                        if struct_def.module_id == module_id {
                            if native_info.struct_names.contains(&struct_def.name) {
                                continue;
                            }
                            let mut writer = LeanWriter::new(String::new());
                            render_struct(struct_def, program, &namespace_name, &mut writer);
                            file_output.push_str(&writer.into_inner());
                        }
                    }
                }

                // Functions
                let all_module_ids: Vec<usize> = std::iter::once(module_id)
                    .chain(merged_spec_modules.iter().copied())
                    .collect();

                let merged_module_ids: HashSet<usize> =
                    merged_spec_modules.iter().copied().collect();

                let module_funcs: Vec<usize> = program
                    .functions
                    .iter()
                    .filter(|(_, f)| all_module_ids.contains(&f.module_id))
                    .map(|(id, _)| id)
                    .collect();

                let sorted_funcs = topological_sort_functions(&module_funcs, program);

                let mut mutual_funcs = Vec::new();
                for &func_id in &sorted_funcs {
                    let func = program.functions.get(&func_id);
                    if func.mutual_group_id.is_some() {
                        mutual_funcs.push(func_id);
                    }
                }

                let mut mutual_groups: BTreeMap<usize, Vec<usize>> = BTreeMap::new();
                for &func_id in &mutual_funcs {
                    let func = program.functions.get(&func_id);
                    let group_id = func
                        .mutual_group_id
                        .expect("mutual func must have group id");
                    mutual_groups.entry(group_id).or_default().push(func_id);
                }

                let func_to_group: HashMap<usize, usize> = mutual_funcs
                    .iter()
                    .map(|&fid| {
                        let gid = program.functions.get(&fid).mutual_group_id.unwrap();
                        (fid, gid)
                    })
                    .collect();

                let mut rendered_groups: HashSet<usize> = HashSet::new();
                // Track rendered function names to skip duplicates from merged spec modules.
                // When both impl and spec modules define a function with the same name,
                // keep the impl version (rendered first in topo order) and skip the spec duplicate.
                let mut rendered_func_names: HashSet<String> = HashSet::new();
                let natives_path = output_dir
                    .join(&program.modules.get(module_id).package_name)
                    .join(format!(
                        "{}Natives.lean",
                        get_namespace_file_stem(program, module_id)
                    ));

                for func_id in sorted_funcs {
                    let func = program.functions.get(&func_id);
                    if !all_module_ids.contains(&func.module_id) {
                        continue;
                    }
                    if func.is_native && natives_path.exists() {
                        continue;
                    }
                    let escaped = escape::escape_identifier(&func.name);
                    let final_rendered_name = escaped.clone();
                    if native_info.function_names.contains(&final_rendered_name) {
                        continue;
                    }
                    if imported_same_namespace_funcs.contains(&final_rendered_name) {
                        continue;
                    }
                    if must_skip_function(func) {
                        continue;
                    }
                    // Skip duplicate functions from merged spec modules
                    if !rendered_func_names.insert(func.name.clone()) {
                        continue;
                    }

                    if let Some(&group_id) = func_to_group.get(&func_id) {
                        if rendered_groups.insert(group_id) {
                            let group = &mutual_groups[&group_id];
                            file_output.push_str("mutual\n");
                            for &gfid in group {
                                let f = program.functions.get(&gfid);
                                let writer = LeanWriter::new(String::new());
                                let writer = render_function(
                                    f,
                                    gfid,
                                    program,
                                    &namespace_name,
                                    writer,
                                    &merged_module_ids,
                                    module_id,
                                    termination_measures.contains(&f.name),
                                );
                                let rendered = writer.into_inner();
                                if !rendered.trim().is_empty() {
                                    file_output.push_str(&rendered);
                                    file_output.push('\n');
                                }
                            }
                            file_output.push_str("end\n\n");
                        }
                    } else {
                        let writer = LeanWriter::new(String::new());
                        let writer = render_function(
                            func,
                            func_id,
                            program,
                            &namespace_name,
                            writer,
                            &merged_module_ids,
                            module_id,
                            termination_measures.contains(&func.name),
                        );
                        let rendered = writer.into_inner();
                        if !rendered.trim().is_empty() {
                            file_output.push_str(&rendered);
                            file_output.push('\n');
                        }
                        // Frame lemmas (§5.4, Phase 4) — before any
                        // `attribute [irreducible]` from the equation block.
                        file_output.push_str(&render_frame_lemmas(program, func_id));
                        // `irreducible_defs` gate: equation/projection lemmas
                        // + `attribute [irreducible]`, right after the def.
                        file_output.push_str(&render_equation_lemmas(program, func_id));
                    }
                }

                // Recomposition lemmas for decomposed `.aborts` bodies.
                file_output.push_str(&render_decompose_theorems(
                    program,
                    module_id,
                    &namespace_name,
                ));
                file_output.push_str(&render_aborts_bundles(program, module_id));
                file_output.push_str(&render_ensures_bundles(program, module_id));

                if !file_output.ends_with("\n\n") {
                    file_output.push('\n');
                }

                file_output.push_str(&format!("end {}\n\n", namespace_name));
            }
        }

        // Write the file
        let first_mid = ordered_scc[0];
        let (file_pkg, file_stem) = &module_to_file[&first_mid];
        let file_path = format!("{}/{}.lean", file_pkg, file_stem);
        let full_path = output_dir.join(&file_path);

        write_if_changed(&full_path, &file_output, written)?;
    }

    // Generate Correctness files: for each module with ensures/requires defs,
    // emit theorems that call the user's proof (or sorry as placeholder).
    generate_correctness_files(
        program,
        output_dir,
        &module_to_file,
        &user_sources_dir,
        user_package_name,
        written,
    )?;

    Ok(())
}

/// Generate Correctness/<file_stem>.lean files containing proof obligation
/// theorems for all ensures/requires defs.
///
/// If the user has a proof file `Proofs/<file_stem>Proofs.lean`, the theorem
/// calls the user's proof: `exact <proof_ns>.<name>_proof <args>`.
/// Otherwise the theorem body is `sorry`.
fn generate_correctness_files(
    program: &Program,
    output_dir: &Path,
    module_to_file: &HashMap<ModuleID, (String, String)>,
    user_sources_dir: &Path,
    user_package_name: Option<&str>,
    written: &mut WrittenFiles,
) -> anyhow::Result<()> {
    use super::type_renderer::type_to_string_with_params;

    // Build set of valid packages (those that have lean_lib entries in the lakefile).
    // A spec package is excluded from lean_libs if ANY of its modules merge into
    // an impl module (same logic as backend.rs). Detect by checking if any module
    // with that package name appears in spec_to_impl.
    let spec_pkg_excluded: HashSet<String> = {
        let mut excluded = HashSet::new();
        for (&mid, _) in &program.spec_to_impl {
            let m = program.modules.get(mid);
            excluded.insert(m.package_name.clone());
        }
        excluded
    };
    let valid_packages: HashSet<String> = module_to_file
        .values()
        .map(|(pkg, _)| pkg.clone())
        .filter(|pkg| !spec_pkg_excluded.contains(pkg))
        .filter(|pkg| pkg != "Prelude")
        .collect();

    // Collect spec functions grouped by (file_pkg, file_stem)
    // Store function IDs + namespace rather than references for borrow checker simplicity.
    struct SpecEntry {
        namespace: String,
        func_id: usize,
    }
    let mut spec_funcs_by_file: HashMap<(String, String), Vec<SpecEntry>> = HashMap::new();

    // Build lookup maps for finding impl .aborts functions.
    // (module_id, func_name) → func_id for direct module-based lookup.
    let mut func_by_module_name: HashMap<(ModuleID, &str), usize> = HashMap::new();
    // func_name → Vec<(module_id, func_id)> for name-based search across modules.
    let mut funcs_by_name: HashMap<&str, Vec<(ModuleID, usize)>> = HashMap::new();
    for (fid, func) in program.functions.iter() {
        func_by_module_name.insert((func.module_id, &func.name), fid);
        funcs_by_name
            .entry(&func.name)
            .or_default()
            .push((func.module_id, fid));
    }

    // Build a set of spec package names for filtering impl functions.
    let spec_packages: HashSet<&str> = program
        .modules
        .iter()
        .filter(|(_, m)| is_spec_package(&m.package_name))
        .map(|(_, m)| m.package_name.as_str())
        .collect();

    // Build a map from (module_id, base_spec_name) → list of precondition function names.
    // Includes both .asserts_cond and .requires functions.
    let mut asserts_cond_by_base: HashMap<(ModuleID, String), Vec<String>> = HashMap::new();
    for (_fid, func) in program.functions.iter() {
        let pos = func
            .name
            .find(".asserts_cond")
            .or_else(|| func.name.find(".requires"));
        if let Some(pos) = pos {
            let base = func.name[..pos].to_string();
            asserts_cond_by_base
                .entry((func.module_id, base))
                .or_default()
                .push(func.name.clone());
        }
    }
    // Sort each list so output is deterministic (asserts_cond, asserts_cond_1, asserts_cond_2, ...)
    for conds in asserts_cond_by_base.values_mut() {
        conds.sort();
    }

    for (fid, func) in program.functions.iter() {
        let is_spec = func.name.contains(".ensures")
            || func.name.contains(".requires")
            || (func.name.contains(".aborts") && func.name.contains("_spec."));
        if !is_spec {
            continue;
        }
        // Bundle/segmentation helpers hoisted off a spec face
        // (`<spec>.aborts.atom_k`, `<spec>.ensures.seg_k`, obligation defs)
        // are decompose_aborts side-cars, not proof obligations.
        if func.name.contains(".atom_") || func.name.contains(".seg_") || func.name.contains(".ob_")
        {
            continue;
        }
        // Resolve spec module → impl module for merged spec packages.
        // Try direct lookup first, then resolve through spec_to_impl.
        let (file_pkg, file_stem) = if let Some(entry) = module_to_file.get(&func.module_id) {
            entry.clone()
        } else if let Some(&impl_mid) = program.spec_to_impl.get(&func.module_id) {
            if let Some(entry) = module_to_file.get(&impl_mid) {
                entry.clone()
            } else {
                continue;
            }
        } else {
            continue;
        };
        // Skip if the file's package doesn't have a lean_lib (orphan spec modules)
        if !valid_packages.contains(&file_pkg) {
            continue;
        }
        // Only generate correctness for the user's own packages, not dependencies
        if let Some(user_pkg) = user_package_name {
            let module = program.modules.get(func.module_id);
            let is_user_pkg = module.package_name == user_pkg
                || module
                    .package_name
                    .to_lowercase()
                    .ends_with(&format!("{}specs", user_pkg.to_lowercase()));
            if !is_user_pkg {
                continue;
            }
        }
        let resolved_mid = program
            .spec_to_impl
            .get(&func.module_id)
            .copied()
            .unwrap_or(func.module_id);
        // Use the resolved module's namespace for the correctness file
        let namespace = get_namespace(program, resolved_mid);
        spec_funcs_by_file
            .entry((file_pkg, file_stem))
            .or_default()
            .push(SpecEntry {
                namespace,
                func_id: fid,
            });
    }

    let correctness_dir = output_dir.join("Correctness");
    // Clean stale correctness files from previous runs
    if correctness_dir.exists() {
        fs::remove_dir_all(&correctness_dir)?;
    }
    fs::create_dir_all(&correctness_dir)?;

    for ((file_pkg, file_stem), spec_funcs) in &spec_funcs_by_file {
        let correctness_path = correctness_dir.join(format!("{}.lean", file_stem));

        // Check if user has a proof file at sources/lean/Proofs/<file_stem>Proofs.lean
        // If so, scan it for available theorem names to know which obligations are proved.
        let proofs_file = user_sources_dir
            .join("Proofs")
            .join(format!("{}Proofs.lean", file_stem));
        let has_proofs = proofs_file.exists();
        // Proof namespace convention: <file_stem>_proofs
        let proof_ns = format!("{}_proofs", file_stem);
        // Set of theorem names available in the proof file.
        // Tracks both plain names ("insert_spec_ensures") and namespace-qualified
        // names ("Enter_market.insert_spec_ensures") for multi-namespace files.
        let available_proofs: HashSet<String> = if has_proofs {
            let content = fs::read_to_string(&proofs_file).unwrap_or_default();
            let mut proofs = HashSet::new();
            let mut current_proof_ns: Option<String> = None;
            for line in content.lines() {
                let trimmed = line.trim();
                if trimmed.starts_with("namespace ") {
                    let ns = trimmed[10..].trim().to_string();
                    // Skip the outer proof namespace
                    if ns != proof_ns {
                        current_proof_ns = Some(ns);
                    }
                } else if trimmed.starts_with("end ") {
                    let ns = trimmed[4..].trim();
                    if current_proof_ns.as_deref() == Some(ns) {
                        current_proof_ns = None;
                    }
                } else if trimmed.starts_with("theorem ") || trimmed.starts_with("def ") {
                    let rest = if trimmed.starts_with("theorem ") {
                        &trimmed[8..]
                    } else {
                        &trimmed[4..]
                    };
                    if let Some(name) = rest.split_whitespace().next() {
                        proofs.insert(name.to_string());
                        if let Some(ref ns) = current_proof_ns {
                            proofs.insert(format!("{}.{}", ns, name));
                        }
                    }
                }
            }
            proofs
        } else {
            HashSet::new()
        };

        // Collect impl module imports needed for aborts theorems that reference impl functions.
        let mut impl_imports: HashSet<String> = HashSet::new();

        // Build theorem body first, then prepend imports (since impl_imports are discovered during body generation).
        let mut body = String::new();
        // Also build starter proof stubs for the user file
        let mut starter_body = String::new();

        // Sort spec functions by (namespace, name) for deterministic grouped output
        let mut sorted_entries: Vec<&SpecEntry> = spec_funcs.iter().collect();
        sorted_entries.sort_by(|a, b| {
            (&a.namespace, &program.functions.get(&a.func_id).name)
                .cmp(&(&b.namespace, &program.functions.get(&b.func_id).name))
        });

        let mut current_ns: Option<&str> = None;
        let mut all_namespaces: Vec<String> = Vec::new();
        let mut starter_emitted: HashSet<String> = HashSet::new();
        let mut starter_ns: Option<&str> = None;
        // Pre-compute: does this file have multiple namespaces?
        let is_multi_ns = {
            let mut ns_set: HashSet<&str> = HashSet::new();
            for entry in &sorted_entries {
                ns_set.insert(&entry.namespace);
            }
            ns_set.len() > 1
        };
        for entry in &sorted_entries {
            let func = program.functions.get(&entry.func_id);
            let namespace = &entry.namespace;
            let escaped_name = escape::escape_identifier(&func.name);
            let type_param_names: Vec<String> = func
                .signature
                .type_params
                .iter()
                .map(|tp| escape::escape_identifier(tp))
                .collect();

            // Open/switch namespace as needed
            if current_ns != Some(namespace.as_str()) {
                if let Some(ns) = current_ns {
                    body.push_str(&format!("end {}\n\n", ns));
                }
                body.push_str(&format!("namespace {}\n\n", namespace));
                current_ns = Some(namespace);
                if !all_namespaces.contains(namespace) {
                    all_namespaces.push(namespace.clone());
                }
            }

            // Check if user has proved this specific theorem.
            // For multi-namespace files, the proof is scoped under its namespace
            // (e.g., proof_ns.Enter_market.enter_market_with_emode_spec_aborts).
            let flat_name = escaped_name.replace('.', "_");
            let this_proved = if is_multi_ns {
                let qualified = format!("{}.{}", namespace, flat_name);
                available_proofs.contains(&qualified)
            } else {
                available_proofs.contains(&flat_name)
            };
            let is_aborts = func.name.contains(".aborts");

            body.push_str(&format!("theorem {}_proved", escaped_name));

            // Type parameters with constraints
            for tp in &type_param_names {
                if tp == "U" {
                    body.push_str(&format!(" ({} : Type) [HasRealOps {}]", tp, tp));
                } else {
                    body.push_str(&format!(
                        " ({} : Type) [BEq {}] [LawfulBEq {}] [Inhabited {}]",
                        tp, tp, tp, tp
                    ));
                }
            }
            // Bag-universe binders: the goal references bag-using functions whose
            // signatures now carry `[HasCode BagU T]`, so the obligation must
            // bind the same instances. Union the spec function's own
            // `fn_bagu_params` with those of the impl it proves (resolved via
            // spec_to_impl + the `_spec` name strip) — the spec `.ensures` face
            // need not transitively reach the bag op, but the impl always does.
            {
                let mut bagu_idx: std::collections::BTreeSet<u16> = program
                    .fn_bagu_params
                    .get(&entry.func_id)
                    .cloned()
                    .unwrap_or_default();
                let base = func
                    .name
                    .split_once(".aborts")
                    .or_else(|| func.name.split_once(".ensures"))
                    .or_else(|| func.name.split_once(".requires"))
                    .map(|(b, _)| b)
                    .unwrap_or(func.name.as_str());
                let impl_base = base.strip_suffix("_spec").unwrap_or(base);
                if let Some(&impl_mid) = program.spec_to_impl.get(&func.module_id) {
                    for cand in [impl_base.to_string(), format!("{}.aborts", impl_base)] {
                        if let Some(&fid) = func_by_module_name.get(&(impl_mid, cand.as_str())) {
                            if let Some(idx) = program.fn_bagu_params.get(&fid) {
                                bagu_idx.extend(idx);
                            }
                        }
                    }
                }
                for &i in &bagu_idx {
                    if let Some(tp) = type_param_names.get(i as usize) {
                        body.push_str(&format!(" [HasCode BagU {}]", tp));
                    }
                }
            }

            // Value parameters (from the spec function)
            let mut param_names: Vec<String> = Vec::new();
            for p in &func.signature.parameters {
                let escaped_param = escape::escape_identifier(&p.name);
                let type_str = type_to_string_with_params(
                    &p.param_type,
                    program,
                    Some(namespace),
                    Some(&type_param_names),
                );
                body.push_str(&format!(" ({} : {})", escaped_param, type_str));
                param_names.push(escaped_param);
            }

            // Extra proof params carried by the spec function via the
            // loop-invariant entry cascade (e.g. `hpre : <impl>.precond …`).
            // Emit them on the obligation and forward them ONLY to the spec /
            // impl references in the goal — NOT to `requires` / `asserts_cond`
            // references, which don't take them.
            let proof_param_names: Vec<String> = {
                for pp in &func.signature.proof_params {
                    body.push_str(&format!(
                        " ({} : {})",
                        pp.name,
                        super::function_renderer::proof_param_type_string(pp, func, program)
                    ));
                }
                func.signature
                    .proof_params
                    .iter()
                    .map(|pp| pp.name.clone())
                    .collect()
            };

            // Theorem statement
            // For aborts with asserts_cond defs:
            //   asserts_cond₁ → ... → ¬impl.aborts (proves impl doesn't abort when preconditions hold)
            // For aborts without asserts: ¬spec.aborts
            // For ensures/requires: direct proposition
            let base_spec_name = if is_aborts {
                func.name.strip_suffix(".aborts").map(|s| s.to_string())
            } else if let Some(pos) = func.name.find(".ensures") {
                Some(func.name[..pos].to_string())
            } else if let Some(pos) = func.name.find(".requires") {
                Some(func.name[..pos].to_string())
            } else {
                None
            };
            let asserts_conds: Option<&Vec<String>> = base_spec_name.as_ref().and_then(|base| {
                let key = (func.module_id, base.clone());
                asserts_cond_by_base.get(&key)
            });
            let has_preconditions = asserts_conds.is_some_and(|c| !c.is_empty());
            let has_asserts = is_aborts && has_preconditions;

            // For aborts with asserts, find the corresponding impl .aborts function.
            // Spec name "insert_spec.aborts" → impl name "insert.aborts" (strip _spec).
            // Find impl by: (1) spec_to_impl if available, (2) name-based search in non-spec packages
            // matching the spec's base package name.
            let impl_aborts_info: Option<(String, String, Vec<(String, String)>, Vec<String>)> =
                if has_asserts {
                    let base = base_spec_name.as_ref().expect("checked");
                    let impl_base = base.strip_suffix("_spec").unwrap_or(base);
                    let impl_func_name = format!("{}.aborts", impl_base);

                    // Try spec_to_impl first
                    let mut found_impl: Option<(ModuleID, usize)> = program
                        .spec_to_impl
                        .get(&func.module_id)
                        .and_then(|&impl_mid| {
                            func_by_module_name
                                .get(&(impl_mid, impl_func_name.as_str()))
                                .map(|&fid| (impl_mid, fid))
                        });

                    // Validate: if found, check that the impl .aborts function's first
                    // param type matches the spec function's first param type. This catches
                    // cases where spec_to_impl maps to the wrong module (e.g., referral_specs
                    // maps to referral, but the spec actually targets user_rebates).
                    if let Some((_, fid)) = found_impl {
                        let impl_func = program.functions.get(&fid);
                        if let (Some(spec_first), Some(impl_first)) = (
                            func.signature.parameters.first(),
                            impl_func.signature.parameters.first(),
                        ) {
                            if spec_first.param_type != impl_first.param_type {
                                found_impl = None;
                            }
                        }
                    }

                    // Fallback: search by function name across non-spec packages.
                    // Match by: (1) base package name (MoveSTLSpecs → movestl matches MoveSTL),
                    // AND (2) spec module name ends with impl module name (move_stl_skip_list ends with skip_list).
                    // This avoids cross-module matches (e.g., skip_list's borrow_spec matching linked_table's borrow).
                    if found_impl.is_none() {
                        if let Some(candidates) = funcs_by_name.get(impl_func_name.as_str()) {
                            let spec_mod = program.modules.get(func.module_id);
                            let spec_pkg_base = spec_mod
                                .package_name
                                .to_lowercase()
                                .replace('_', "")
                                .trim_end_matches("specs")
                                .to_string();
                            for &(cand_mid, cand_fid) in candidates {
                                let cand_mod = program.modules.get(cand_mid);
                                if spec_packages.contains(cand_mod.package_name.as_str()) {
                                    continue;
                                }
                                let cand_pkg_base =
                                    cand_mod.package_name.to_lowercase().replace('_', "");
                                if cand_pkg_base != spec_pkg_base {
                                    continue;
                                }
                                // Check module name match: spec module name should end with
                                // the impl module name (e.g., move_stl_skip_list ends with skip_list).
                                let spec_name = &spec_mod.name;
                                let cand_name = &cand_mod.name;
                                if spec_name == cand_name
                                    || spec_name.ends_with(&format!("_{}", cand_name))
                                {
                                    found_impl = Some((cand_mid, cand_fid));
                                    break;
                                }
                            }

                            // If module name match failed, try parameter type matching.
                            // This handles cross-module spec targets (e.g., referral_specs
                            // targeting user_rebates functions where types differ from referral).
                            if found_impl.is_none() {
                                if let Some(spec_first_type) =
                                    func.signature.parameters.first().map(|p| &p.param_type)
                                {
                                    for &(cand_mid, cand_fid) in candidates {
                                        let cand_mod = program.modules.get(cand_mid);
                                        if spec_packages.contains(cand_mod.package_name.as_str()) {
                                            continue;
                                        }
                                        let cand_func = program.functions.get(&cand_fid);
                                        if let Some(cand_first) =
                                            cand_func.signature.parameters.first()
                                        {
                                            if &cand_first.param_type == spec_first_type {
                                                found_impl = Some((cand_mid, cand_fid));
                                                break;
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }

                    if let Some((impl_mid, fid)) = found_impl {
                        let impl_ns = get_namespace(program, impl_mid);
                        let impl_func = program.functions.get(&fid);
                        let impl_params: Vec<(String, String)> = impl_func
                            .signature
                            .parameters
                            .iter()
                            .map(|p| {
                                let name = escape::escape_identifier(&p.name);
                                let ty = type_to_string_with_params(
                                    &p.param_type,
                                    program,
                                    Some(&impl_ns),
                                    Some(&type_param_names),
                                );
                                (name, ty)
                            })
                            .collect();
                        if let Some((impl_pkg, impl_stem)) = module_to_file.get(&impl_mid) {
                            let import = format!("{}.{}", impl_pkg, impl_stem);
                            impl_imports.insert(import);
                        }
                        let impl_proof_params: Vec<String> = impl_func
                            .signature
                            .proof_params
                            .iter()
                            .map(|pp| pp.name.clone())
                            .collect();
                        Some((
                            impl_ns,
                            escape::escape_identifier(&impl_func_name),
                            impl_params,
                            impl_proof_params,
                        ))
                    } else {
                        None
                    }
                } else {
                    None
                };

            if has_asserts && impl_aborts_info.is_some() {
                // Implication form: asserts_cond₁ → ... → ¬impl_ns.impl.aborts params
                // This proves the implementation doesn't abort when preconditions hold.
                let (ref impl_ns, ref impl_escaped_name, ref impl_params, ref impl_proof_params) =
                    impl_aborts_info.as_ref().expect("checked");
                // World-mode: the SPEC face always carries machine-injected
                // binders (`__world`, `__ghost_*`), but the impl `.aborts`
                // only carries the ones its own cone was threaded with
                // (world_mode replaces ghost slots with `__world`, and an
                // impl that never touches the World has neither). Machine
                // params are name-stable across spec/impl, so filter them by
                // presence; user params keep positional forwarding.
                let impl_has_machine_param = |n: &str| impl_params.iter().any(|(p, _)| p == n);
                body.push_str(" :");
                let conds = asserts_conds.expect("checked above");
                for cond_name in conds.iter() {
                    body.push_str("\n    ");
                    let escaped_cond = escape::escape_identifier(cond_name);
                    body.push_str(&escaped_cond);
                    for tp in &type_param_names {
                        body.push_str(&format!(" {}", tp));
                    }
                    for pn in &param_names {
                        body.push_str(&format!(" {}", pn));
                    }
                    body.push_str(" →");
                }
                body.push_str(&format!("\n    {}.{}", impl_ns, impl_escaped_name));
                for tp in &type_param_names {
                    body.push_str(&format!(" {}", tp));
                }
                // Use the theorem's own parameter names (from the spec function),
                // not the impl function's parameter names which may differ.
                for pn in &param_names {
                    if pn.starts_with("__") && !impl_has_machine_param(pn) {
                        continue;
                    }
                    body.push_str(&format!(" {}", pn));
                }
                // Forward only the proof params the impl itself carries: a
                // spec-boundary-only hypothesis (e.g. `hdinv`) is a binder on
                // the obligation, not an argument of the impl.
                for pn in &proof_param_names {
                    if impl_proof_params.contains(pn) {
                        body.push_str(&format!(" {}", pn));
                    }
                }
                body.push_str(" = Option.none");
            } else if is_aborts {
                body.push_str(&format!(" :\n    {}", escaped_name));
                for tp in &type_param_names {
                    body.push_str(&format!(" {}", tp));
                }
                for pn in &param_names {
                    body.push_str(&format!(" {}", pn));
                }
                for pn in &proof_param_names {
                    body.push_str(&format!(" {}", pn));
                }
                body.push_str(" = Option.none");
            } else {
                body.push_str(" :");
                if has_preconditions {
                    let conds = asserts_conds.expect("has_preconditions checked");
                    for cond_name in conds.iter() {
                        body.push_str("\n    ");
                        let escaped_cond = escape::escape_identifier(cond_name);
                        body.push_str(&escaped_cond);
                        for tp in &type_param_names {
                            body.push_str(&format!(" {}", tp));
                        }
                        for pn in &param_names {
                            body.push_str(&format!(" {}", pn));
                        }
                        body.push_str(" →");
                    }
                }
                body.push_str(&format!("\n    {}", escaped_name));
                for tp in &type_param_names {
                    body.push_str(&format!(" {}", tp));
                }
                for pn in &param_names {
                    body.push_str(&format!(" {}", pn));
                }
                for pn in &proof_param_names {
                    body.push_str(&format!(" {}", pn));
                }
            }

            if this_proved {
                let proof_ref = if is_multi_ns {
                    format!("{}.{}.{}", proof_ns, namespace, flat_name)
                } else {
                    format!("{}.{}", proof_ns, flat_name)
                };
                body.push_str(&format!(" :=\n  {}", proof_ref));
                for tp in &type_param_names {
                    body.push_str(&format!(" {}", tp));
                }
                for pn in &param_names {
                    body.push_str(&format!(" {}", pn));
                }
                for pn in &proof_param_names {
                    body.push_str(&format!(" {}", pn));
                }
                body.push_str("\n\n");
            } else if func.name.contains(".requires") {
                // A `requires` face's obligation is vacuous by construction:
                // every spec `requires` (including this one) is also a
                // hypothesis of the goal, so the conclusion is literally one
                // of the antecedents. Self-close instead of emitting a sorry.
                body.push_str(" := by\n  intros\n  assumption\n\n");
            } else {
                body.push_str(" := by\n  sorry\n\n");
            }

            // Stored-value invariant preservation goals (`_data_inv`): the
            // assert half of the data-invariant discipline. One theorem per
            // (spec, slot, updated-container result component), stated over
            // the same binders as the spec's obligation, concluding that the
            // impl's result still satisfies `TypedMap.all`. Proved by the
            // user's Proofs file when a matching theorem exists, else sorry.
            if let Some(goals) = program.data_inv_goals.get(&entry.func_id) {
                for goal in goals {
                    let goal_base = flat_name
                        .strip_suffix("_aborts")
                        .expect("data_inv goals are keyed by `_spec.aborts` functions");
                    let goal_flat = format!("{}_data_inv{}", goal_base, goal.goal_suffix);
                    let impl_func = program.functions.get(&goal.impl_fn_id);
                    let impl_ns = get_namespace(program, impl_func.module_id);
                    if let Some((impl_pkg, impl_stem)) = module_to_file.get(&impl_func.module_id) {
                        impl_imports.insert(format!("{}.{}", impl_pkg, impl_stem));
                    }
                    let goal_proved = if is_multi_ns {
                        available_proofs.contains(&format!("{}.{}", namespace, goal_flat))
                    } else {
                        available_proofs.contains(&goal_flat)
                    };
                    body.push_str(&format!("theorem {}_proved", goal_flat));
                    for tp in &type_param_names {
                        body.push_str(&format!(
                            " ({} : Type) [BEq {}] [LawfulBEq {}] [Inhabited {}]",
                            tp, tp, tp, tp
                        ));
                    }
                    if let Some(idx) = program.fn_bagu_params.get(&goal.impl_fn_id) {
                        for &i in idx {
                            if let Some(tp) = type_param_names.get(i as usize) {
                                body.push_str(&format!(" [HasCode BagU {}]", tp));
                            }
                        }
                    }
                    for p in &func.signature.parameters {
                        let escaped_param = escape::escape_identifier(&p.name);
                        let type_str = type_to_string_with_params(
                            &p.param_type,
                            program,
                            Some(namespace),
                            Some(&type_param_names),
                        );
                        body.push_str(&format!(" ({} : {})", escaped_param, type_str));
                    }
                    for pp in &func.signature.proof_params {
                        body.push_str(&format!(
                            " ({} : {})",
                            pp.name,
                            super::function_renderer::proof_param_type_string(pp, func, program)
                        ));
                    }
                    body.push_str(" :");
                    if let Some(conds) = asserts_conds {
                        for cond_name in conds.iter() {
                            body.push_str("\n    ");
                            body.push_str(&escape::escape_identifier(cond_name));
                            for tp in &type_param_names {
                                body.push_str(&format!(" {}", tp));
                            }
                            for pn in &param_names {
                                body.push_str(&format!(" {}", pn));
                            }
                            body.push_str(" →");
                        }
                    }
                    let k = type_to_string_with_params(&goal.key_type, program, None, None);
                    let v = type_to_string_with_params(&goal.value_type, program, None, None);
                    body.push_str(&format!(
                        "\n    TypedMap.all ({}) ({}) {} (({}.{}",
                        k,
                        v,
                        goal.pred,
                        impl_ns,
                        escape::escape_identifier(&impl_func.name)
                    ));
                    for tp in &type_param_names {
                        body.push_str(&format!(" {}", tp));
                    }
                    for pn in param_names.iter().take(goal.n_args) {
                        body.push_str(&format!(" {}", pn));
                    }
                    // Forward the impl's own proof params (e.g. `hpre`) when the
                    // spec obligation carries a same-named binder.
                    for pp in &impl_func.signature.proof_params {
                        if proof_param_names.contains(&pp.name) {
                            body.push_str(&format!(" {}", pp.name));
                        }
                    }
                    body.push_str(&format!("){}{})", goal.proj_expr, goal.map_tail));
                    if goal_proved {
                        let proof_ref = if is_multi_ns {
                            format!("{}.{}.{}", proof_ns, namespace, goal_flat)
                        } else {
                            format!("{}.{}", proof_ns, goal_flat)
                        };
                        body.push_str(&format!(" :=\n  {}", proof_ref));
                        for tp in &type_param_names {
                            body.push_str(&format!(" {}", tp));
                        }
                        for pn in &param_names {
                            body.push_str(&format!(" {}", pn));
                        }
                        for pn in &proof_param_names {
                            body.push_str(&format!(" {}", pn));
                        }
                        body.push_str("\n\n");
                    } else {
                        body.push_str(" := by\n  sorry\n\n");
                    }
                }
            }

            // World-mode preservation goals (unified-backend design §7,
            // Phase 5): same discipline as `_data_inv` above, but concluding
            // `Prover.World.World.allDf` over the impl's RESULT WORLD at the
            // invariant's parent uid. Proved by the user's Proofs file when a
            // matching theorem exists, else sorry.
            if let Some(goals) = program.data_inv_world_goals.get(&entry.func_id) {
                for goal in goals {
                    let goal_base = flat_name
                        .strip_suffix("_aborts")
                        .expect("data_inv goals are keyed by `_spec.aborts` functions");
                    let goal_flat = format!("{}_data_inv{}", goal_base, goal.goal_suffix);
                    let impl_func = program.functions.get(&goal.impl_fn_id);
                    let impl_ns = get_namespace(program, impl_func.module_id);
                    if let Some((impl_pkg, impl_stem)) = module_to_file.get(&impl_func.module_id) {
                        impl_imports.insert(format!("{}.{}", impl_pkg, impl_stem));
                    }
                    let goal_proved = if is_multi_ns {
                        available_proofs.contains(&format!("{}.{}", namespace, goal_flat))
                    } else {
                        available_proofs.contains(&goal_flat)
                    };
                    body.push_str(&format!("theorem {}_proved", goal_flat));
                    for tp in &type_param_names {
                        body.push_str(&format!(
                            " ({} : Type) [BEq {}] [LawfulBEq {}] [Inhabited {}]",
                            tp, tp, tp, tp
                        ));
                    }
                    if let Some(idx) = program.fn_bagu_params.get(&goal.impl_fn_id) {
                        for &i in idx {
                            if let Some(tp) = type_param_names.get(i as usize) {
                                body.push_str(&format!(" [HasCode BagU {}]", tp));
                            }
                        }
                    }
                    for p in &func.signature.parameters {
                        let escaped_param = escape::escape_identifier(&p.name);
                        let type_str = type_to_string_with_params(
                            &p.param_type,
                            program,
                            Some(namespace),
                            Some(&type_param_names),
                        );
                        body.push_str(&format!(" ({} : {})", escaped_param, type_str));
                    }
                    for pp in &func.signature.proof_params {
                        body.push_str(&format!(
                            " ({} : {})",
                            pp.name,
                            super::function_renderer::proof_param_type_string(pp, func, program)
                        ));
                    }
                    body.push_str(" :");
                    body.push_str(&format!(
                        "\n    Prover.World.World.allDf (({}.{}",
                        impl_ns,
                        escape::escape_identifier(&impl_func.name)
                    ));
                    for tp in &type_param_names {
                        body.push_str(&format!(" {}", tp));
                    }
                    for pn in param_names.iter().take(goal.n_args) {
                        body.push_str(&format!(" {}", pn));
                    }
                    for pp in &impl_func.signature.proof_params {
                        if proof_param_names.contains(&pp.name) {
                            body.push_str(&format!(" {}", pp.name));
                        }
                    }
                    body.push_str(&format!(
                        "){}) (World.uidNat {}) {}",
                        goal.world_proj, goal.parent_expr, goal.pred
                    ));
                    if goal_proved {
                        let proof_ref = if is_multi_ns {
                            format!("{}.{}.{}", proof_ns, namespace, goal_flat)
                        } else {
                            format!("{}.{}", proof_ns, goal_flat)
                        };
                        body.push_str(&format!(" :=\n  {}", proof_ref));
                        for tp in &type_param_names {
                            body.push_str(&format!(" {}", tp));
                        }
                        for pn in &param_names {
                            body.push_str(&format!(" {}", pn));
                        }
                        for pn in &proof_param_names {
                            body.push_str(&format!(" {}", pn));
                        }
                        body.push_str("\n\n");
                    } else {
                        body.push_str(" := by\n  sorry\n\n");
                    }
                }
            }

            // Build starter proof stub: theorem flat_name (params) : proposition := by sorry
            // Skip if already emitted (dedup for merged modules with shared specs)
            let starter_key = if is_multi_ns {
                format!("{}.{}", namespace, flat_name)
            } else {
                flat_name.clone()
            };
            if !starter_emitted.contains(&starter_key) {
                starter_emitted.insert(starter_key);
                // For multi-namespace files, scope each theorem in its namespace
                if is_multi_ns && starter_ns != Some(namespace.as_str()) {
                    if let Some(ns) = starter_ns {
                        starter_body.push_str(&format!("end {}\n\n", ns));
                    }
                    starter_body.push_str(&format!(
                        "namespace {}\nopen _root_.{}\n\n",
                        namespace, namespace
                    ));
                    starter_ns = Some(namespace);
                }
                starter_body.push_str(&format!("theorem {}", flat_name));
                for tp in &type_param_names {
                    starter_body.push_str(&format!(
                        " ({} : Type) [BEq {}] [LawfulBEq {}] [Inhabited {}]",
                        tp, tp, tp, tp
                    ));
                }
                if let Some(idx) = program.fn_bagu_params.get(&entry.func_id) {
                    for &i in idx {
                        if let Some(tp) = type_param_names.get(i as usize) {
                            starter_body.push_str(&format!(" [HasCode BagU {}]", tp));
                        }
                    }
                }
                for p in &func.signature.parameters {
                    let escaped_param = escape::escape_identifier(&p.name);
                    let type_str = type_to_string_with_params(
                        &p.param_type,
                        program,
                        Some(namespace),
                        Some(&type_param_names),
                    );
                    starter_body.push_str(&format!(" ({} : {})", escaped_param, type_str));
                }
                for pp in &func.signature.proof_params {
                    starter_body.push_str(&format!(
                        " ({} : {})",
                        pp.name,
                        super::function_renderer::proof_param_type_string(pp, func, program)
                    ));
                }
                starter_body.push_str(" :");
                if has_asserts && impl_aborts_info.is_some() {
                    // Aborts with asserts + impl: asserts_cond₁ → ... → impl.aborts = false
                    let conds = asserts_conds.expect("has_asserts checked");
                    for cond_name in conds.iter() {
                        let escaped_cond = escape::escape_identifier(cond_name);
                        starter_body.push_str(&format!("\n    {}", escaped_cond));
                        for tp in &type_param_names {
                            starter_body.push_str(&format!(" {}", tp));
                        }
                        for pn in &param_names {
                            starter_body.push_str(&format!(" {}", pn));
                        }
                        starter_body.push_str(" →");
                    }
                    let (ref impl_ns, ref impl_escaped_name, _, ref impl_proof_params) =
                        impl_aborts_info.as_ref().expect("checked");
                    starter_body.push_str(&format!("\n    {}.{}", impl_ns, impl_escaped_name));
                    for tp in &type_param_names {
                        starter_body.push_str(&format!(" {}", tp));
                    }
                    for pn in &param_names {
                        starter_body.push_str(&format!(" {}", pn));
                    }
                    for pn in &proof_param_names {
                        if impl_proof_params.contains(pn) {
                            starter_body.push_str(&format!(" {}", pn));
                        }
                    }
                    starter_body.push_str(" = Option.none");
                } else if is_aborts {
                    // Aborts without asserts (or no impl found): spec.aborts = false
                    starter_body.push_str(&format!("\n    {}", escaped_name));
                    for tp in &type_param_names {
                        starter_body.push_str(&format!(" {}", tp));
                    }
                    for pn in &param_names {
                        starter_body.push_str(&format!(" {}", pn));
                    }
                    for pn in &proof_param_names {
                        starter_body.push_str(&format!(" {}", pn));
                    }
                    starter_body.push_str(" = Option.none");
                } else {
                    // Ensures/requires: add precondition hypotheses if present
                    if has_preconditions {
                        let conds = asserts_conds.expect("has_preconditions checked");
                        for cond_name in conds.iter() {
                            let escaped_cond = escape::escape_identifier(cond_name);
                            starter_body.push_str(&format!("\n    {}", escaped_cond));
                            for tp in &type_param_names {
                                starter_body.push_str(&format!(" {}", tp));
                            }
                            for pn in &param_names {
                                starter_body.push_str(&format!(" {}", pn));
                            }
                            starter_body.push_str(" →");
                        }
                    }
                    starter_body.push_str(&format!("\n    {}", escaped_name));
                    for tp in &type_param_names {
                        starter_body.push_str(&format!(" {}", tp));
                    }
                    for pn in &param_names {
                        starter_body.push_str(&format!(" {}", pn));
                    }
                    for pn in &proof_param_names {
                        starter_body.push_str(&format!(" {}", pn));
                    }
                }
                starter_body.push_str(" := by\n  sorry\n\n");
            } // end dedup check
        }
        // Close final starter namespace
        if is_multi_ns {
            if let Some(ns) = starter_ns {
                starter_body.push_str(&format!("end {}\n\n", ns));
            }
        }
        // Close final namespace
        if let Some(ns) = current_ns {
            body.push_str(&format!("end {}\n", ns));
        }

        // Assemble final output: imports + body
        let mut output = String::new();
        output.push_str("-- Correctness proof obligations generated by the translator.\n");
        if !has_proofs {
            output.push_str(&format!(
                "-- Provide proofs in sources/lean/Proofs/{}Proofs.lean (namespace {}).\n",
                file_stem, proof_ns
            ));
        }
        output.push_str(&format!("import {}.{}\n", file_pkg, file_stem));
        // Import impl modules referenced in aborts theorems
        let mut sorted_impl_imports: Vec<&String> = impl_imports.iter().collect();
        sorted_impl_imports.sort();
        for imp in sorted_impl_imports {
            output.push_str(&format!("import {}\n", imp));
        }
        if has_proofs {
            output.push_str(&format!("import Proofs.{}Proofs\n", file_stem));
        }
        output.push('\n');
        output.push_str(&body);

        write_if_changed(&correctness_path, &output, written)?;

        // Generate starter proof file in sources/lean/ if it doesn't exist yet.
        // This gives users a starting point with all theorem signatures and sorry bodies.
        // Only generate starter proof files for the user's own package, not framework deps.
        let is_user_pkg = user_package_name.map_or(true, |name| {
            let pkg_lower = file_pkg.to_lowercase().replace('_', "");
            let name_lower = name.to_lowercase().replace('_', "");
            pkg_lower == name_lower
                || pkg_lower == format!("{}specs", name_lower)
                || pkg_lower.starts_with(&name_lower)
        });
        let starter_path = user_sources_dir
            .join("Proofs")
            .join(format!("{}Proofs.lean", file_stem));
        if is_user_pkg && !starter_path.exists() && !starter_body.is_empty() {
            fs::create_dir_all(user_sources_dir.join("Proofs"))?;
            let mut starter_output = String::new();
            starter_output.push_str(&format!("import {}.{}\n", file_pkg, file_stem));
            // Add impl imports needed for aborts theorems
            let mut sorted_impl_imports2: Vec<&String> = impl_imports.iter().collect();
            sorted_impl_imports2.sort();
            for imp in sorted_impl_imports2 {
                starter_output.push_str(&format!("import {}\n", imp));
            }
            starter_output.push_str("\nset_option maxRecDepth 4096\n");
            starter_output.push_str("set_option maxHeartbeats 400000\n\n");
            starter_output.push_str(&format!("namespace {}\n\n", proof_ns));
            // For single-namespace files, open the spec namespace
            if !is_multi_ns {
                for ns in &all_namespaces {
                    starter_output.push_str(&format!("open _root_.{}\n", ns));
                }
                starter_output.push('\n');
            }
            // For multi-namespace files, each theorem is scoped in its own
            // namespace block (emitted in starter_body), so no global open needed.
            starter_output.push_str(&starter_body);
            starter_output.push_str(&format!("end {}\n", proof_ns));
            fs::write(&starter_path, &starter_output)?;
        }
    }

    Ok(())
}

/// Copy native package implementations from lemmas directory.
fn copy_native_packages(
    program: &Program,
    output_dir: &Path,
    written: &mut WrittenFiles,
) -> anyhow::Result<()> {
    let lemmas_dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("lemmas");
    let mut copied_modules = HashSet::new();

    // Hand-written `Prelude/*.lean` files in `lemmas/Prelude/` reach into
    // a fixed set of natives via `import` (e.g. `Prelude/Quantifiers.lean`
    // imports `MoveStdlib.IntegerNatives` and `MoveStdlib.MoveVectorNatives`
    // for spec-level helpers). Those imports stand regardless of which Move
    // modules end up in `program.modules` — the Prelude is a static
    // dependency.
    //
    // Without this preliminary pass, when a small `--test` run prunes its
    // module closure tightly enough that `std::integer` doesn't surface as
    // a target, the main loop below skips copying `IntegerNatives.lean` and
    // every prelude file that imports it then fails to elaborate
    // (`bad import 'MoveStdlib.IntegerNatives'`), cascading into every
    // generated module that imports the prelude. The per-test driver then
    // can't load its module's `.olean` and the runner reports
    // `UNKNOWN_INVARIANT_VIOLATION_ERROR`.
    //
    // Copy these unconditionally. The list mirrors the Prelude's actual
    // imports of `<Pkg>.<Mod>Natives` files; if the Prelude grows new
    // such imports, add them here too.
    const PRELUDE_REQUIRED_NATIVES: &[(&str, &str)] = &[
        ("MoveStdlib", "MoveVectorNatives"),
        ("MoveStdlib", "IntegerNatives"),
    ];
    for (package_name, file_stem) in PRELUDE_REQUIRED_NATIVES {
        let module_key = format!("{}::{}", package_name, file_stem);
        if copied_modules.contains(&module_key) {
            continue;
        }
        let source_path = lemmas_dir.join(format!("natives/{}/{}.lean", package_name, file_stem));
        if !source_path.exists() {
            continue;
        }
        let dest_path = output_dir
            .join(package_name)
            .join(format!("{}.lean", file_stem));
        // Native `.aborts` companions are authored as `Option MoveAbort`
        // directly in the `lemmas/` source files; copy verbatim.
        copy_if_changed(&source_path, &dest_path, written)?;
        copied_modules.insert(module_key);
    }

    for (&module_id, module) in program.modules.iter() {
        let module_key = format!("{}::{}", module.package_name, module.name);
        if copied_modules.contains(&module_key) {
            continue;
        }

        let module_has_content = program.structs.values().any(|s| s.module_id == module_id)
            || program
                .functions
                .iter()
                .any(|(_, f)| f.module_id == module_id);
        if !module_has_content {
            continue;
        }

        let capitalized_name = escape::capitalize_first(&module.name);
        let namespace = get_namespace(program, module_id);
        let file_stem = get_namespace_file_stem(program, module_id);

        let possible_files = [
            format!("natives/{}/{}.lean", module.package_name, capitalized_name),
            format!(
                "natives/{}/{}Natives.lean",
                module.package_name, capitalized_name
            ),
            format!("natives/{}/{}Natives.lean", module.package_name, namespace),
            format!("natives/{}/{}Natives.lean", module.package_name, file_stem),
        ];

        let source_path = possible_files
            .iter()
            .map(|f| lemmas_dir.join(f))
            .find(|p| p.exists());

        let source_path = match source_path {
            Some(p) => p,
            None => continue,
        };

        let dest_path = output_dir
            .join(&module.package_name)
            .join(format!("{}Natives.lean", file_stem));

        // Rewrite cross-namespace references for renamed namespaces.
        // Native files reference *other* modules by their original namespace
        // name (e.g. `MoveOption.MoveOption`). When that other module's
        // namespace was renamed via `_M`, the qualified reference must be
        // rewritten too. The natives file's OWN `namespace <Foo>` line is
        // left intact so the abbrev re-export bridge in the generated file
        // still works.
        // Build the rename map for cross-namespace references. Apply for
        // every module whose namespace was renamed via the namespace-vs-struct
        // collision rule. Hand-written natives that reference `<old>.<X>` need
        // the qualified prefix updated to the new namespace, since the OLD
        // namespace is no longer where `<X>` lives (the struct, in particular,
        // has moved).
        let mut renames: Vec<(String, String)> = Vec::new();
        for (&other_mid, override_ns) in program.namespace_overrides.iter() {
            if other_mid == module_id {
                continue;
            }
            let other_module = program.modules.get(other_mid);
            let original = escape::module_name_to_namespace(&other_module.name);
            if &original == override_ns {
                continue;
            }
            // Only rewrite the namespace-collision form (`*_M`); cross-package
            // overrides predate this rename and natives never referred to those.
            if !override_ns.ends_with(escape::NAMESPACE_COLLISION_SUFFIX) {
                continue;
            }
            renames.push((original, override_ns.clone()));
        }
        renames.sort();

        // Native `.aborts` companions are authored as `Option MoveAbort`
        // directly in the `lemmas/` source files, so files are copied verbatim
        // (only namespace-collision renames still need a content rewrite).
        if renames.is_empty() {
            copy_if_changed(&source_path, &dest_path, written)?;
        } else {
            let content =
                rewrite_namespace_references(&fs::read_to_string(&source_path)?, &renames);
            write_if_changed(&dest_path, &content, written)?;
        }
        copied_modules.insert(module_key);
    }

    Ok(())
}

/// Rewrite cross-namespace references in a hand-written native file. For each
/// `(old, new)` pair, replaces qualified references `old.<word>` with
/// `new.<word>`. Skips the file's own `namespace <old>` declaration so the
/// abbrev re-export bridge keeps working.
fn rewrite_namespace_references(content: &str, renames: &[(String, String)]) -> String {
    let mut out = String::with_capacity(content.len());
    for line in content.split_inclusive('\n') {
        let trimmed = line.trim_start();
        // Don't rewrite `namespace <old>` / `end <old>` declarations: those
        // are the file's own namespace and the bridge in the generated file
        // depends on them keeping the original name.
        let is_ns_decl = trimmed.starts_with("namespace ") || trimmed.starts_with("end ");
        let mut rewritten = String::from(line);
        if !is_ns_decl {
            for (old, new) in renames {
                rewritten = replace_qualified_prefix(&rewritten, old, new);
            }
        }
        out.push_str(&rewritten);
    }
    out
}

/// Replace occurrences of `<old>.<ident-start>` with `<new>.<ident-start>`,
/// only matching when `<old>` appears as a stand-alone identifier (preceded by
/// non-identifier or start-of-input). Avoids substring matches inside longer
/// identifiers like `Foobar.X` when `old` is `oo`.
fn replace_qualified_prefix(s: &str, old: &str, new: &str) -> String {
    let needle = format!("{}.", old);
    let bytes = s.as_bytes();
    let mut out = String::with_capacity(s.len());
    let mut i = 0;
    while i < bytes.len() {
        if bytes[i..].starts_with(needle.as_bytes()) {
            let prev_ok = i == 0 || {
                let c = bytes[i - 1] as char;
                !(c.is_alphanumeric() || c == '_' || c == '.')
            };
            if prev_ok {
                out.push_str(new);
                out.push('.');
                i += needle.len();
                continue;
            }
        }
        let ch = s[i..].chars().next().unwrap();
        out.push(ch);
        i += ch.len_utf8();
    }
    out
}
