// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Import collection pass

use crate::data::{Dependable, ModuleID, Program};
use crate::Function;
use std::collections::HashSet;

/// Check if a package name indicates it's a spec package.
/// Matches patterns like "Specs", "FooSpecs", "specs", etc.
fn is_spec_package(package_name: &str) -> bool {
    let lower = package_name.to_lowercase();
    lower == "specs" || lower.ends_with("specs")
}

pub fn collect_imports(program: &mut Program) {
    let module_imports: Vec<_> = program
        .modules
        .iter_ids()
        .map(|id| (id, collect_module_imports(program, id)))
        .collect();

    for (module_id, imports) in module_imports {
        program.modules.get_mut(module_id).required_imports = imports;
    }
}

fn collect_module_imports(program: &Program, module_id: ModuleID) -> Vec<ModuleID> {
    let struct_deps = collect_struct_imports(program, module_id);
    let function_deps = collect_function_imports(program, module_id);

    let current_module = program.modules.get(module_id);

    // Get the set of synthetic module IDs to exclude from imports
    // (e.g., the TypedMap module created by dynamic field rewriting —
    // TypedMap.lean is already a Prelude submodule, so no import needed)
    let synthetic_module_ids: HashSet<ModuleID> = program
        .typed_map_functions
        .as_ref()
        .map(|tm| tm.module_id)
        .into_iter()
        // The synthetic World module (world-mode) is likewise not a real
        // file: its call surface lives in Generated/World.lean, imported by
        // the renderer's world-usage injection.
        .chain(program.world_functions.as_ref().map(|w| w.module_id))
        .collect();

    let combined: HashSet<ModuleID> = struct_deps
        .into_iter()
        .chain(function_deps)
        .filter(|&m| {
            if m == module_id {
                return false;
            }
            if synthetic_module_ids.contains(&m) {
                return false;
            }
            // For same-named modules in different packages (impl vs spec),
            // the spec module may import the impl module, but not vice versa.
            // Loop invariants and specs are merged into the impl module's output
            // by the renderer, so we don't need this import.
            let other_module = program.modules.get(m);
            if other_module.name == current_module.name
                && other_module.package_name != current_module.package_name
            {
                // If current is impl (non-Specs) and other is spec, skip import
                // The spec's content will be merged by the renderer
                let current_is_spec = is_spec_package(&current_module.package_name);
                let other_is_spec = is_spec_package(&other_module.package_name);
                if !current_is_spec && other_is_spec {
                    return false;
                }
            }
            true
        })
        .collect();

    combined.into_iter().collect()
}

fn collect_struct_imports(program: &Program, module_id: ModuleID) -> HashSet<ModuleID> {
    program
        .structs
        .values()
        .filter(|s| s.module_id == module_id)
        .flat_map(|s| s.dependencies())
        .map(|sid| program.structs.get(sid).module_id)
        .collect()
}

fn collect_function_imports(program: &Program, module_id: ModuleID) -> HashSet<ModuleID> {
    // Only collect imports from base (Runtime) functions, not spec variants.
    // Spec variants (.requires, .ensures, etc.) are rendered in SpecDefs/Specs directories,
    // not in Impls. Including them here creates circular dependencies because spec functions
    // call back to the implementation they're specifying.
    program
        .functions
        .values()
        .filter(|f| f.module_id == module_id)
        .flat_map(|f| collect_from_function(program, f))
        .collect()
}

fn collect_from_function<'a>(
    program: &'a Program,
    function: &'a Function,
) -> impl Iterator<Item = ModuleID> + 'a {
    let sig_deps = function
        .signature
        .parameters
        .iter()
        .map(|p| &p.param_type)
        .chain(std::iter::once(&function.signature.return_type))
        .flat_map(|t| t.struct_ids())
        .map(|sid| program.structs.get(sid).module_id);

    let call_deps = function
        .body
        .calls()
        .map(move |fid| program.functions.get(&fid).module_id);

    let struct_deps = function
        .body
        .iter_struct_references()
        .chain(function.body.iter_type_struct_ids())
        .map(|sid| program.structs.get(sid).module_id);

    sig_deps.chain(call_deps).chain(struct_deps)
}
