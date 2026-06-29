// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Augment IR struct definitions with `dynamic_fields*` ghost fields
//! that the corresponding hand-written native Lean file declares.
//!
//! Upstream `DynamicFieldAnalysisProcessor` only computes
//! `DynamicFieldInfo` for verified-or-inlined-or-reachable functions
//! (the Boogie pipeline's accessibility gate). For projects with no
//! verified specs (typical Lean-only clients like cetus-stl), every
//! function falls under that gate, the analysis is empty for everyone,
//! and `program_builder` adds no `dynamic_fields` ghost field to the
//! struct. The hand-written native (`Skip_listNatives.lean`,
//! `MoveSTL_Linked_tableNatives.lean`, etc.) declares the ghost field
//! anyway — without a matching IR-side field, `Pack` calls are
//! arity-mismatched and the Phase 2 dynamic-field rewriting pass
//! skips the struct entirely (so `Dynamic_field.borrow` etc. survive
//! to the rendered Lean output, where they're undefined).
//!
//! This module reads the natives in `lemmas/natives/<package>/` and
//! parses out each struct's `dynamic_fields*` field count, then
//! appends placeholder fields to any IR struct whose IR ghost-field
//! count is below the native's. The placeholder type is a
//! parameterised `List (K × V)` shape recognised by
//! `dynamic_field_rewriting::build_df_field_map`; the rewrite pass
//! pulls actual K/V types from each call site, so the placeholder
//! field type only needs to match the structural pattern, not the
//! exact element types.
//!
//! Exception: if `program_builder` already added a ghost field for
//! this struct (the analysis was populated, e.g. via the hardcoded
//! `Table` special case or a regular accessibility-passing path),
//! we leave it alone — the IR-side type is already accurate.

use intermediate_theorem_format::{Field, Program, Type};
use std::collections::HashMap;
use std::fs;
use std::path::Path;

/// Parse a single `lemmas/natives/<package>/<file>.lean` file and
/// return, per struct name declared in it, the count of fields whose
/// name is `dynamic_fields` or `dynamic_fields_<N>`.
///
/// The parser is line-based and intentionally minimal: it tracks
/// `namespace` only to avoid mis-attributing fields when a file
/// declares multiple structs in different namespaces (rare in
/// practice; framework natives usually carry one namespace per file).
/// Returns map keyed by bare struct name (no namespace prefix); the
/// caller matches that against `program.structs.<id>.name`.
pub fn parse_native_ghost_field_counts(file_path: &Path) -> HashMap<String, usize> {
    let mut counts: HashMap<String, usize> = HashMap::new();
    let Ok(content) = fs::read_to_string(file_path) else {
        return counts;
    };

    let mut current_struct: Option<String> = None;
    for line in content.lines() {
        let trimmed = line.trim();

        // Comment / blank lines: nothing to do, but keep current_struct
        // (a blank line inside a structure body shouldn't end it).
        if trimmed.is_empty() || trimmed.starts_with("--") {
            continue;
        }

        // `structure NAME (...) where` opens a new struct block.
        if let Some(rest) = trimmed.strip_prefix("structure ") {
            let name_end = rest
                .find(|c: char| c.is_whitespace() || c == '(' || c == '{' || c == ':')
                .unwrap_or(rest.len());
            let struct_name = rest[..name_end].trim().to_string();
            if !struct_name.is_empty() {
                current_struct = Some(struct_name);
            }
            continue;
        }

        // Lines that close a structure body or move us to top-level.
        // `deriving`, `instance`, `def`, `theorem`, `end`, `namespace`,
        // `import` all end the current struct.
        let leading_word_ends_struct = matches!(
            trimmed.split_whitespace().next(),
            Some(
                "deriving"
                    | "instance"
                    | "def"
                    | "theorem"
                    | "end"
                    | "namespace"
                    | "import"
                    | "set_option"
                    | "structure"
            )
        );

        // Unindented non-empty lines that aren't field continuations also
        // end the struct. The indentation check handles the more general
        // case where a file's struct body is followed by a non-keyword
        // top-level form we don't recognise.
        let is_unindented = !line.starts_with(' ') && !line.starts_with('\t');

        if leading_word_ends_struct {
            current_struct = None;
            continue;
        }
        if is_unindented {
            current_struct = None;
            continue;
        }

        // Within a struct: look for `<field_name> :` lines, count those
        // whose name starts with `dynamic_fields`.
        if let Some(struct_name) = current_struct.as_ref() {
            let Some(colon_pos) = trimmed.find(':') else {
                continue;
            };
            let field_name = trimmed[..colon_pos].trim();
            if field_name == "dynamic_fields" || field_name.starts_with("dynamic_fields_") {
                *counts.entry(struct_name.clone()).or_insert(0) += 1;
            }
        }
    }
    counts
}

/// Walk every module in `program`, locate its hand-written native
/// file under `lemmas_dir`, parse the per-struct ghost-field counts,
/// and append placeholder ghost fields to any matching IR struct
/// whose IR ghost-field count is below the native's.
///
/// The placeholder type is `List (K × V)` with `K = TypeParameter(0)`
/// and `V = TypeParameter(0)` (or `TypeParameter(1)` when the struct
/// has at least two type parameters). The rewrite pass identifies
/// the field by its `dynamic_fields*` name and pulls actual K / V
/// types from each call site — the placeholder field type only
/// needs to satisfy `Type::Vector(Type::Tuple([_, _]))` so
/// `build_df_field_map` records the field as a ghost.
///
/// Lookup of native files mirrors `copy_native_packages` in
/// `program_renderer.rs`: try `<Capitalized>.lean`,
/// `<Capitalized>Natives.lean`, `<Namespace>Natives.lean`,
/// `<FileStem>Natives.lean`. The first that exists wins; otherwise
/// the module has no native and we leave its structs alone.
pub fn augment_structs_with_native_ghost_fields(program: &mut Program, lemmas_dir: &Path) {
    use crate::escape;
    use crate::renderer::{compute_namespace_overrides, get_namespace, get_namespace_file_stem};

    // Compute namespace overrides up-front so `get_namespace_file_stem`
    // returns the post-collision-resolution form (e.g.
    // `MoveSTL_Linked_table` instead of `Linked_table`) — the
    // hand-written native files use the resolved name in their
    // filenames, and `render_to_directory` re-runs this pass when it
    // begins so a second computation is idempotent.
    compute_namespace_overrides(program);

    // Per-module: parse the native file (if any) once and cache the
    // struct -> ghost count map.
    let mut module_ghost_counts: HashMap<usize, HashMap<String, usize>> = HashMap::new();
    for (&module_id, module) in program.modules.iter() {
        let capitalized_name = escape::capitalize_first(&module.name);
        let namespace = get_namespace(program, module_id);
        let file_stem = get_namespace_file_stem(program, module_id);

        let candidate_paths = [
            format!("natives/{}/{}.lean", module.package_name, capitalized_name),
            format!(
                "natives/{}/{}Natives.lean",
                module.package_name, capitalized_name
            ),
            format!("natives/{}/{}Natives.lean", module.package_name, namespace),
            format!("natives/{}/{}Natives.lean", module.package_name, file_stem),
        ];
        let Some(native_path) = candidate_paths
            .iter()
            .map(|p| lemmas_dir.join(p))
            .find(|p| p.exists())
        else {
            continue;
        };
        let counts = parse_native_ghost_field_counts(&native_path);
        if !counts.is_empty() {
            module_ghost_counts.insert(module_id, counts);
        }
    }

    if module_ghost_counts.is_empty() {
        return;
    }

    let struct_ids: Vec<usize> = program.structs.iter().map(|(&id, _)| id).collect();
    for sid in struct_ids {
        let s = program.structs.get(sid);
        let module_id = s.module_id;
        let struct_name = s.name.clone();
        let ir_ghost_count = s
            .fields
            .iter()
            .filter(|f| f.name == "dynamic_fields" || f.name.starts_with("dynamic_fields_"))
            .count();

        let Some(per_module) = module_ghost_counts.get(&module_id) else {
            continue;
        };
        let Some(&native_ghost_count) = per_module.get(&struct_name) else {
            continue;
        };
        if native_ghost_count <= ir_ghost_count {
            continue;
        }

        let num_type_params = s.type_params.len();
        let s_mut = program.structs.get_mut(sid);
        for i in ir_ghost_count..native_ghost_count {
            let field_name = if native_ghost_count == 1 {
                "dynamic_fields".to_string()
            } else {
                format!("dynamic_fields_{}", i)
            };
            // Placeholder type. Type params are picked from the
            // struct's own type-parameter slots when available so the
            // ghost-type's `max_type_param_index` agrees with the
            // struct's arity (existing IR code in `program_builder`
            // gates on `max_idx <= num_struct_params`; the augmenter
            // doesn't go through that gate but should produce a
            // similarly well-formed shape).
            let key_slot = if num_type_params >= 1 {
                Type::TypeParameter(0)
            } else {
                Type::Bool
            };
            let value_slot = if num_type_params >= 2 {
                Type::TypeParameter(1)
            } else if num_type_params >= 1 {
                Type::TypeParameter(0)
            } else {
                Type::Bool
            };
            s_mut.fields.push(Field {
                name: field_name,
                field_type: Type::Vector(Box::new(Type::Tuple(vec![key_slot, value_slot]))),
            });
        }
    }
}
