// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Detect IR functions shadowed by hand-written natives.
//!
//! Some modules (e.g. `sui::coin`, `sui::balance`) have Move source that
//! gets fully translated to IR, but a hand-written Lean version lives at
//! `crates/move-prover-lean-backend/lemmas/natives/<Pkg>/<Module>Natives.lean`
//! and overrides the rendered IR. The renderer drops the IR-generated
//! `def`s for shadowed names, but analyses run before the renderer don't
//! know about that — they see the IR's `.aborts` companion (which returns
//! `Option MoveAbort` in test-mode) and emit callers' `match ... | some
//! __abort` accordingly. At elaboration time, the native's Bool-shape
//! `.aborts` wins and the match becomes a type mismatch.
//!
//! This pass scans the natives directory, finds each `def <name>` entry,
//! and marks any IR function whose `(module.name, name)` matches as
//! `is_native = true`. Downstream analyses (notably
//! [`compose_callee_aborts_option`]) gate Bool-vs-Option lifting on
//! `is_native`, so updating the flag here is enough to make the
//! generated callers match the native shape.

use crate::data::Program;
use std::collections::HashSet;
use std::path::{Path, PathBuf};

/// Locate the `lemmas/natives/` directory shipped with
/// `move-prover-lean-backend`. Returns `None` only if the layout has
/// drifted from what `PreludeManager::find_prelude_source_dir` expects.
fn find_natives_dir() -> Option<PathBuf> {
    // CARGO_MANIFEST_DIR for this crate is .../crates/intermediate-theorem-format.
    // The natives live at .../crates/move-prover-lean-backend/lemmas/natives.
    let manifest_dir = env!("CARGO_MANIFEST_DIR");
    let here = PathBuf::from(manifest_dir);
    let sibling = here.parent().map(|p| {
        p.join("move-prover-lean-backend")
            .join("lemmas")
            .join("natives")
    });
    if let Some(p) = sibling {
        if p.exists() {
            return Some(p);
        }
    }
    // Fallback: walk up from CWD.
    if let Ok(mut current) = std::env::current_dir() {
        loop {
            let candidate = current
                .join("crates")
                .join("move-prover-lean-backend")
                .join("lemmas")
                .join("natives");
            if candidate.exists() {
                return Some(candidate);
            }
            if !current.pop() {
                break;
            }
        }
    }
    None
}

/// Convenience: scan the auto-located natives directory and update the
/// program. No-op if the directory can't be found.
pub fn mark_native_shadowed_auto(program: &mut Program) {
    if let Some(dir) = find_natives_dir() {
        mark_native_shadowed(program, &dir);
    }
}

/// Walk every `*Natives.lean` under `natives_dir` and collect the function
/// names defined inside. Returned set is keyed by `(file_stem,
/// func_name)`, where `file_stem` is the file name without the
/// `Natives.lean` suffix (e.g. "Coin"). Matches the layout produced by
/// `module_name_to_namespace`.
fn collect_native_function_names(natives_dir: &Path) -> HashSet<(String, String)> {
    let mut out = HashSet::new();
    let Ok(packages) = std::fs::read_dir(natives_dir) else {
        return out;
    };
    for pkg_entry in packages.flatten() {
        if !pkg_entry.file_type().map(|t| t.is_dir()).unwrap_or(false) {
            continue;
        }
        let Ok(files) = std::fs::read_dir(pkg_entry.path()) else {
            continue;
        };
        for file_entry in files.flatten() {
            let path = file_entry.path();
            let Some(stem) = path
                .file_stem()
                .and_then(|s| s.to_str())
                .and_then(|s| s.strip_suffix("Natives"))
            else {
                continue;
            };
            let Ok(content) = std::fs::read_to_string(&path) else {
                continue;
            };
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
                } else if let Some(r) = stripped.strip_prefix("opaque ") {
                    r
                } else if let Some(r) = stripped.strip_prefix("axiom ") {
                    r
                } else {
                    continue;
                };
                let Some(name_end) = rest.find([' ', '(', ':', '{']) else {
                    continue;
                };
                out.insert((stem.to_string(), rest[..name_end].to_string()));
            }
        }
    }
    out
}

/// Map a Move module name like "coin" to the native file stem "Coin".
/// Matches `escape::module_name_to_namespace` for the simple case (which
/// is all the natives directory uses).
fn module_name_to_native_stem(name: &str) -> String {
    let mut chars = name.chars();
    match chars.next() {
        Some(c) => c.to_uppercase().chain(chars).collect(),
        None => String::new(),
    }
}

/// Mark every IR function whose `(module-stem, name)` matches a native
/// `def` as `is_native = true`. For each shadowed function, also normalize
/// its companion `.aborts` so the rest of the pipeline matches what the
/// renderer will actually emit:
///
/// - Mark the `.aborts` as `is_native = true` too.
/// - Set its return type to `Bool` and replace the body with `Bool(false)`,
///   so the option-shape composition in `compose_callee_aborts_option`
///   wraps calls to it with the Bool-to-Option lifter rather than emitting
///   an `Option`-shape `match` that would mismatch the hand-written native
///   Bool signature at elaboration time.
///
/// Idempotent; safe to call before any analysis that gates on `is_native`.
pub fn mark_native_shadowed(program: &mut Program, natives_dir: &Path) {
    use crate::data::types::Type;
    use crate::{Const, IRNode};

    let native_names = collect_native_function_names(natives_dir);
    if native_names.is_empty() {
        return;
    }

    // Collect shadowed function IDs first; their `.aborts` companions
    // live in the same module under "<name>.aborts" by convention.
    let mut shadowed: Vec<(usize, usize)> = Vec::new(); // (module_id, fid)
    let func_ids: Vec<usize> = program.functions.iter().map(|(id, _)| id).collect();
    for fid in &func_ids {
        let func = program.functions.get(fid);
        if func.is_native {
            continue;
        }
        let module_name = &program.modules.get(func.module_id).name;
        let stem = module_name_to_native_stem(module_name);
        if native_names.contains(&(stem, func.name.clone())) {
            shadowed.push((func.module_id, *fid));
        }
    }

    // Index functions by (module, name) for quick `.aborts` lookup.
    let by_module_name: std::collections::HashMap<(usize, String), usize> = program
        .functions
        .iter()
        .map(|(id, f)| ((f.module_id, f.name.clone()), id))
        .collect();

    for (module_id, fid) in shadowed {
        let aborts_name = {
            let func = program.functions.get(&fid);
            format!("{}.aborts", func.name)
        };
        program.functions.get_mut(fid).is_native = true;
        if let Some(&aborts_id) = by_module_name.get(&(module_id, aborts_name)) {
            let aborts = program.functions.get_mut(aborts_id);
            aborts.is_native = true;
            aborts.signature.return_type = Type::Bool;
            aborts.body = IRNode::Const(Const::Bool(false));
        }
    }
}
