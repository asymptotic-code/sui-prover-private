// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Lean backend entry point
//!
//! Takes TheoremProgram and renders to Lean files.
//! ZERO logic, pure rendering.

use crate::prelude::PreludeManager;
use crate::renderer::render_to_directory;
use crate::runtime::run_lake_build;
use crate::WrittenFiles;
use intermediate_theorem_format::validate_program;
use move_model::model::{FunId, GlobalEnv, QualifiedId};
use move_model::ty::Type as MoveType;
use move_stackless_bytecode::function_target_pipeline::FunctionTargetsHolder;
use stackless_to_intermediate::ProgramBuilder;
use std::fs;
use std::path::{Path, PathBuf};

/// Relative path from `from_dir` to `to` (both must exist), used to point
/// lake libs at the user's sources/lean directory from the output directory.
fn relative_path(from_dir: &Path, to: &Path) -> anyhow::Result<PathBuf> {
    let from = from_dir.canonicalize()?;
    let to = to.canonicalize()?;
    let mut from_comps = from.components().peekable();
    let mut to_comps = to.components().peekable();
    while let (Some(f), Some(t)) = (from_comps.peek(), to_comps.peek()) {
        if f != t {
            break;
        }
        from_comps.next();
        to_comps.next();
    }
    let mut rel = PathBuf::new();
    for _ in from_comps {
        rel.push("..");
    }
    for c in to_comps {
        rel.push(c.as_os_str());
    }
    Ok(rel)
}

/// Lean backend - translate IR to Lean
///
/// - `env`: The Move global environment
/// - `targets`: The function targets holder
/// - `output_dir`: Where to write generated Lean files (e.g., `<package>/output`)
/// - `package_dir`: The Move package root (e.g., `<package>/`), used to find user proofs in `sources/lean/`
pub async fn run_backend(
    env: &GlobalEnv,
    targets: &FunctionTargetsHolder,
    output_dir: &Path,
    package_dir: &Path,
    generate_only: bool,
) -> anyhow::Result<()> {
    run_backend_with_boogie_proven(
        env,
        targets,
        output_dir,
        package_dir,
        generate_only,
        &std::collections::HashSet::new(),
        Vec::new(),
    )
    .await
}

/// The Move-level ghost-native seed: per ghost-writing native, the `(K, V)`
/// marker pairs its spec declares. Computed by the caller from
/// `PackageTargets` (gated to markers declared by target-package specs) and
/// threaded through to `ProgramBuilder`. Empty = ghost threading is inert.
pub type GhostNativeSeed = Vec<(QualifiedId<FunId>, Vec<(MoveType, MoveType)>)>;

/// Like [`run_backend`] but lets the caller supply the set of bare spec
/// names marked `#[spec(prove, run_on="boogie")]`. Their correctness
/// obligations render as trusted `axiom`s instead of `theorem ... := by
/// sorry`. The caller computes the set from the authoritative
/// `PackageTargets` (the merged `FunctionTargetsHolder` is lossy in All mode).
pub async fn run_backend_with_boogie_proven(
    env: &GlobalEnv,
    targets: &FunctionTargetsHolder,
    output_dir: &Path,
    package_dir: &Path,
    generate_only: bool,
    boogie_proven_names: &std::collections::HashSet<String>,
    ghost_native_seed: GhostNativeSeed,
) -> anyhow::Result<()> {
    run_backend_inner(
        env,
        targets,
        output_dir,
        package_dir,
        generate_only,
        false, // test_mode: build with BuildMode::Spec (prune #[test] items)
        boogie_proven_names,
        ghost_native_seed,
    )
    .await
}

/// Like [`run_backend`] but lets the caller opt into the test-mode IR
/// pipeline (`Program::finalize_for_test`), which preserves `#[test]` items
/// and inline `IRNode::Abort` bodies. Used by `--test`.
pub async fn run_backend_with_options(
    env: &GlobalEnv,
    targets: &FunctionTargetsHolder,
    output_dir: &Path,
    package_dir: &Path,
    generate_only: bool,
    test_mode: bool,
    ghost_native_seed: GhostNativeSeed,
) -> anyhow::Result<()> {
    run_backend_inner(
        env,
        targets,
        output_dir,
        package_dir,
        generate_only,
        test_mode,
        &std::collections::HashSet::new(),
        ghost_native_seed,
    )
    .await
}

async fn run_backend_inner(
    env: &GlobalEnv,
    targets: &FunctionTargetsHolder,
    output_dir: &Path,
    package_dir: &Path,
    generate_only: bool,
    test_mode: bool,
    boogie_proven_names: &std::collections::HashSet<String>,
    ghost_native_seed: GhostNativeSeed,
) -> anyhow::Result<()> {
    let overall_start = std::time::Instant::now();

    // Lemmas dir holds hand-written `<...>Natives.lean` files. The
    // augmenter parses the natives' `dynamic_fields*` field
    // declarations and adds matching placeholder fields to IR structs
    // before `Program::finalize_*` runs the dynamic-field rewriting
    // pass. Without this, structs whose ghost fields the upstream
    // accessibility-gated `DynamicFieldAnalysisProcessor` failed to
    // record would emit arity-mismatched `Pack` calls and skip Phase 2
    // rewriting (so `Dynamic_field.borrow` etc. survive to the
    // rendered Lean output, where they're undefined).
    let lemmas_dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("lemmas");
    // Harvest the client's Lean termination declarations (`def <name>.loop_hyp` /
    // `def <name>.precond` headers in `sources/lean/*.lean`) so the generic
    // `thread_lean_terminations` pass can thread their hypotheses — name-free,
    // driven by what the client actually wrote.
    let lean_termination_decls =
        scan_lean_termination_decls(&package_dir.join("sources").join("lean"));
    // Extracted before the `move` closure below consumes `lean_termination_decls`.
    // Gates loop-invariant registration in the IR builder (see
    // `ProgramBuilder::with_loop_hyp_decls`): a Move `loop_inv` is honored only
    // when the client shipped a matching `loop_hyp`, else the loop degrades to
    // the plain sorry-termination default instead of dangling.
    let loop_hyp_decls = lean_termination_decls.loop_hyp.clone();
    let pre_finalize = move |program: &mut intermediate_theorem_format::Program| {
        crate::native_ghost_fields::augment_structs_with_native_ghost_fields(program, &lemmas_dir);
        program.lean_termination_decls = lean_termination_decls.clone();
        // World-mode ghost-slot suppression (unified-backend design Phase 5):
        // with the df store living in the threaded World, the build-time ghost
        // `dynamic_fields*` fields on generated structs are dead — drop them
        // (natives-declared structs keep theirs). Must run here (not in
        // finalize) because natives-file coverage needs `lemmas_dir`. Inert
        // off world-mode.
        if intermediate_theorem_format::analysis::world_threading::world_mode_enabled(program) {
            crate::native_ghost_fields::suppress_ghost_df_slots_world_mode(program, &lemmas_dir);
        }
    };

    // Run translation pipeline
    let build_start = std::time::Instant::now();
    let mut program = if test_mode {
        // Test-mode body shape: preserves `IRNode::Abort` inside bodies and
        // keeps `#[test]` items in the IR, then runs option-shape finalize.
        ProgramBuilder::new(env)
            .with_ghost_native_seed(ghost_native_seed)
            .with_loop_hyp_decls(loop_hyp_decls)
            .build_for_test_with_hook(targets, pre_finalize)
    } else {
        ProgramBuilder::new(env)
            .with_ghost_native_seed(ghost_native_seed)
            .with_loop_hyp_decls(loop_hyp_decls)
            .build_with_mode_and_hook(
                targets,
                intermediate_theorem_format::BuildMode::Spec,
                pre_finalize,
            )
    };
    eprintln!(
        "⏱ IR translation took: {}ms",
        build_start.elapsed().as_millis()
    );

    // Hybrid Boogie+Lean: specs marked `#[spec(prove, run_on="boogie")]` are
    // trusted to be proven by the Boogie backend. The caller passes their bare
    // Move function names (computed from the authoritative PackageTargets) so
    // the renderer emits a trusted `axiom` for their correctness obligations
    // instead of `theorem ... := by sorry`.
    program.boogie_proven_specs = boogie_proven_names.clone();
    if !program.boogie_proven_specs.is_empty() {
        eprintln!(
            "ℹ {} spec(s) marked run_on=\"boogie\" -> emitted as trusted axiom",
            program.boogie_proven_specs.len()
        );
    }

    // Validate IR before rendering (catches undefined variables, type mismatches, etc.)
    let validation_start = std::time::Instant::now();
    let validation_errors = validate_program(&program);
    if !validation_errors.is_empty() {
        eprintln!("\n⚠️  IR Validation Errors ({}):", validation_errors.len());
        for error in &validation_errors {
            eprintln!("  - {}", error);
        }
        eprintln!();
    }
    eprintln!(
        "⏱ IR validation took: {}ms",
        validation_start.elapsed().as_millis()
    );

    let setup_start = std::time::Instant::now();
    let mut written = WrittenFiles::new();
    fs::create_dir_all(output_dir)?;
    fs::create_dir_all(output_dir.join("Correctness"))?;

    // User files in sources/lean/{Proofs,Termination}/ are built by lake in
    // place (the lakefile points those libs' srcDir at sources/lean); nothing
    // is copied into the output tree. Legacy flat-layout files are migrated
    // into the subdirectories during rendering.
    let user_proofs_src = package_dir.join("sources").join("lean");

    // Delete inv_target functions from the program (they are hand-written in Lean)
    let datatype_invs: Vec<_> = targets.get_datatype_invs().into_iter().collect();
    for (_datatype_qid, fun_qid) in &datatype_invs {
        let func_env = env.get_function(**fun_qid);
        let func_name = env.symbol_pool().string(func_env.get_name()).to_string();
        let module_name = env
            .symbol_pool()
            .string(func_env.module_env.get_name().name())
            .to_string();
        let ids_to_delete: Vec<usize> = program
            .functions
            .iter()
            .filter(|(_, f)| f.name == func_name || f.name.starts_with(&format!("{}.", func_name)))
            .filter(|(_, f)| {
                let ir_module = program.modules.get(&f.module_id);
                ir_module.name == module_name
            })
            .map(|(id, _)| id)
            .collect();
        for id in ids_to_delete {
            program.functions.delete_function(id);
        }
    }

    // Copy Prelude files
    let prelude_manager = PreludeManager::new(output_dir.to_path_buf());
    prelude_manager.initialize(&mut written)?;

    // Get Prelude imports from actual files being copied
    let prelude_imports = prelude_manager.get_prelude_imports()?;
    eprintln!(
        "⏱ Setup (dirs, prelude) took: {}ms",
        setup_start.elapsed().as_millis()
    );

    // Collect all unique package names for the lakefile.
    // Exclude spec packages that get merged into their impl packages.
    // A spec module with package_name ending in "Specs" (or just "specs") is merged if there's a
    // corresponding impl module (same module name, package_name NOT ending in "Specs").
    let packages: Vec<String> = {
        // Helper to check if a package is a spec package
        fn is_spec_package(package_name: &str) -> bool {
            let lower = package_name.to_lowercase();
            lower == "specs" || lower.ends_with("specs")
        }

        // First, build the spec_to_impl mapping (same logic as program_renderer.rs)
        let mut spec_packages_to_exclude: std::collections::HashSet<String> =
            std::collections::HashSet::new();

        for (_mid, m) in &program.modules {
            if is_spec_package(&m.package_name) {
                let spec_base = m
                    .package_name
                    .to_lowercase()
                    .trim_end_matches("specs")
                    .trim_end_matches('_')
                    .to_string();
                // Check if there's a corresponding impl module
                for (_, other) in &program.modules {
                    let spec_module_base = m.name.trim_end_matches("_specs");
                    if (other.name == m.name || other.name == spec_module_base)
                        && !is_spec_package(&other.package_name)
                        && (spec_base.is_empty()
                            || other.package_name.to_lowercase().replace('_', "")
                                == spec_base.replace('_', ""))
                    {
                        spec_packages_to_exclude.insert(m.package_name.clone());
                        break;
                    }
                }
            }
        }

        program
            .modules
            .values()
            .map(|m| m.package_name.clone())
            .filter(|pkg| !spec_packages_to_exclude.contains(pkg))
            // Exclude "Prelude" — it's already hardcoded in the lakefile
            .filter(|pkg| pkg != "Prelude")
            .collect::<std::collections::BTreeSet<_>>()
            .into_iter()
            .collect()
    };

    // Render to Lean - each package gets its own directory
    // Read the package name from Move.toml to identify user's own packages
    let user_package_name = {
        let move_toml = package_dir.join("Move.toml");
        if move_toml.exists() {
            let content = fs::read_to_string(&move_toml).unwrap_or_default();
            content
                .lines()
                .find(|l| l.trim().starts_with("name"))
                .and_then(|l| l.split('=').nth(1))
                .map(|s| s.trim().trim_matches('"').to_string())
        } else {
            None
        }
    };

    let render_start = std::time::Instant::now();
    render_to_directory(
        &mut program,
        output_dir,
        &prelude_imports,
        package_dir,
        user_package_name.as_deref(),
        &mut written,
    )?;
    eprintln!(
        "⏱ Rendering to Lean took: {}ms",
        render_start.elapsed().as_millis()
    );

    // Re-render after the first pass: rendering may have generated starter
    // proof files in sources/lean/Proofs/ that weren't present initially, and
    // correctness files must detect them.
    if user_proofs_src.exists() {
        render_to_directory(
            &mut program,
            output_dir,
            &prelude_imports,
            package_dir,
            user_package_name.as_deref(),
            &mut written,
        )?;
    }

    // Heterogeneous-storage closed universes: when the program references
    // `bag::Bag` / `object_bag::ObjectBag`, emit the per-project `TyCode` (DF
    // universe) and `BagU` (bag universe) inductives + interp/Universe/HasCode
    // instance files into Generated/ (the DfU/BagU split, unified-backend
    // design Phase 0). The lakefile dir-scan below picks up `Generated` as its
    // own lean_lib.
    // World-mode packages need the universes unconditionally: every type
    // flowing through a `World.*` typed view must have a `HasCode TyCode`
    // instance, bag or no bag.
    if crate::renderer::dyn_type_universe::program_uses_bag(&program)
        || program.world_functions.is_some()
    {
        // Native struct keys: structs provided by hand-written `*Natives.lean`
        // files (they carry their own DecidableEq instances; the interp files
        // must not post-hoc-derive them).
        let native_struct_keys: std::collections::HashSet<(usize, String)> = {
            let mut set = std::collections::HashSet::new();
            for (mid, module) in program.modules.iter() {
                let stem =
                    crate::renderer::program_renderer::get_namespace_file_stem(&program, *mid);
                let natives_path = output_dir
                    .join(&module.package_name)
                    .join(format!("{}Natives.lean", stem));
                if natives_path.exists() {
                    for name in crate::renderer::program_renderer::extract_native_struct_names_pub(
                        &natives_path,
                    ) {
                        set.insert((*mid, name));
                    }
                }
            }
            set
        };
        crate::renderer::dyn_type_universe::write_universes(
            &program,
            output_dir,
            &native_struct_keys,
            &mut written,
        )?;
    }

    // World-mode: pin the per-project `Generated/World.lean` (the `World`
    // abbrev over the DF/Bag universes + the `World.*` typed-view wrappers
    // the lowered calls render against).
    if program.world_functions.is_some() {
        crate::renderer::dyn_type_universe::write_world_file(&program, output_dir, &mut written)?;
    }

    // Cast-quarantine render check (unified-backend design Phase 0.3): no
    // heterogeneity machinery outside Prelude/, Generated/ and natives files.
    crate::renderer::cast_quarantine::check_output_dir(output_dir);

    // Generate lakefile and manifest with per-package libraries
    let lake_setup_start = std::time::Instant::now();
    let mut all_packages: std::collections::BTreeSet<String> = packages.iter().cloned().collect();
    for entry in fs::read_dir(output_dir)? {
        let entry = entry?;
        if entry.path().is_dir() {
            let name = entry.file_name().to_string_lossy().to_string();
            // Skip dot-prefixed dirs (sui-lean internals like `.lake`,
            // `.test_bytecode_deps`) — Lake rejects identifiers starting
            // with a dot, and these aren't lean libraries anyway.
            if name.starts_with('.') {
                continue;
            }
            // Skip dirs whose name is not a valid Lean lib identifier
            // (must start with a letter/underscore, then letters/digits/underscores).
            // Stale per-function-mode project dirs land here as
            // `0xb::tick_math` (address-qualified) — turning them into
            // `lean_lib 0xb::tick_math` produces a lakefile that fails to
            // parse. Skip loudly rather than emit invalid output.
            let is_valid_lib_ident = name
                .chars()
                .next()
                .is_some_and(|c| c.is_ascii_alphabetic() || c == '_')
                && name.chars().all(|c| c.is_ascii_alphanumeric() || c == '_');
            if !is_valid_lib_ident {
                eprintln!(
                    "⚠️  Skipping output dir {:?}: not a valid Lean lib name \
                     (likely stale from a prior --generation-mode run; safe to delete)",
                    name
                );
                continue;
            }
            if name != "Prelude"
                && name != "Prover"
                && name != "Proofs"
                && name != "Termination"
                && name != "Correctness"
                && name != "lake-packages"
            {
                all_packages.insert(name);
            }
        }
    }
    let all_packages: Vec<String> = all_packages.into_iter().collect();
    // Point the Proofs/Termination libs at sources/lean/ so lake builds the
    // user-maintained files in place (no copies in the output tree). When a
    // subdirectory doesn't exist, the lib falls back to an empty output-local
    // directory so lake still resolves its root.
    let user_src_rel = |sub: &str| -> anyhow::Result<Option<String>> {
        if user_proofs_src.join(sub).is_dir() {
            let rel = relative_path(output_dir, &user_proofs_src)?;
            Ok(Some(rel.to_string_lossy().into_owned()))
        } else {
            fs::create_dir_all(output_dir.join(sub))?;
            Ok(None)
        }
    };
    let proofs_src = user_src_rel("Proofs")?;
    let termination_src = user_src_rel("Termination")?;
    // The unified hook surface (unified-backend design §8): built by lake in
    // place like Termination/, but with NO output-local fallback dir — a
    // package without sources/lean/Hooks/ keeps a byte-identical lakefile.
    let hooks_src = if user_proofs_src.join("Hooks").is_dir() {
        Some(
            relative_path(output_dir, &user_proofs_src)?
                .to_string_lossy()
                .into_owned(),
        )
    } else {
        None
    };
    crate::write_lakefile(
        output_dir,
        "sui_lean_output",
        &all_packages,
        proofs_src.as_deref(),
        termination_src.as_deref(),
        hooks_src.as_deref(),
        &mut written,
    )?;
    eprintln!(
        "⏱ Lakefile generation took: {}ms",
        lake_setup_start.elapsed().as_millis()
    );

    // Remove stale .lean files from previous runs.
    written.remove_stale(output_dir);

    // Run lake build
    let lake_build_start = std::time::Instant::now();
    let output_str = output_dir
        .to_str()
        .ok_or_else(|| anyhow::anyhow!("Invalid output path"))?;

    eprintln!(
        "⏱ Overall backend took: {}ms",
        overall_start.elapsed().as_millis()
    );

    if generate_only {
        println!("Generated Lean files in: {}", output_dir.display());
        println!("(Skipping lake build due to --generate-only flag)");
        return Ok(());
    }

    match run_lake_build(output_str).await {
        Ok(output) => {
            println!("\n=== Lake Build Output ===");
            println!("{}", output);
            println!("=== Lake Build Succeeded ===\n");
            println!("Generated Lean files in: {}", output_dir.display());
            Ok(())
        }
        Err(e) => Err(e),
    }
}

/// Scan a `sources/lean/` directory for the client's termination hooks: the
/// `def <name>.loop_hyp` and `def <name>.precond` headers. These drive the
/// generic `thread_lean_terminations` pass (the name-free replacement for the
/// old hard-coded max_heapify/derive_gas passes), so the function names live in
/// the client's Lean files, never in the generator.
pub fn scan_lean_termination_decls(
    sources_lean_dir: &Path,
) -> intermediate_theorem_format::LeanTerminationDecls {
    let mut decls = intermediate_theorem_format::LeanTerminationDecls::default();
    let entries = match fs::read_dir(sources_lean_dir) {
        Ok(e) => e,
        Err(_) => return decls,
    };
    for entry in entries.flatten() {
        let path = entry.path();
        // Termination hooks live in sources/lean/Termination/ (legacy layouts
        // keep them flat); scan one level of subdirectories either way.
        if path.is_dir() {
            let sub = scan_lean_termination_decls(&path);
            decls.loop_hyp.extend(sub.loop_hyp);
            decls.precond.extend(sub.precond);
            decls.termination.extend(sub.termination);
            decls.data_inv.extend(sub.data_inv);
            for (stem, opts) in sub.module_options {
                decls.module_options.entry(stem).or_default().extend(opts);
            }
            continue;
        }
        if path.extension().and_then(|e| e.to_str()) != Some("lean") {
            continue;
        }
        let Ok(content) = fs::read_to_string(&path) else {
            continue;
        };
        for line in content.lines() {
            let mut t = line.trim_start();
            // Skip a leading attribute list (`@[reducible] def ...`).
            if let Some(after_attr) = t.strip_prefix("@[") {
                let Some(close) = after_attr.find(']') else {
                    continue;
                };
                t = after_attr[close + 1..].trim_start();
            }
            let Some(rest) = t.strip_prefix("def ") else {
                continue;
            };
            let Some(name) = rest.split([' ', '(', '\t']).next() else {
                continue;
            };
            if let Some(stem) = name.strip_suffix(".loop_hyp") {
                decls.loop_hyp.insert(stem.to_string());
            } else if let Some(stem) = name.strip_suffix(".precond") {
                decls.precond.insert(stem.to_string());
            } else if let Some(stem) = name.strip_suffix(".termination") {
                decls.termination.insert(stem.to_string());
            } else if let Some(stem) = name.strip_suffix(".data_inv") {
                decls.data_inv.insert(stem.to_string());
            } else if let Some(stem) = name.strip_suffix(".module_options") {
                // Options are the quoted string literals on the decl line,
                // e.g. `def Demo.module_options : List String := ["world_mode"]`.
                let opts: std::collections::BTreeSet<String> = line
                    .split('"')
                    .skip(1)
                    .step_by(2)
                    .map(|s| s.to_string())
                    .collect();
                decls
                    .module_options
                    .entry(stem.to_string())
                    .or_default()
                    .extend(opts);
            }
        }
    }
    decls
}
