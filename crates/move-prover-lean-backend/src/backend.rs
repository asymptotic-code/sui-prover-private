// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Lean backend entry point
//!
//! Takes TheoremProgram and renders to Lean files.
//! ZERO logic, pure rendering.

use crate::prelude::PreludeManager;
use crate::renderer::render_to_directory;
use crate::runtime::run_lake_build;
use crate::{copy_if_changed, WrittenFiles};
use intermediate_theorem_format::validate_program;
use move_model::model::GlobalEnv;
use move_stackless_bytecode::function_target_pipeline::FunctionTargetsHolder;
use stackless_to_intermediate::ProgramBuilder;
use std::fs;
use std::path::Path;

/// Recursively copy a directory tree, only copying files that changed
fn copy_dir_recursive(src: &Path, dst: &Path, written: &mut WrittenFiles) -> anyhow::Result<()> {
    if !src.is_dir() {
        return Ok(());
    }

    fs::create_dir_all(dst)?;

    for entry in fs::read_dir(src)? {
        let entry = entry?;
        let src_path = entry.path();
        let dst_path = dst.join(entry.file_name());

        if src_path.is_dir() {
            copy_dir_recursive(&src_path, &dst_path, written)?;
        } else {
            copy_if_changed(&src_path, &dst_path, written)?;
        }
    }

    Ok(())
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
    )
    .await
}

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
) -> anyhow::Result<()> {
    run_backend_inner(
        env,
        targets,
        output_dir,
        package_dir,
        generate_only,
        false, // test_mode: build with BuildMode::Spec (prune #[test] items)
        boogie_proven_names,
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
) -> anyhow::Result<()> {
    run_backend_inner(
        env,
        targets,
        output_dir,
        package_dir,
        generate_only,
        test_mode,
        &std::collections::HashSet::new(),
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
    let pre_finalize = move |program: &mut intermediate_theorem_format::Program| {
        crate::native_ghost_fields::augment_structs_with_native_ghost_fields(program, &lemmas_dir);
    };

    // Run translation pipeline
    let build_start = std::time::Instant::now();
    let mut program = if test_mode {
        // Test-mode body shape: preserves `IRNode::Abort` inside bodies and
        // keeps `#[test]` items in the IR, then runs option-shape finalize.
        ProgramBuilder::new(env).build_for_test_with_hook(targets, pre_finalize)
    } else {
        ProgramBuilder::new(env).build_with_mode_and_hook(
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
    fs::create_dir_all(output_dir.join("Proofs"))?;
    fs::create_dir_all(output_dir.join("Termination"))?;
    fs::create_dir_all(output_dir.join("Correctness"))?;

    // Copy user files from sources/lean/ to output/Proofs/
    // Termination files (those matching generated module names) will be copied
    // to output/Termination/ during rendering when the module is processed.
    let user_proofs_src = package_dir.join("sources").join("lean");
    let proofs_dest = output_dir.join("Proofs");
    if user_proofs_src.exists() {
        copy_dir_recursive(&user_proofs_src, &proofs_dest, &mut written)?;
    }

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
        &proofs_dest,
        user_package_name.as_deref(),
        &mut written,
    )?;
    eprintln!(
        "⏱ Rendering to Lean took: {}ms",
        render_start.elapsed().as_millis()
    );

    // Re-copy user proofs after rendering: the render step may have generated
    // starter proof files in sources/lean/ that weren't present during the
    // initial copy. This ensures output/Proofs/ has the latest versions
    // and correctness files detect them.
    if user_proofs_src.exists() {
        copy_dir_recursive(&user_proofs_src, &proofs_dest, &mut written)?;
        render_to_directory(
            &mut program,
            output_dir,
            &prelude_imports,
            package_dir,
            &proofs_dest,
            user_package_name.as_deref(),
            &mut written,
        )?;
    }

    // Heterogeneous-bag closed universe: when the program references
    // `bag::Bag` / `object_bag::ObjectBag`, emit the per-project `TyCode`
    // (bare inductive + interp/Universe/HasCode instances) into Generated/.
    // The lakefile dir-scan below picks up `Generated` as its own lean_lib.
    if crate::renderer::dyn_type_universe::program_uses_bag(&program) {
        let universe = crate::renderer::dyn_type_universe::collect(&program);
        crate::renderer::dyn_type_universe::write_ty_code_file(
            &universe,
            &program,
            output_dir,
            &mut written,
        )?;
        crate::renderer::dyn_type_universe::write_ty_code_interp_file(
            &universe,
            &program,
            output_dir,
            &mut written,
        )?;
    }

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
    crate::write_lakefile(output_dir, "sui_lean_output", &all_packages, &mut written)?;
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
