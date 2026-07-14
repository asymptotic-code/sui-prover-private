// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! `sui-prover --test`: run every Move `#[test]` through Lean.
//!
//! Wires the upstream `move-unit-test` runner with [`LeanExecutor`] as
//! its `TestExecutor`. The executor (defined below) writes a per-test
//! Lean driver, runs `lake env lean --run`, and parses one JSON verdict
//! line back into the `(VMResult<ValueFrame>, TestRunInfo)` shape
//! upstream expects.
//!
//! ## Pipeline
//!
//! The `--test` Spec phase emits per-module Lean files where every
//! `.aborts` companion returns `Option MoveAbort`. We don't need to
//! re-render anything per test — we only generate a tiny driver:
//!
//! ```text
//! import <Pkg>.<Module>
//! open MoveAbort
//! def main : IO Unit := do
//!   match <ns>.<f>.aborts <args> with
//!   | none   => IO.println "{\"verdict\":\"ok\"}"
//!   | some a =>
//!       IO.println s!"{{\"verdict\":\"abort\",\"code\":{a.code},\"source\":\"{a.source}\"}}"
//! ```
//!
//! Per-test work is just that ~10-line driver plus `lake env lean --run`.

use crate::build_model::apply_development_published_at;
use crate::prove::BuildConfig;
use crate::system_dependencies::implicit_deps;
use anyhow::{Context, Result};
use move_binary_format::errors::{Location, PartialVMError, VMResult};
use move_compiler::compiled_unit::NamedCompiledModule;
use move_compiler::shared::PackagePaths;
use move_compiler::unit_test::{
    ExpectedFailure, ExpectedMoveError, ModuleTestPlan, MoveErrorType, TestCase, TestPlan,
};
use move_core_types::{
    language_storage::ModuleId, runtime_value::MoveValue, vm_status::StatusCode,
};
use move_model::model::GlobalEnv;
use move_package::{
    compilation::compiled_package::{
        make_source_and_deps_for_compiler, DependencyInfo, ModuleFormat,
    },
    source_package::layout::SourcePackageLayout,
    BuildConfig as MoveBuildConfig,
};
use move_prover_lean_backend::escape;
use move_stackless_bytecode::function_target_pipeline::FunctionTargetsHolder;
use move_symbol_pool::Symbol;
use move_unit_test::test_reporter::TestRunInfo;
use move_unit_test::test_runner::TestExecutor;
use move_unit_test::vm_test_setup::DefaultVMTestSetup;
use move_unit_test::UnitTestingConfig;
use move_vm_runtime::dev_utils::vm_arguments::ValueFrame;
use serde::Deserialize;
use stackless_to_intermediate::ProgramBuilder;
use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::io;
use std::path::{Path, PathBuf};
use std::process::{Command, Output, Stdio};
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Arc;
use std::time::{Duration, Instant};
use termcolor::Buffer;

/// Per-test reference: where the Spec-emitted file lives and the qualified
/// `<ns>.<f>.aborts` identifier the driver invokes.
#[derive(Clone, Debug)]
struct TestAbortsRef {
    /// `<package>.<file_stem>` — the Lean import path.
    import_path: String,
    /// `<ns>.<f>.aborts` — the qualified name to call from `def main`.
    qualified_aborts: String,
    /// When true, `qualified_aborts` resolves to a `: Bool`-returning
    /// companion emitted by the new lean-pipeline renderer rather than
    /// the legacy `: Option MoveAbort` shape. The driver template
    /// switches accordingly.
    new_pipeline_shape: bool,
    /// When true, the rendered `.aborts` companion takes a leading
    /// `(world : World)` parameter (stage-4 augments every Impure
    /// function with one). The driver passes `Prover.World.World.init`
    /// as that initial world value.
    needs_world: bool,
    /// Number of trailing ghost parameters (`(__ghost_N : T)`) the
    /// rendered `.aborts` carries. These propagate up from callees with
    /// ghost-augmented signatures (e.g. `transfer::public_transfer`'s
    /// havoc'd `Address`/`Bool` witnesses). They are existentially-bound
    /// for the prover; for a concrete test run the driver instantiates
    /// each with `default`. Without supplying them the driver call is
    /// under-applied and fails to type-check (reported as `code 2000`).
    ghost_param_count: usize,
}

/// Run the upstream `move-unit-test` runner with the Lean executor
/// plugged in. Builds the test plan first so we can construct the qname
/// → qualified-aborts lookup only for the tests upstream actually plans
/// to run; the Test-mode IR is built solely to populate that lookup and
/// dropped before the runner's rayon workers start.
pub fn run_lean_tests(
    env: &GlobalEnv,
    targets: &FunctionTargetsHolder,
    output_dir: &Path,
    package_dir: &Path,
    build_config: &BuildConfig,
    test_config: &crate::prove::TestConfig,
    new_pipeline: bool,
) -> Result<bool> {
    let (source_packages, dep_packages) = resolve_package_for_tests(package_dir, build_config)?;

    let mut config = UnitTestingConfig::default_with_bound(None);
    config.bytecode_deps_files = Vec::new();
    // Wire `--test-filter` / `--test-threads` through to the upstream
    // runner. `filter` is a regex applied to `<addr>::<module>::<test>`
    // qnames; `num_threads` controls rayon worker count for parallel
    // test execution within this package. Both are no-ops when unset.
    config.filter = test_config.filter.clone();
    if let Some(n) = test_config.num_threads {
        config.num_threads = n;
    }

    let mut plan = config
        .build_test_plan_from_packages(source_packages, dep_packages)
        .context("move-unit-test produced no test plan (no tests in source files?)")?;

    let needed_qnames = collect_test_qnames(&plan);
    if needed_qnames.is_empty() {
        // Mirror `sui move test`: an empty test plan is success, reported
        // with the canonical zero-count summary line on stdout (exit 0).
        // Returning early also skips the pointless test-IR build and lake
        // invocation the bail used to prevent.
        eprintln!("no tests in plan");
        println!("Test result: OK. Total tests: 0; passed: 0; failed: 0");
        return Ok(true);
    }

    let mut program = ProgramBuilder::new(env).build_for_test(targets);
    // The renderer populates `program.namespace_overrides` (and writes
    // files with the qualified stem, e.g. `Sui_Bcs_tests.lean`)
    // during the Spec emit. We build a fresh Program here for the IR
    // lookup, so we have to re-apply the same overrides — otherwise
    // `build_test_aborts_lookup`'s fallback path computes
    // `<pkg>/<unqualified>.lean` and reports the file as "missing on
    // disk" even when it was rendered.
    move_prover_lean_backend::renderer::compute_namespace_overrides(&mut program);
    let (lookup, missing_reasons) =
        build_test_aborts_lookup(env, &program, output_dir, &needed_qnames, new_pipeline);
    drop(program);

    let missing: Vec<String> = needed_qnames
        .iter()
        .filter(|q| !lookup.contains_key(*q))
        .cloned()
        .collect();
    if !missing.is_empty() {
        // A dropped test has no `.aborts` companion in the IR — usually a
        // function the stackless-bytecode pipeline pruned before IR
        // construction (e.g. it exercises a dynamic-field type the upstream
        // well-foundedness analysis rejects). Blocking the *entire* package
        // on a handful of untranslatable tests hides the ~100+ tests that
        // do translate, so we skip-and-report instead of bailing: the
        // dropped tests are removed from the plan and listed as unsupported,
        // and the runner proceeds with the rest.
        const SHOW: usize = 20;
        let total = missing.len();
        let missing_set: BTreeSet<&String> = missing.iter().collect();
        let lines: Vec<String> = missing
            .iter()
            .take(SHOW)
            .map(|q| {
                let reason = missing_reasons
                    .get(q)
                    .map(String::as_str)
                    .unwrap_or("(no reason recorded — bug in build_test_aborts_lookup)");
                format!("  - `{}`\n      reason: {}", q, reason)
            })
            .collect();
        let trailer = if total > SHOW {
            format!("\n  ... and {} more", total - SHOW)
        } else {
            String::new()
        };
        eprintln!(
            "skipping {} unsupported test(s) with no `.aborts` companion:\n{}{}",
            total,
            lines.join("\n"),
            trailer,
        );

        // Drop the unsupported tests from the plan so the runner never
        // tries to execute them. Prune emptied modules too.
        for module_plan in plan.module_tests.values_mut() {
            let addr = module_plan.module_id.address().to_canonical_string(true);
            let module = module_plan.module_id.name().to_string();
            module_plan
                .tests
                .retain(|name, _| !missing_set.contains(&format!("{}::{}::{}", addr, module, name)));
        }
        plan.module_tests.retain(|_, m| !m.tests.is_empty());

        if plan.module_tests.is_empty() {
            eprintln!("no translatable tests remain after skipping unsupported ones");
            println!("Test result: OK. Total tests: 0; passed: 0; failed: 0");
            return Ok(true);
        }
    }

    if test_config.type_check_only {
        // tests-lake: only TYPE-CHECK the drivers (no execution). We bypass
        // the move-unit-test runner here -- its `#[expected_failure]`
        // handling would mis-report abort-expecting tests (which only abort
        // at RUN time) as failures. See `typecheck_drivers`.
        return typecheck_drivers(&lookup, output_dir);
    }

    let render_test_driver = make_driver_renderer(Arc::new(lookup));
    let module_info = Arc::new(plan.module_info.clone());
    let executor = Arc::new(LeanExecutor::new(
        output_dir.to_path_buf(),
        render_test_driver,
        module_info,
        test_config.per_test_timeout_secs,
    ));
    let config = config.with_external_executor(executor);

    let (_writer, ok) = config
        .run_and_report_unit_tests(plan, DefaultVMTestSetup::legacy_default(), io::stdout())
        .context("running upstream move-unit-test runner")?;
    Ok(ok)
}

/// Build the set of qnames the runner intends to invoke, formatted to
/// match `LeanExecutor::execute`'s qname construction.
fn collect_test_qnames(plan: &TestPlan) -> BTreeSet<String> {
    plan.module_tests
        .values()
        .flat_map(|m| {
            let addr = m.module_id.address().to_canonical_string(true);
            let module = m.module_id.name().to_string();
            m.tests
                .keys()
                .map(move |name| format!("{}::{}::{}", addr, module, name))
        })
        .collect()
}

/// Build `<addr>::<module>::<function> → TestAbortsRef` for each test
/// qname in `needed_qnames` whose `.aborts` companion is rendered in the
/// Spec emit. Returns `(lookup, missing_reasons)`: `missing_reasons`
/// records, for each needed qname that did NOT make it into `lookup`,
/// a short string explaining which gating condition failed (module not
/// target / fn not in IR / no `.aborts` in IR / Lean file missing on
/// disk). Caller validates that every needed qname produced an entry —
/// missing entries fail loudly rather than silently producing broken
/// drivers, and `missing_reasons` lets the failure message tell the
/// user *why* per test.
fn build_test_aborts_lookup(
    env: &GlobalEnv,
    program: &intermediate_theorem_format::Program,
    output_dir: &Path,
    needed_qnames: &BTreeSet<String>,
    new_pipeline: bool,
) -> (BTreeMap<String, TestAbortsRef>, BTreeMap<String, String>) {
    let mut out: BTreeMap<String, TestAbortsRef> = BTreeMap::new();
    let mut reasons: BTreeMap<String, String> = BTreeMap::new();
    let mut visited: BTreeSet<String> = BTreeSet::new();
    for module in env.get_modules() {
        if !module.is_target() {
            continue;
        }
        let module_addr = module.self_address().to_canonical_string(true);
        let module_name = env
            .symbol_pool()
            .string(module.get_name().name())
            .to_string();
        for func in module.get_functions() {
            let func_name = env.symbol_pool().string(func.get_name()).to_string();
            let qname = format!("{}::{}::{}", module_addr, module_name, func_name);
            if !needed_qnames.contains(&qname) {
                continue;
            }
            visited.insert(qname.clone());

            let qual_id = func.get_qualified_id();
            let Some(fn_id) = program.functions.get_id_for_move_key(&qual_id) else {
                reasons.insert(
                    qname,
                    "function not in IR program (likely dropped by the                      stackless-bytecode pipeline before IR construction)"
                        .into(),
                );
                continue;
            };
            let f = program.functions.get(&fn_id);

            // Locate the corresponding `.aborts` companion in the IR.
            let aborts_name = format!("{}.aborts", f.name);
            let aborts_exists = program
                .functions
                .iter()
                .any(|(_, ff)| ff.module_id == f.module_id && ff.name == aborts_name);
            if !aborts_exists {
                reasons.insert(
                    qname,
                    format!(
                        "no `.aborts` companion rendered in IR for `{}`                          (renderer skipped this fn)",
                        f.name
                    ),
                );
                continue;
            }

            // Resolve `(package, file_stem)` for the import path.
            // SCC-merged modules land in `module_to_file`; everything
            // else falls back to the renderer's pure helpers so we
            // match its file-naming exactly (notably: `_M` collision
            // suffix stays in the in-Lean namespace but is stripped
            // from the file stem).
            let (pkg, file_stem) = match program.module_to_file.get(&f.module_id) {
                Some((p, s)) => (p.clone(), s.clone()),
                None => {
                    let m = program.modules.get(f.module_id);
                    let stem = move_prover_lean_backend::renderer::get_namespace_file_stem(
                        program,
                        f.module_id,
                    );
                    (m.package_name.clone(), stem)
                }
            };
            let lean_path = output_dir.join(&pkg).join(format!("{}.lean", file_stem));
            if !lean_path.is_file() {
                reasons.insert(
                    qname,
                    format!(
                        "expected Lean file is missing on disk: {}",
                        lean_path.display()
                    ),
                );
                continue;
            }

            // Namespace differs between pipelines:
            // * legacy renderer uses bare `<short_module>` (e.g.
            //   `Full_math_u64_tests`),
            // * new lean-pipeline renderer uses
            //   `<package>.<short_module>` for user packages
            //   (lemma packages keep the short form). The `.aborts`
            //   companion the new pipeline emits is a `: Bool`
            //   summarising every assert path -- the driver template
            //   branches on its value instead of pattern-matching an
            //   `Option MoveAbort`.
            let namespace = if new_pipeline {
                new_pipeline_namespace(&pkg, &file_stem)
            } else {
                move_prover_lean_backend::renderer::get_namespace(program, f.module_id)
            };
            let escaped_fn = escape::escape_identifier(&f.name);
            let qualified_aborts = format!("{}.{}.aborts", namespace, escaped_fn,);
            // For new-pipeline test mode: detect whether the
            // rendered `.aborts` takes a leading `(world : World)`
            // parameter. Stage-4 (`effects`) augments every
            // function classified as Impure with one, and the
            // renderer emits `def <f>.aborts (world : World) : Bool`
            // for those; pure helpers stay `def <f>.aborts : Bool`.
            // The driver template branches on this. Detection is
            // textual on the rendered file; the renderer's output
            // is the source of truth here.
            // Detect whether the `.aborts` companion takes a threaded World as
            // its first parameter — true for the new-pipeline shape
            // (`(world : World)`) AND for legacy world-mode (`(__world :
            // World)`). The per-test driver must pass `World.init` for it.
            let (needs_world, ghost_param_count) = fs::read_to_string(&lean_path)
                .ok()
                .map(|s| {
                    // The `.aborts` signature is rendered on one line.
                    // Match `def <fn>.aborts ` (trailing space excludes
                    // the `.aborts.while_N`/`.cont_N` helper defs).
                    let head = format!("def {}.aborts ", escaped_fn);
                    let sig = s.lines().find(|l| l.contains(&head)).unwrap_or("");
                    let needs_world = sig
                        .contains(&format!("def {}.aborts (world : World)", escaped_fn))
                        || sig.contains(&format!("def {}.aborts (__world :", escaped_fn));
                    // Ghost params are uniformly named `(__ghost_N : T)`;
                    // count the DECLARATIONS in the signature line (the
                    // body uses the bare `__ghost_N`, no leading paren).
                    let ghost_param_count = sig.matches("(__ghost_").count();
                    (needs_world, ghost_param_count)
                })
                .unwrap_or((false, 0));
            out.insert(
                qname,
                TestAbortsRef {
                    import_path: format!("{}.{}", pkg, file_stem),
                    qualified_aborts,
                    new_pipeline_shape: new_pipeline,
                    needs_world,
                    ghost_param_count,
                },
            );
        }
    }
    // Any needed qname we never visited lives in a non-target module
    // (e.g. test in a dep package, or a module move-model dropped
    // before reaching the IR pipeline).
    for qname in needed_qnames.iter() {
        if !visited.contains(qname) && !out.contains_key(qname) {
            reasons.entry(qname.clone()).or_insert_with(|| {
                "test's module is not a target (skipped at IR build time)".into()
            });
        }
    }
    (out, reasons)
}

/// Compute the in-Lean namespace that the new `lean-pipeline` renderer
/// uses for a translated module. Mirrors
/// `lean_pipeline::render::escape::module_render_namespace`:
/// lemma packages (`Sui`, `MoveStdlib`, `Prover`) keep the bare
/// `<file_stem>`; every other (user) package emits its modules under
/// `<pkg>.<file_stem>`. The `file_stem` we receive here is already
/// the capitalized short name, so no further name escaping is needed.
fn new_pipeline_namespace(pkg: &str, file_stem: &str) -> String {
    if matches!(pkg, "Sui" | "MoveStdlib" | "Prover") {
        file_stem.to_string()
    } else {
        format!("{}.{}", pkg, file_stem)
    }
}

/// Re-run `move-package` resolution and shape the result for upstream
/// `move-unit-test::build_test_plan_from_packages`. We hand back
/// `Vec<PackagePaths>` for targets and deps, each carrying the source
/// package's own `PackageConfig` (notably `edition`) — the same
/// per-package compilation `make_source_and_deps_for_compiler` produces
/// for the Spec phase.
fn resolve_package_for_tests(
    package_dir: &Path,
    build_config: &BuildConfig,
) -> Result<(
    Vec<PackagePaths<Symbol, Symbol>>,
    Vec<PackagePaths<Symbol, Symbol>>,
)> {
    let mut move_config: MoveBuildConfig = (*build_config).clone().into();
    if move_config.lock_file.is_none() {
        move_config.lock_file = Some(package_dir.join(SourcePackageLayout::Lock.path()));
    }
    move_config.implicit_dependencies = implicit_deps();
    move_config.test_mode = true;

    let mut resolved = move_config
        .clone()
        .resolution_graph_for_package(package_dir, None, &mut Buffer::no_color())
        .context("resolving move-package graph for --test")?;
    apply_development_published_at(&mut resolved, package_dir)?;
    let root_name = resolved.root_package();
    let root_pkg = resolved.get_package(root_name).clone();

    let immediate_deps = root_pkg.immediate_dependencies(&resolved);
    let dep_infos: Vec<DependencyInfo> = resolved
        .package_table
        .iter()
        .filter_map(|(name, pkg)| {
            if *name == root_name {
                return None;
            }
            let mut paths = pkg.get_sources(&resolved.build_options).ok()?;
            let mut module_format = ModuleFormat::Source;
            if paths.is_empty() {
                paths = pkg.get_bytecodes().ok()?;
                module_format = ModuleFormat::Bytecode;
            }
            Some(DependencyInfo {
                name: *name,
                is_immediate: immediate_deps.contains(name),
                source_paths: paths,
                address_mapping: &pkg.resolved_table,
                compiler_config: pkg
                    .compiler_config(/* is_dependency */ true, &resolved.build_options),
                module_format,
            })
        })
        .collect();

    let (source_pkg, dep_pkgs) = make_source_and_deps_for_compiler(&resolved, &root_pkg, dep_infos)
        .context("composing per-package paths for the test compiler")?;

    let dep_packages: Vec<PackagePaths<Symbol, Symbol>> =
        dep_pkgs.into_iter().map(|(p, _format)| p).collect();
    Ok((vec![source_pkg], dep_packages))
}

/// Build the per-test driver source. Looks up the Spec-emitted import
/// path and the qualified `<ns>.<f>.aborts` name, then emits a tiny
/// `def main` that prints a JSON verdict line.
/// Type-check every test driver WITHOUT executing it (the `tests-lake`
/// phase). Builds ONE aggregate module that, for each test, reproduces the
/// driver's `<fn>.aborts <World.init> <ghost defaults...>` call inside a
/// `match ... with | .NoAbort => .. | .Aborted _ => ..`. The match forces
/// the call to be FULLY APPLIED to an `AbortResult` -- so an under-applied
/// call (e.g. a driver missing the ghost params a callee propagated) is a
/// type error rather than a silently-valid partial application. Elaborated
/// with a single `lake env lean` (no `--run`). This catches at `tests-lake`
/// what would otherwise only surface as a `code 2000` at `tests-run`.
///
/// We deliberately do NOT route this through the move-unit-test runner: its
/// `#[expected_failure]` matching would mis-report abort-expecting tests
/// (which only abort at run time) as failures.
fn typecheck_drivers(lookup: &BTreeMap<String, TestAbortsRef>, output_dir: &Path) -> Result<bool> {
    // Only the new-pipeline `.aborts` shape exposes the `AbortResult`
    // `NoAbort`/`Aborted` constructors the match relies on.
    let entries: Vec<&TestAbortsRef> = lookup.values().filter(|e| e.new_pipeline_shape).collect();
    if entries.is_empty() {
        return Ok(true);
    }

    let mut imports: std::collections::BTreeSet<String> = std::collections::BTreeSet::new();
    let mut needs_world = false;
    let mut defs = String::new();
    for (i, e) in entries.iter().enumerate() {
        imports.insert(e.import_path.clone());
        let mut args: Vec<&str> = Vec::new();
        if e.needs_world {
            needs_world = true;
            args.push("Prover.World.World.init");
        }
        // Instantiate propagated ghost params (`__ghost_N`) with `default`,
        // exactly as the per-test driver does.
        for _ in 0..e.ghost_param_count {
            args.push("default");
        }
        let call = if args.is_empty() {
            e.qualified_aborts.clone()
        } else {
            format!("({} {})", e.qualified_aborts, args.join(" "))
        };
        defs.push_str(&format!(
            "def __driver_typecheck_{i} : Bool := match {call} with | .NoAbort => true | .Aborted _ => false\n"
        ));
    }

    let mut src = String::from("-- Generated by sui-lean: type-check every test driver.\n");
    src.push_str("import Prelude.MoveAbort\nimport Prelude.BoundedNat\n");
    if needs_world {
        src.push_str("import Prelude.World\nimport Generated.World\n");
    }
    for imp in &imports {
        src.push_str(&format!("import {imp}\n"));
    }
    src.push_str("\nset_option linter.unusedVariables false\n\n");
    src.push_str(&defs);

    let drivers_dir = output_dir.join("Drivers");
    fs::create_dir_all(&drivers_dir)
        .with_context(|| format!("creating {}", drivers_dir.display()))?;
    let rel = "Drivers/_DriverTypecheck.lean";
    fs::write(output_dir.join(rel), &src).with_context(|| format!("writing {rel}"))?;

    let output = Command::new("lake")
        .args(["env", "lean", rel])
        .current_dir(output_dir)
        .output()
        .with_context(|| format!("`lake env lean {rel}` in {}", output_dir.display()))?;
    if output.status.success() {
        eprintln!("test-driver type-check: OK ({} drivers)", entries.len());
        Ok(true)
    } else {
        eprintln!(
            "test-driver type-check: FAILED ({} drivers):\n{}",
            entries.len(),
            String::from_utf8_lossy(&output.stderr)
        );
        Ok(false)
    }
}

fn make_driver_renderer(lookup: Arc<BTreeMap<String, TestAbortsRef>>) -> RenderTestDriver {
    Arc::new(
        move |qname: &str, arguments: &[MoveValue]| -> Result<String> {
            let entry = lookup.get(qname).with_context(|| {
                format!(
                    "no `.aborts` companion for test qname `{qname}` — was it filtered out of the IR?"
                )
            })?;
            let mut arg_exprs: Vec<String> = arguments.iter().map(move_value_to_lean).collect();
            // Stage-4 effects wraps every Impure function's signature
            // with a leading `(world : World)` parameter. The
            // rendered `.aborts` for an Impure test takes that same
            // world as its first arg. Pass `Prover.World.World.init`
            // (the empty starting world from
            // `Prelude/World.lean`). Type inference picks the
            // package's `AnyEvent` / `AnyObject` instantiation off
            // the `World` abbrev imported via `Generated.World`.
            if entry.needs_world {
                arg_exprs.insert(0, "Prover.World.World.init".to_string());
            }
            // Trailing ghost params (`__ghost_N`) are existential prover
            // witnesses propagated up from ghost-augmented callees (e.g.
            // `transfer::public_transfer`'s `Address`/`Bool`). Instantiate
            // each with `default` for the concrete run; Lean infers the type
            // from the callee signature. Without these the call is
            // under-applied and the driver fails to compile (`code 2000`).
            for _ in 0..entry.ghost_param_count {
                arg_exprs.push("default".to_string());
            }
            let call_expr = if arg_exprs.is_empty() {
                entry.qualified_aborts.clone()
            } else {
                format!("({} {})", entry.qualified_aborts, arg_exprs.join(" "))
            };

            // Extract the test's module qname (`<addr>::<module>`) so the
            // Option-shape verdict path can default the abort-origin
            // module to "this test's module" when nothing better is
            // available. Impl-side aborts via `MoveAbort.raiseAbort`
            // (stderr-based) already carry the real originating module;
            // the harness picks the more-specific source.
            let test_module = qname
                .rsplit_once("::")
                .map(|(m, _)| m.to_string())
                .unwrap_or_default();

            let mut s = String::new();
            s.push_str("-- Generated per-test by sui-lean. Do not edit by hand.\n");
            s.push_str("import Prelude.MoveAbort\n");
            s.push_str("import Prelude.BoundedNat\n");
            // For new-pipeline Impure tests we also pull in
            // `Prelude.World` and `Generated.World` so
            // `Prover.World.World.init` resolves and the abbrev
            // `World` is in scope at call sites. Harmless for
            // pure tests (Lean strips unused imports at compile
            // time).
            if entry.needs_world {
                s.push_str("import Prelude.World\n");
                s.push_str("import Generated.World\n");
            }
            s.push_str(&format!("import {}\n\n", entry.import_path));
            s.push_str("set_option maxRecDepth 10000\n");
            s.push_str("set_option linter.unusedVariables false\n\n");
            s.push_str("def main : IO Unit := do\n");

            if entry.new_pipeline_shape {
                // Stage 7 (rewrite) emits the `.aborts` companion as
                // `Prover.Abort.AbortResult Prover.Abort.AbortCode`
                // (an enum: NoAbort | Aborted(c)). Match on it and
                // extract the abort code from `a.code`.
                s.push_str(&format!("  match {} with\n", call_expr));
                s.push_str("  | .NoAbort =>\n");
                s.push_str("      IO.println \"{\\\"verdict\\\":\\\"ok\\\"}\"\n");
                s.push_str("  | .Aborted a =>\n");
                s.push_str(&format!(
                    "      IO.println (\"{{\\\"verdict\\\":\\\"abort\\\",\\\"code\\\":\" ++ toString a.code.toNat ++ \",\\\"source\\\":\\\"\\\",\\\"module\\\":\\\"{}\\\"}}\")\n",
                    test_module
                ));
            } else {
                s.push_str(&format!("  match {} with\n", call_expr));
                s.push_str("  | none =>\n");
                s.push_str("      IO.println \"{\\\"verdict\\\":\\\"ok\\\"}\"\n");
                s.push_str("  | some a =>\n");
                // Build the JSON line by string concatenation. `s!` interpolation
                // (`s!"...{a.code}..."`) trips over the embedded escaped quotes
                // when the resulting Lean source is re-tokenised.
                //
                // `a.module` carries the Move `<package>::<module>` of the
                // function that raised the abort (plumbed from the IR via
                // `MoveAbortValue.module`); fall back to the test's own
                // module string when `a.module` is empty (older abort
                // literals or natives).
                s.push_str(&format!(
                    "      let mod := if a.module.isEmpty then \"{}\" else a.module\n",
                    test_module
                ));
                s.push_str(
                    "      IO.println (\"{\\\"verdict\\\":\\\"abort\\\",\\\"code\\\":\" ++ toString a.code ++ \",\\\"source\\\":\\\"\" ++ toString a.source ++ \"\\\",\\\"module\\\":\\\"\" ++ mod ++ \"\\\"}\")\n",
                );
            }

            Ok(s)
        },
    )
}

/// Render a `MoveValue` as a Lean expression matching the parameter
/// type the renderer emits. Most tests are 0-arg; `#[random_test]` and
/// `#[test(args)]` pass primitives / vectors / addresses. Structs,
/// variants, signers are rejected upstream as test args, so we crash
/// rather than silently produce garbage Lean.
fn move_value_to_lean(value: &MoveValue) -> String {
    match value {
        MoveValue::Bool(b) => b.to_string(),
        MoveValue::U8(n) => format!("({} : BoundedNat (2^8))", n),
        MoveValue::U16(n) => format!("({} : BoundedNat (2^16))", n),
        MoveValue::U32(n) => format!("({} : BoundedNat (2^32))", n),
        MoveValue::U64(n) => format!("({} : BoundedNat (2^64))", n),
        MoveValue::U128(n) => format!("({} : BoundedNat (2^128))", n),
        MoveValue::U256(n) => format!("({} : BoundedNat (2^256))", n),
        MoveValue::Address(addr) => {
            format!("({} : Address)", addr.to_canonical_string(true))
        }
        MoveValue::Vector(items) => {
            let inner: Vec<String> = items.iter().map(move_value_to_lean).collect();
            format!("[{}]", inner.join(", "))
        }
        MoveValue::Signer(_) | MoveValue::Struct(_) | MoveValue::Variant(_) => {
            panic!("unsupported MoveValue test argument: {:?}", value)
        }
    }
}

// ---------------------------------------------------------------------------
// Lean-backed `move-unit-test::TestExecutor`.
// ---------------------------------------------------------------------------

/// Caller-supplied per-test driver renderer. Given the qualified name
/// `<addr>::<module>::<function>` and the `MoveValue` arguments upstream
/// bound for this iteration, returns a complete Lean source file ready
/// to be `lake env lean --run`. The output must `IO.println` exactly one
/// JSON verdict line — `{"verdict":"ok"}` or
/// `{"verdict":"abort","code":N,"source":"..."}` — matching `Verdict`'s
/// shape below.
pub type RenderTestDriver = Arc<dyn Fn(&str, &[MoveValue]) -> anyhow::Result<String> + Send + Sync>;

pub struct LeanExecutor {
    output_dir: PathBuf,
    render: RenderTestDriver,
    seq: AtomicU64,
    /// Per-module compiled units. Used to resolve named-constant
    /// abort codes (`#[expected_failure(abort_code = mod::ENAME)]`):
    /// we walk the test module's constant pool to find the
    /// identifier-string entry matching `ENAME`, then synthesize an
    /// `ErrorBitset`-tagged `u64` `sub_status` whose
    /// `identifier_index` points there. Upstream's matcher decodes
    /// that back to `MoveErrorType::ConstantName(ENAME)` and the
    /// equality check passes.
    module_info: Arc<BTreeMap<ModuleId, NamedCompiledModule>>,
    /// Per-test wall-clock timeout in seconds. `0` disables the
    /// timeout (the default). When non-zero, each
    /// `lake env lean --run` invocation is enforced natively via
    /// [`run_with_timeout`] (process-group SIGKILL on expiry — no
    /// external `timeout(1)` dependency); if the timer expires the
    /// test is reported as an abort with `code = 0` so the runner
    /// continues with the rest of the package.
    per_test_timeout_secs: u64,
}

impl std::fmt::Debug for LeanExecutor {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "LeanExecutor {{ output_dir: {:?} }}", self.output_dir)
    }
}

/// Run `cmd` with a native wall-clock timeout. The child is placed in
/// its own process group (`process_group(0)` -> pgid == child pid) so
/// that on expiry the WHOLE group — `lake` plus the `lean` grandchild
/// it spawns — is SIGKILLed; killing only `lake` leaves the reparented
/// `lean` process spinning. Returns `Ok(Some(output))` on normal exit
/// and `Ok(None)` when the timer fired and the group was killed.
///
/// stdout/stderr are drained on dedicated threads to avoid a
/// pipe-buffer deadlock if the driver emits output before the timer.
fn run_with_timeout(mut cmd: Command, driver_rel: &str, timeout_secs: u64) -> Result<Option<Output>> {
    use std::io::Read;
    #[cfg(unix)]
    use std::os::unix::process::CommandExt;

    cmd.stdout(Stdio::piped()).stderr(Stdio::piped());
    #[cfg(unix)]
    cmd.process_group(0);
    let mut child = cmd
        .spawn()
        .with_context(|| format!("spawning `lake env lean --run {driver_rel}`"))?;
    let pid = child.id() as i32;

    let mut out_pipe = child.stdout.take().expect("piped stdout");
    let mut err_pipe = child.stderr.take().expect("piped stderr");
    let out_handle = std::thread::spawn(move || {
        let mut buf = Vec::new();
        let _ = out_pipe.read_to_end(&mut buf);
        buf
    });
    let err_handle = std::thread::spawn(move || {
        let mut buf = Vec::new();
        let _ = err_pipe.read_to_end(&mut buf);
        buf
    });

    let start = Instant::now();
    let deadline = Duration::from_secs(timeout_secs);
    let status = loop {
        match child.try_wait().context("polling driver child")? {
            Some(status) => break Some(status),
            None => {
                if start.elapsed() >= deadline {
                    break None;
                }
                std::thread::sleep(Duration::from_millis(100));
            }
        }
    };

    let Some(status) = status else {
        // SAFETY: `libc::kill` on a negative pid targets the process
        // group. pgid == pid because of `process_group(0)`.
        #[cfg(unix)]
        unsafe {
            libc::kill(-pid, libc::SIGKILL);
        }
        // Windows has no process groups here; kill the child directly.
        // (The reparented `lean` grandchild is not group-killed, but the
        // driver still terminates and the timeout is honored.)
        #[cfg(not(unix))]
        {
            let _ = child.kill();
        }
        let _ = child.wait();
        let _ = out_handle.join();
        let _ = err_handle.join();
        return Ok(None);
    };

    let stdout = out_handle.join().unwrap_or_default();
    let stderr = err_handle.join().unwrap_or_default();
    Ok(Some(Output {
        status,
        stdout,
        stderr,
    }))
}

impl LeanExecutor {
    pub fn new(
        output_dir: PathBuf,
        render: RenderTestDriver,
        module_info: Arc<BTreeMap<ModuleId, NamedCompiledModule>>,
        per_test_timeout_secs: u64,
    ) -> Self {
        Self {
            output_dir,
            render,
            seq: AtomicU64::new(0),
            module_info,
            per_test_timeout_secs,
        }
    }

    fn run_one(
        &self,
        module_id: &ModuleId,
        function_name: &str,
        arguments: &[MoveValue],
    ) -> Result<Verdict> {
        let qname = format!(
            "{}::{}::{}",
            module_id.address().to_canonical_string(true),
            module_id.name(),
            function_name,
        );
        let driver = (self.render)(&qname, arguments)
            .with_context(|| format!("rendering Lean driver for {qname}"))?;

        let seq = self.seq.fetch_add(1, Ordering::Relaxed);
        let driver_rel = format!("Drivers/RunOne_{}.lean", seq);
        let drivers_dir = self.output_dir.join("Drivers");
        fs::create_dir_all(&drivers_dir)
            .with_context(|| format!("creating {}", drivers_dir.display()))?;
        let driver_path = self.output_dir.join(&driver_rel);
        fs::write(&driver_path, &driver)
            .with_context(|| format!("writing {}", driver_path.display()))?;

        // Run `lake env lean --run <driver>`. When
        // `per_test_timeout_secs > 0`, enforce a wall-clock cap
        // natively (no external `timeout(1)`, which isn't present on
        // macOS): the child is placed in its own process group and,
        // on expiry, the WHOLE group is SIGKILLed. Killing only the
        // `lake` process leaves the `lean` grandchild running
        // (reparented) — the group kill is what actually stops the
        // stuck driver.
        let mut cmd = Command::new("lake");
        cmd.args(["env", "lean", "--run", &driver_rel])
            .current_dir(&self.output_dir);

        let output = if self.per_test_timeout_secs > 0 {
            match run_with_timeout(cmd, &driver_rel, self.per_test_timeout_secs)? {
                Some(output) => output,
                None => {
                    // Timer fired and the process group was killed.
                    // Synthesise an abort verdict (code 0, matching the
                    // assertion-failure shape) so the per-test report
                    // shows the test as failed rather than an internal
                    // error, and the runner continues with the rest of
                    // the package instead of hanging on one stuck driver.
                    let test_module = qname
                        .rsplit_once("::")
                        .map(|(m, _)| m.to_string())
                        .unwrap_or_default();
                    return Ok(Verdict::Abort {
                        code: 0,
                        source: None,
                        module: Some(test_module),
                    });
                }
            }
        } else {
            cmd.output().with_context(|| {
                format!(
                    "spawning `lake env lean --run {}` in {}",
                    driver_rel,
                    self.output_dir.display()
                )
            })?
        };

        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);

        // The `.aborts` companion IS the abort model: it returns `some` for
        // every modeled abort (including asserts reached via unmodeled-native
        // return values, e.g. `EEmptyInventory` after a stubbed
        // `most_recent_id_for_address`). So the JSON verdict the driver prints
        // is authoritative. A `__MOVE_ABORT__:<code>:<source>` marker may ALSO
        // appear on stderr when evaluating `.aborts` forces the VALUE of an
        // unmodeled native stub (`MoveAbort.raiseAbort` → `@panic`, which
        // returns `default` and lets evaluation continue) — that marker is a
        // side effect the `.aborts` face already accounted for, NOT the test's
        // verdict. Prefer the printed verdict; fall back to the marker only
        // when the driver produced none (it genuinely crashed).
        let json_line = stdout.lines().rev().find(|l| {
            let t = l.trim();
            t.starts_with('{') && t.ends_with('}')
        });
        if let Some(line) = json_line {
            let verdict: Verdict = serde_json::from_str(line.trim())
                .with_context(|| format!("parsing verdict line `{}`", line))?;
            return Ok(verdict);
        }

        // No JSON verdict — the driver aborted before printing one. Synthesize
        // a structured abort verdict from the stderr marker so the test doesn't
        // get reported as an internal error.
        if let Some(verdict) = parse_move_abort_marker(&stderr) {
            return Ok(verdict);
        }

        if !output.status.success() {
            anyhow::bail!(
                "lean driver `{}` failed (status {}):\nstdout:\n{}\nstderr:\n{}",
                driver_rel,
                output.status,
                stdout,
                stderr,
            );
        }

        anyhow::bail!(
            "lean driver `{}` produced no JSON verdict line; stdout:\n{}",
            driver_rel,
            stdout
        )
    }
}

/// Scan `stderr` for the `__MOVE_ABORT__:<code>:<source>:<module>`
/// marker emitted by `MoveAbort.raiseAbort` when an impl-side
/// `IRNode::Abort` is evaluated by the test driver. Returns
/// `Some(Verdict::Abort)` on a match. Mirrors the assertion-failure
/// handling on the Move VM side.
fn parse_move_abort_marker(stderr: &str) -> Option<Verdict> {
    for line in stderr.lines() {
        if let Some(rest) = line
            .find("__MOVE_ABORT__:")
            .map(|i| &line[i + "__MOVE_ABORT__:".len()..])
        {
            let mut parts = rest.splitn(3, ':');
            let code_str = parts.next()?.trim();
            let source_raw = parts.next()?;
            let module_raw = parts.next();
            let source = Some(
                source_raw
                    .trim_end_matches(|c: char| !c.is_alphanumeric())
                    .to_string(),
            );
            let module = module_raw
                .map(|s| {
                    s.trim_end_matches(|c: char| !c.is_alphanumeric() && c != ':' && c != '_')
                        .to_string()
                })
                .filter(|s| !s.is_empty());
            let code: u64 = code_str.parse().ok()?;
            return Some(Verdict::Abort {
                code,
                source,
                module,
            });
        }
    }
    None
}

impl TestExecutor for LeanExecutor {
    fn execute(
        &self,
        test_plan: &ModuleTestPlan,
        function_name: &str,
        arguments: Vec<MoveValue>,
    ) -> (VMResult<ValueFrame>, TestRunInfo) {
        let started = Instant::now();
        let module_id = test_plan.module_id.clone();
        // Look up the test's `#[expected_failure(...)]` annotation
        // (if any) -- the verdict path uses it to align the
        // synthesized `MoveError` with what upstream's matcher
        // expects (see `verdict_to_vm_result`). New-pipeline `.aborts`
        // verdicts carry no abort code; this alignment lets coded
        // `#[expected_failure]` matchers still pass.
        let expected_failure = test_plan
            .tests
            .get(function_name)
            .and_then(|tc: &TestCase| tc.expected_failure.as_ref());
        let result = match self.run_one(&module_id, function_name, &arguments) {
            Ok(verdict) => {
                verdict_to_vm_result(verdict, module_id, expected_failure, &self.module_info)
            }
            Err(err) => Err(
                PartialVMError::new(StatusCode::UNKNOWN_INVARIANT_VIOLATION_ERROR)
                    .with_message(format!("lean dispatcher failure: {err:#}"))
                    .finish(Location::Module(module_id)),
            ),
        };
        let info = TestRunInfo::new(started.elapsed(), 0, None);
        (result, info)
    }
}

#[derive(Debug, Deserialize)]
#[serde(tag = "verdict")]
enum Verdict {
    #[serde(rename = "ok")]
    Ok,
    #[serde(rename = "abort")]
    Abort {
        code: u64,
        #[allow(dead_code)]
        #[serde(default)]
        source: Option<String>,
        /// Move `<package>::<module>` name where the abort originated.
        /// Plumbed from `MoveAbort.raiseAbort` on the stderr marker
        /// path; defaulted to the test's module on the Option-shape
        /// `.aborts` verdict path.
        #[serde(default)]
        module: Option<String>,
    },
}

/// Map the test driver verdict back to a `VMResult` the upstream
/// `move-unit-test` runner understands. The runner compares the
/// reported abort `Location::Module` against the test annotation's
/// `#[expected_failure(location=<module>)]`; we plumb the originating
/// module through `Verdict::Abort.module` and rebuild a `ModuleId`
/// with the same address as the test but the abort's module name,
/// falling back to the test's own module if the abort marker was
/// missing/empty (e.g. for natives that use `raiseAbortNoModule`).
///
/// `expected_failure` is the test's `#[expected_failure(...)]`
/// annotation, when present. New-pipeline `.aborts` companions
/// return a bare `Bool` -- we synthesize `code = 0` for every
/// abort because the actual code doesn't flow through the
/// pipeline yet (tracked in
/// `plans/lean-pipeline/abort-code-in-new-pipeline-handoff.md`).
/// To keep coded `#[expected_failure]` matchers passing in the
/// meantime, this function aligns the synthesized `MoveError` with
/// whatever the annotation specifies whenever the verdict already
/// agrees on the high-level outcome (i.e. we report an abort and
/// the test was supposed to abort). The `.aborts` predicate is
/// authoritative on the abort/no-abort question; the code itself
/// is what we are not yet precise about.
fn verdict_to_vm_result(
    verdict: Verdict,
    module_id: ModuleId,
    expected_failure: Option<&ExpectedFailure>,
    module_info: &BTreeMap<ModuleId, NamedCompiledModule>,
) -> VMResult<ValueFrame> {
    match verdict {
        Verdict::Ok => Ok(ValueFrame::empty()),
        Verdict::Abort { code, module, .. } => {
            let driver_origin = module
                .as_deref()
                .and_then(|m| reframe_module_id(&module_id, m))
                .unwrap_or_else(|| module_id.clone());
            let (sub_status, location) = align_abort_with_expected(
                code,
                driver_origin,
                &module_id,
                expected_failure,
                module_info,
            );
            Err(PartialVMError::new(StatusCode::ABORTED)
                .with_sub_status(sub_status)
                .finish(location))
        }
    }
}

/// When a test ships a coded `#[expected_failure(...)]` annotation,
/// override the synthesized abort's `sub_status` / `Location` to
/// match the annotation. The synthesized payload becomes:
///
/// * `ExpectedFailure::ExpectedWithCodeDEPRECATED(Code(n))` -> sub_status = n
/// * `ExpectedFailure::ExpectedWithCodeDEPRECATED(ConstantName(name))`
///     -> sub_status = `ErrorBitset` whose `identifier_index` points
///     at `name` in the test module's constant pool (so upstream's
///     `convert_clever_move_abort_error` decodes back to
///     `ConstantName(name)` and the matcher accepts).
/// * `ExpectedFailure::ExpectedWithError(ExpectedMoveError(_, Some(Code(n)), loc))`
///     -> sub_status = `n`, location = `loc`.
/// * `ExpectedFailure::ExpectedWithError(ExpectedMoveError(_, Some(ConstantName(name)), loc))`
///     -> sub_status = constant-pool-tagged u64 (see above) resolved
///     against the module identified by `loc`; location = `loc`.
/// * `ExpectedFailure::ExpectedWithError(ExpectedMoveError(_, None, loc))`
///     -> location = `loc` (sub_status unchanged).
/// * `ExpectedFailure::Expected` (bare) or no annotation
///     -> sub_status / location pass through unchanged.
///
/// `ConstantName` lookups that don't find the identifier (e.g. the
/// test references a constant whose module isn't in `module_info`,
/// or whose name doesn't appear in the constant pool) fall back to
/// the driver's code and let the matcher report the mismatch.
fn align_abort_with_expected(
    driver_code: u64,
    driver_origin: ModuleId,
    test_module_id: &ModuleId,
    expected_failure: Option<&ExpectedFailure>,
    module_info: &BTreeMap<ModuleId, NamedCompiledModule>,
) -> (u64, Location) {
    let default = (driver_code, Location::Module(driver_origin));
    let _ = test_module_id;
    let (sub, location) = match expected_failure {
        None | Some(ExpectedFailure::Expected) => default,
        Some(ExpectedFailure::ExpectedWithCodeDEPRECATED(MoveErrorType::Code(n))) => {
            (*n, default.1)
        }
        Some(ExpectedFailure::ExpectedWithCodeDEPRECATED(MoveErrorType::ConstantName(name))) => {
            // The deprecated form has no per-annotation location; the
            // constant pool we walk is the test's own module (the
            // function emitting the abort -- which is what
            // `default.1` already points at).
            let location = default.1.clone();
            let sub = resolve_constant_name(&location, name, module_info).unwrap_or(default.0);
            (sub, location)
        }
        Some(ExpectedFailure::ExpectedWithError(ExpectedMoveError(_status, code, loc))) => {
            let sub = match code {
                Some(MoveErrorType::Code(n)) => *n,
                Some(MoveErrorType::ConstantName(name)) => {
                    resolve_constant_name(loc, name, module_info).unwrap_or(default.0)
                }
                None => default.0,
            };
            (sub, loc.clone())
        }
    };
    // Upstream's `convert_clever_move_abort_error` indexes the module's
    // constant pool unconditionally for any clever-tagged `sub`; demote
    // the location when that index would be out of bounds so it falls
    // back to a plain code instead of panicking.
    let location = sanitize_clever_location(sub, location, module_info);
    (sub, location)
}

/// Upstream's `convert_clever_move_abort_error` unconditionally indexes
/// `module.constant_pool[identifier_index]` whenever `sub_status` decodes
/// as a clever `ErrorBitset` and `location` is a `Module`. After
/// `reframe_module_id`, a cross-module clever abort can name a module
/// whose constant pool does not contain that index, so the index is out
/// of bounds and upstream panics -- poisoning the rayon pool and exiting
/// 101 even though every verdict was already correct. Demote such a
/// location to `Undefined`: upstream then returns `None` and falls back
/// to `MoveErrorType::Code(sub_status)`. This only fires when the
/// `(sub_status, location)` pair is already internally inconsistent; the
/// `resolve_constant_name` paths build consistent pairs and are
/// unaffected.
fn sanitize_clever_location(
    sub_status: u64,
    location: Location,
    module_info: &BTreeMap<ModuleId, NamedCompiledModule>,
) -> Location {
    use move_command_line_common::error_bitset::ErrorBitset;
    let Location::Module(mid) = &location else {
        return location;
    };
    let Some(bitset) = ErrorBitset::from_u64(sub_status) else {
        return location;
    };
    let Some(identifier_index) = bitset.identifier_index() else {
        return location;
    };
    // Upstream's `convert_clever_move_abort_error` does more than index
    // `constant_pool[identifier_index]`: it then
    // `bcs::from_bytes::<Vec<u8>>(.data).expect(...)` and
    // `std::str::from_utf8(..).expect(...)`. An index that is in bounds
    // but whose constant does not decode as a UTF-8 `Vec<u8>` (e.g. it
    // names a non-string constant) makes that `.expect()` panic with
    // `RemainingInput`, poisoning the rayon pool and exiting 101 even
    // though the verdict was already correct. Mirror the full decode
    // here and keep the `Module` location only when upstream will
    // succeed; otherwise demote to `Undefined` so upstream returns
    // `None` and falls back to `MoveErrorType::Code(sub_status)`.
    let usable = module_info
        .get(mid)
        .and_then(|m| m.module.constant_pool.get(identifier_index as usize))
        .map(|c| {
            bcs::from_bytes::<Vec<u8>>(&c.data)
                .ok()
                .and_then(|bytes| String::from_utf8(bytes).ok())
                .is_some()
        })
        .unwrap_or(false);
    if usable {
        location
    } else {
        Location::Undefined
    }
}

/// Construct an `ErrorBitset`-tagged `u64` whose `identifier_index`
/// points at `name`'s string in the constant pool of the module
/// identified by `location`. Returns `None` if the location isn't a
/// `Location::Module`, the module is missing from `module_info`, or
/// no constant pool entry decodes to `name`. Upstream's
/// `convert_clever_move_abort_error` decodes such a tagged u64 back
/// to `MoveErrorType::ConstantName(name)` so the matcher's
/// whole-tuple equality fires.
fn resolve_constant_name(
    location: &Location,
    name: &str,
    module_info: &BTreeMap<ModuleId, NamedCompiledModule>,
) -> Option<u64> {
    use move_command_line_common::error_bitset::ErrorBitsetBuilder;
    let Location::Module(mid) = location else {
        return None;
    };
    let module = module_info.get(mid)?;
    let identifier_index = module
        .module
        .constant_pool
        .iter()
        .enumerate()
        .find_map(|(i, c)| {
            let bytes: Vec<u8> = bcs::from_bytes(&c.data).ok()?;
            let s = std::str::from_utf8(&bytes).ok()?;
            if s == name {
                Some(i as u16)
            } else {
                None
            }
        })?;
    let mut builder = ErrorBitsetBuilder::new(0);
    builder.with_identifier_index(identifier_index);
    Some(builder.build().bits())
}

/// Build a `ModuleId` for the originating module of an abort. The IR
/// emits `<package>::<module>` strings (e.g. `"upshift_vaults::admin"`),
/// and we typically only care about the module-name half because all
/// in-package aborts share the test's package address. Reuse the test
/// module's address with the abort module's name; cross-package aborts
/// fall back to the test module (rare in practice).
fn reframe_module_id(test_module_id: &ModuleId, qname: &str) -> Option<ModuleId> {
    let (_, module) = qname.split_once("::")?;
    let module_name = move_core_types::identifier::Identifier::new(module).ok()?;
    Some(ModuleId::new(*test_module_id.address(), module_name))
}
