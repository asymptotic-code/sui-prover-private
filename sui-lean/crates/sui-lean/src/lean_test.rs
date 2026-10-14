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
//! `.aborts` companion returns either legacy `Option MoveAbort` or the
//! new pipeline's `AbortResult AbortCode`. We don't need to re-render
//! anything per test — we only generate a tiny driver.
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
use crate::test_results::{Document as TestResultsDocument, Recorder, Status, TestRecord};
use anyhow::{Context, Result};
use lean_pipeline::ir::ObservedErrorKind;
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
#[allow(unused_imports)]
use std::process::{Command, Output, Stdio};
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, Mutex};
#[allow(unused_imports)]
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
    /// When true, `qualified_aborts` resolves to the new pipeline's
    /// `AbortResult AbortCode` shape rather than the legacy
    /// `Option MoveAbort` shape. The driver template switches accordingly.
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
    package_build_failures: &[String],
) -> Result<bool> {
    let recorder = Arc::new(Recorder::default());
    let result = run_lean_tests_inner(
        env,
        targets,
        output_dir,
        package_dir,
        build_config,
        test_config,
        new_pipeline,
        package_build_failures,
        recorder.clone(),
    );
    let write_result = write_test_results(test_config, &recorder);
    match (result, write_result) {
        (Ok(ok), Ok(())) => Ok(ok),
        (Err(error), Ok(())) => Err(error),
        (Ok(_), Err(error)) => Err(error),
        (Err(error), Err(write_error)) => Err(error.context(format!(
            "also failed to write structured test results: {write_error:#}"
        ))),
    }
}

#[allow(clippy::too_many_arguments)]
fn run_lean_tests_inner(
    env: &GlobalEnv,
    targets: &FunctionTargetsHolder,
    output_dir: &Path,
    package_dir: &Path,
    build_config: &BuildConfig,
    test_config: &crate::prove::TestConfig,
    new_pipeline: bool,
    package_build_failures: &[String],
    recorder: Arc<Recorder>,
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
    if let Some(filter) = config.filter.as_deref() {
        filter_test_plan(&mut plan, filter)?;
    }

    let needed_qnames = collect_test_qnames(&plan);
    if needed_qnames.is_empty() {
        require_successful_empty_plan_prebuild(package_build_failures)?;
        // Mirror `sui move test`: an empty test plan is success, reported
        // with the canonical zero-count summary line on stdout (exit 0).
        // Returning early also skips the pointless test-IR build and lake
        // invocation the bail used to prevent.
        eprintln!("no tests in plan");
        println!("Test result: OK. Total tests: 0; passed: 0; failed: 0");
        return Ok(true);
    }

    let mut legacy_program =
        (!new_pipeline).then(|| ProgramBuilder::new(env).build_for_test(targets));
    let new_declarations = if new_pipeline {
        match lean_pipeline::render::read_test_declarations(output_dir) {
            Ok(declarations) => Some(declarations),
            Err(error) => {
                let error = anyhow::anyhow!(
                    "reading new-pipeline test declaration index from {}: {error:?}",
                    output_dir.display()
                );
                record_selected_infrastructure(
                    &needed_qnames,
                    &recorder,
                    "test_declaration_manifest_invalid",
                    &error,
                );
                return Err(error);
            }
        }
    } else {
        move_prover_lean_backend::renderer::compute_namespace_overrides(
            legacy_program
                .as_mut()
                .expect("legacy test lookup has an IR program"),
        );
        None
    };
    let lookup_result = build_test_aborts_lookup(
        env,
        legacy_program.as_ref(),
        output_dir,
        &needed_qnames,
        new_declarations.as_ref(),
    );
    let (lookup, missing_reasons) = match lookup_result {
        Ok(result) => result,
        Err(error) => {
            record_selected_infrastructure(
                &needed_qnames,
                &recorder,
                "test_declaration_lookup_failed",
                &error,
            );
            return Err(error);
        }
    };

    let missing: Vec<String> = needed_qnames
        .iter()
        .filter(|q| !lookup.contains_key(*q))
        .cloned()
        .collect();
    for qname in &missing {
        let detail = missing_reasons
            .get(qname)
            .cloned()
            .unwrap_or_else(|| "no `.aborts` companion and no reason was recorded".into());
        recorder.record(TestRecord {
            name: qname.clone(),
            status: Status::Unsupported,
            reason_code: Some("driver_lookup_missing".into()),
            detail: Some(detail),
        });
    }
    if !missing.is_empty() {
        // A dropped test has no `.aborts` companion in the IR — usually a
        // function the stackless-bytecode pipeline pruned before IR
        // construction (e.g. it exercises a dynamic-field type the upstream
        // well-foundedness analysis rejects). Blocking the *entire* package
        // on a handful of untranslatable tests hides the ~100+ tests that
        // do translate, so we skip-and-report instead of bailing: the
        // dropped tests are removed from the plan and listed as unsupported,
        // and the runner proceeds with the rest. Unsupported tests are a
        // typed, failing outcome rather than silently reducing the test count.
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
            module_plan.tests.retain(|name, _| {
                !missing_set.contains(&format!("{}::{}::{}", addr, module, name))
            });
        }
        plan.module_tests.retain(|_, m| !m.tests.is_empty());

        if plan.module_tests.is_empty() {
            eprintln!("no translatable tests remain after skipping unsupported ones");
            println!("Test result: OK. Total tests: 0; passed: 0; failed: 0");
            report_unsupported_tests(&missing, &missing_reasons);
            return Ok(false);
        }
    }

    let abort_origins = if new_pipeline {
        match load_abort_origins(output_dir) {
            Ok(origins) => Arc::new(origins),
            Err(error) => {
                for qname in lookup.keys() {
                    recorder.record(TestRecord {
                        name: qname.clone(),
                        status: Status::Infra,
                        reason_code: Some("abort_origin_manifest_invalid".into()),
                        detail: Some(format!("{error:#}")),
                    });
                }
                ensure_all_results(&needed_qnames, &recorder);
                return Err(error);
            }
        }
    } else {
        Arc::new(BTreeMap::new())
    };

    if test_config.type_check_only {
        // tests-lake: only TYPE-CHECK the drivers (no execution). We bypass
        // the move-unit-test runner here -- its `#[expected_failure]`
        // handling would mis-report abort-expecting tests (which only abort
        // at RUN time) as failures. See `typecheck_drivers`.
        let ok = match typecheck_drivers(&lookup, output_dir) {
            Ok(ok) => ok,
            Err(error) => {
                record_typecheck_infrastructure(&lookup, &recorder, &error);
                ensure_all_results(&needed_qnames, &recorder);
                report_unsupported_tests(&missing, &missing_reasons);
                return Err(error).context("type-checking Lean test drivers");
            }
        };
        for qname in lookup.keys() {
            recorder.record(TestRecord {
                name: qname.clone(),
                status: if ok { Status::Pass } else { Status::Infra },
                reason_code: (!ok).then(|| "driver_typecheck_failed".into()),
                detail: (!ok).then(|| {
                    "the aggregate Lean driver module failed to type-check; individual failing drivers are not identifiable from this phase"
                        .into()
                }),
            });
        }
        ensure_all_results(&needed_qnames, &recorder);
        report_unsupported_tests(&missing, &missing_reasons);
        return Ok(ok && missing.is_empty());
    }
    let render_test_driver = make_driver_renderer(Arc::new(lookup));
    let module_info = Arc::new(plan.module_info.clone());
    let executor = Arc::new(LeanExecutor::new(
        output_dir.to_path_buf(),
        render_test_driver,
        module_info,
        abort_origins,
        new_pipeline,
        test_config.per_test_timeout_secs,
        recorder.clone(),
    ));
    let external_executor: Arc<dyn TestExecutor> = executor.clone();
    let config = config.with_external_executor(external_executor);

    let run_result =
        config.run_and_report_unit_tests(plan, DefaultVMTestSetup::legacy_default(), io::stdout());
    let (_writer, ok) = match run_result {
        Ok(result) => result,
        Err(error) => {
            ensure_all_results(&needed_qnames, &recorder);
            return Err(error).context("running upstream move-unit-test runner");
        }
    };
    report_unsupported_tests(&missing, &missing_reasons);
    let mut issues = executor.issues();
    sort_test_issues(&mut issues);
    for issue in &issues {
        println!(
            "[ {} ] {} -- {}",
            issue.kind.marker(),
            issue.qname,
            issue.detail
        );
    }
    ensure_all_results(&needed_qnames, &recorder);
    Ok(ok && missing.is_empty() && issues.is_empty())
}

fn require_successful_empty_plan_prebuild(package_build_failures: &[String]) -> Result<()> {
    anyhow::ensure!(
        package_build_failures.is_empty(),
        "the empty test plan has no drivers to gate generated Lean, and package type-checking failed:\n{}",
        package_build_failures.join("\n")
    );
    Ok(())
}

fn write_test_results(test_config: &crate::prove::TestConfig, recorder: &Recorder) -> Result<()> {
    let Some(path) = test_config.results_toml.as_deref() else {
        return Ok(());
    };
    let phase = if test_config.type_check_only {
        "typecheck"
    } else {
        "run"
    };
    TestResultsDocument::new(phase, recorder.records()).write_atomic(path)
}

fn ensure_all_results(expected: &BTreeSet<String>, recorder: &Recorder) {
    let recorded: BTreeSet<String> = recorder
        .records()
        .into_iter()
        .map(|record| record.name)
        .collect();
    for qname in expected.difference(&recorded) {
        recorder.record(TestRecord {
            name: qname.clone(),
            status: Status::Infra,
            reason_code: Some("runner_result_missing".into()),
            detail: Some("the test runner returned without classifying this selected test".into()),
        });
    }
}

fn record_typecheck_infrastructure(
    lookup: &BTreeMap<String, TestAbortsRef>,
    recorder: &Recorder,
    error: &anyhow::Error,
) {
    let detail = format!("{error:#}");
    for qname in lookup.keys() {
        recorder.record(TestRecord {
            name: qname.clone(),
            status: Status::Infra,
            reason_code: Some("driver_typecheck_infrastructure".into()),
            detail: Some(detail.clone()),
        });
    }
}

fn record_selected_infrastructure(
    qnames: &BTreeSet<String>,
    recorder: &Recorder,
    reason_code: &str,
    error: &anyhow::Error,
) {
    let detail = format!("{error:#}");
    for qname in qnames {
        recorder.record(TestRecord {
            name: qname.clone(),
            status: Status::Infra,
            reason_code: Some(reason_code.into()),
            detail: Some(detail.clone()),
        });
    }
}

fn load_abort_origins(output_dir: &Path) -> Result<BTreeMap<u64, ModuleId>> {
    let document =
        lean_pipeline::render::read_abort_origins_sidecar(output_dir).map_err(|error| {
            anyhow::anyhow!(
                "reading new-pipeline abort origin manifest from {}: {error:?}",
                output_dir.display()
            )
        })?;
    let mut origins = BTreeMap::new();
    let mut modules = BTreeSet::new();
    for origin in document.origins {
        let module_id = parse_addressed_module(&origin.module).map_err(|detail| {
            anyhow::anyhow!(
                "abort origin tag {} has invalid module `{}`: {}",
                origin.tag,
                origin.module,
                detail
            )
        })?;
        anyhow::ensure!(
            modules.insert(module_id.clone()),
            "abort origin manifest maps multiple tags to module `{}`",
            origin.module
        );
        origins.insert(origin.tag, module_id);
    }
    Ok(origins)
}

fn report_unsupported_tests(missing: &[String], reasons: &BTreeMap<String, String>) {
    for qname in missing {
        let reason = reasons
            .get(qname)
            .map(String::as_str)
            .unwrap_or("no `.aborts` companion and no reason was recorded");
        println!("[ UNSUPPORTED ] {qname} -- {reason}");
    }
}

fn sort_test_issues(issues: &mut [TestIssue]) {
    issues.sort_by(|a, b| {
        a.qname
            .cmp(&b.qname)
            .then_with(|| a.kind.marker().cmp(b.kind.marker()))
            .then_with(|| a.detail.cmp(&b.detail))
    });
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

fn filter_test_plan(plan: &mut TestPlan, filter: &str) -> Result<()> {
    let regex = regex::Regex::new(filter).context("compiling move-unit-test filter")?;
    for (module_id, module_plan) in &mut plan.module_tests {
        if module_id.name().as_str().contains(filter) {
            continue;
        }
        let rendered_module = if let Some(address_name) = plan
            .module_info
            .get(module_id)
            .and_then(|module| module.address_name())
        {
            format!("{}::{}", address_name, module_id.name())
        } else {
            module_id.short_str_lossless()
        };
        module_plan
            .tests
            .retain(|name, _| regex.is_match(&format!("{}::{}", rendered_module, name)));
    }
    plan.module_tests
        .retain(|_, module| !module.tests.is_empty());
    Ok(())
}

fn index_test_declarations(
    manifest: &lean_pipeline::render::TestDeclarations,
) -> Result<BTreeMap<(ModuleId, String), &lean_pipeline::render::TestDeclaration>> {
    let mut index = BTreeMap::new();
    let mut import_owners = BTreeMap::new();
    for declaration in &manifest.declarations {
        let module_id =
            parse_addressed_module(&declaration.addressed_module).map_err(|detail| {
                anyhow::anyhow!(
                    "invalid addressed module `{}` for test declaration `{}`: {}",
                    declaration.addressed_module,
                    declaration.function,
                    detail
                )
            })?;
        let canonical = format!(
            "{}::{}",
            module_id.address().to_hex_literal(),
            module_id.name()
        );
        if declaration.addressed_module != canonical {
            return Err(anyhow::anyhow!(
                "test declaration module `{}` is not canonical; expected `{}`",
                declaration.addressed_module,
                canonical
            ));
        }
        if let Some(owner) = import_owners.insert(
            declaration.import_path.as_str(),
            declaration.addressed_module.as_str(),
        ) {
            anyhow::ensure!(
                owner == declaration.addressed_module,
                "test declaration import `{}` aliases addressed modules `{}` and `{}`",
                declaration.import_path,
                owner,
                declaration.addressed_module
            );
        }
        let key = (module_id, declaration.function.clone());
        if index.insert(key, declaration).is_some() {
            return Err(anyhow::anyhow!(
                "duplicate test declaration for `{}::{}`",
                declaration.addressed_module,
                declaration.function
            ));
        }
    }
    Ok(index)
}

fn lean_file_for_import(
    output_dir: &Path,
    import_path: &str,
) -> std::result::Result<PathBuf, String> {
    let mut path = output_dir.to_path_buf();
    for component in import_path.split('.') {
        if component.is_empty() || component.contains('/') || component.contains('\\') {
            return Err(format!("invalid Lean import path `{import_path}`"));
        }
        path.push(component);
    }
    path.set_extension("lean");
    Ok(path)
}

/// Build `<addr>::<module>::<function> → TestAbortsRef` for each selected
/// test. The new pipeline resolves renderer-owned declarations by addressed
/// module identity; the legacy pipeline retains its IR-based lookup.
fn build_test_aborts_lookup(
    env: &GlobalEnv,
    legacy_program: Option<&intermediate_theorem_format::Program>,
    output_dir: &Path,
    needed_qnames: &BTreeSet<String>,
    new_declarations: Option<&lean_pipeline::render::TestDeclarations>,
) -> Result<(BTreeMap<String, TestAbortsRef>, BTreeMap<String, String>)> {
    let declaration_index = new_declarations.map(index_test_declarations).transpose()?;
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

            if let Some(declaration_index) = declaration_index.as_ref() {
                let module_id = parse_addressed_module(&format!(
                    "{}::{}",
                    module.self_address().to_hex_literal(),
                    module_name
                ))
                .expect("move-model module identity is valid");
                let Some(declaration) = declaration_index.get(&(module_id, func_name.clone()))
                else {
                    reasons.insert(
                        qname,
                        format!(
                            "no new-pipeline test declaration indexed for `{}::{}::{}`",
                            module.self_address().to_hex_literal(),
                            module_name,
                            func_name
                        ),
                    );
                    continue;
                };
                let lean_path = match lean_file_for_import(output_dir, &declaration.import_path) {
                    Ok(path) => path,
                    Err(detail) => {
                        reasons.insert(qname, detail);
                        continue;
                    }
                };
                if !lean_path.is_file() {
                    reasons.insert(
                        qname,
                        format!(
                            "Lean file indexed by renderer is missing on disk: {}",
                            lean_path.display()
                        ),
                    );
                    continue;
                }
                if declaration.lean_declaration.trim().is_empty() {
                    reasons.insert(
                        qname,
                        "renderer indexed an empty Lean declaration name".into(),
                    );
                    continue;
                }
                out.insert(
                    qname,
                    TestAbortsRef {
                        import_path: declaration.import_path.clone(),
                        qualified_aborts: declaration.lean_declaration.clone(),
                        new_pipeline_shape: true,
                        needs_world: declaration.needs_world,
                        ghost_param_count: declaration.ghost_param_count,
                    },
                );
                continue;
            }

            let program = legacy_program.expect("legacy test lookup has an IR program");
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

            let namespace = move_prover_lean_backend::renderer::get_namespace(program, f.module_id);
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
                    new_pipeline_shape: false,
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
    Ok((out, reasons))
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
    let entries: Vec<&TestAbortsRef> = lookup.values().collect();
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
        // `noncomputable`: the probe's job is ELABORATION coverage (arity /
        // ghost-param / type agreement with the `.aborts` face), not
        // executability. Rendered modules sit in a `noncomputable section`
        // (transparent quantifier helpers pull in Classical), so a plain
        // `def` fails compilation with `dependsOnNoncomputable` for every
        // test whose `.aborts` transitively touches one -- run-mode
        // evaluability is `tests-run`'s to report, not this probe's.
        let cases = if e.new_pipeline_shape {
            "| .NoAbort => true | .Aborted _ => false"
        } else {
            "| none => true | some _ => false"
        };
        defs.push_str(&format!(
            "noncomputable def __driver_typecheck_{i} : Bool := match {call} with {cases}\n"
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
                s.push_str(
                    "      IO.println (\"{\\\"verdict\\\":\\\"abort\\\",\\\"code\\\":\" ++ toString a.code.toNat ++ \",\\\"origin_tag\\\":\" ++ toString a.origin_tag.toNat ++ \",\\\"error_kind\\\":\" ++ toString a.error_kind.toNat ++ \"}\")\n",
                );
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
                // function that raised the abort. Preserve an empty value:
                // older literals and natives do not provide an origin, and
                // attributing those aborts to the test module would invent
                // precision the driver did not observe.
                s.push_str("      let mod := a.module\n");
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

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum TestIssueKind {
    Timeout,
    Unsupported,
    Infrastructure,
}

impl TestIssueKind {
    fn marker(self) -> &'static str {
        match self {
            Self::Timeout => "TIMEOUT",
            Self::Unsupported => "UNSUPPORTED",
            Self::Infrastructure => "INFRA",
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct TestIssue {
    kind: TestIssueKind,
    qname: String,
    detail: String,
}

enum ExecutionOutcome {
    Verdict(Verdict),
    TimedOut { timeout_secs: u64 },
}

pub struct LeanExecutor {
    output_dir: PathBuf,
    render: RenderTestDriver,
    seq: AtomicU64,
    /// Per-module compiled units. Used only to verify that an observed
    /// clever abort code is safe for the upstream runner to decode. We
    /// never manufacture a code from an expected-failure annotation.
    module_info: Arc<BTreeMap<ModuleId, NamedCompiledModule>>,
    abort_origins: Arc<BTreeMap<u64, ModuleId>>,
    require_origin_tag: bool,
    /// Per-test wall-clock timeout in seconds. `0` disables the
    /// timeout (the default). When non-zero, each
    /// `lake env lean --run` invocation is enforced natively via
    /// [`run_with_timeout`] (process-group SIGKILL on expiry — no
    /// external `timeout(1)` dependency). Expiry is reported as an
    /// infrastructure timeout and never synthesized into a Move abort.
    per_test_timeout_secs: u64,
    issues: Mutex<Vec<TestIssue>>,
    recorder: Arc<Recorder>,
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
fn run_with_timeout(
    mut cmd: Command,
    driver_rel: &str,
    timeout_secs: u64,
) -> Result<Option<Output>> {
    use std::io::Read;
    #[cfg(unix)]
    use std::os::unix::process::CommandExt;

    cmd.stdout(Stdio::piped()).stderr(Stdio::piped());
    #[cfg(unix)]
    cmd.process_group(0);
    let mut child = cmd
        .spawn()
        .with_context(|| format!("spawning `lake env lean --run {driver_rel}`"))?;
    let pid = child.id();

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
            libc::kill(-(pid as i32), libc::SIGKILL);
        }
        #[cfg(windows)]
        let _ = Command::new("taskkill")
            .args(["/PID", &pid.to_string(), "/T", "/F"])
            .status();
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
        abort_origins: Arc<BTreeMap<u64, ModuleId>>,
        require_origin_tag: bool,
        per_test_timeout_secs: u64,
        recorder: Arc<Recorder>,
    ) -> Self {
        Self {
            output_dir,
            render,
            seq: AtomicU64::new(0),
            module_info,
            abort_origins,
            require_origin_tag,
            per_test_timeout_secs,
            issues: Mutex::new(Vec::new()),
            recorder,
        }
    }

    fn record_issue(&self, kind: TestIssueKind, qname: String, detail: String) {
        self.issues
            .lock()
            .expect("LeanExecutor issue mutex poisoned")
            .push(TestIssue {
                kind,
                qname,
                detail,
            });
    }

    fn issues(&self) -> Vec<TestIssue> {
        self.issues
            .lock()
            .expect("LeanExecutor issue mutex poisoned")
            .clone()
    }

    fn run_one(
        &self,
        module_id: &ModuleId,
        function_name: &str,
        arguments: &[MoveValue],
    ) -> Result<ExecutionOutcome> {
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
                    return Ok(ExecutionOutcome::TimedOut {
                        timeout_secs: self.per_test_timeout_secs,
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
            return Ok(ExecutionOutcome::Verdict(verdict));
        }

        // No JSON verdict — the driver aborted before printing one. Synthesize
        // a structured abort verdict from the stderr marker so the test doesn't
        // get reported as an internal error.
        if let Some(verdict) = parse_move_abort_marker(&stderr) {
            return Ok(ExecutionOutcome::Verdict(verdict));
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
                origin_tag: None,
                error_kind: None,
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
        let qname = format!(
            "{}::{}::{}",
            module_id.address().to_canonical_string(true),
            module_id.name(),
            function_name,
        );
        let expected_failure = test_plan
            .tests
            .get(function_name)
            .and_then(|tc: &TestCase| tc.expected_failure.as_ref());
        let result = match self.run_one(&module_id, function_name, &arguments) {
            Ok(ExecutionOutcome::Verdict(verdict)) => {
                match verdict_to_vm_result(
                    verdict,
                    module_id.clone(),
                    expected_failure,
                    &self.module_info,
                    &self.abort_origins,
                    self.require_origin_tag,
                ) {
                    Ok(result) => {
                        self.recorder.record(classify_vm_result(
                            &qname,
                            &result,
                            expected_failure,
                            &self.module_info,
                        ));
                        result
                    }
                    Err(detail) => {
                        self.record_issue(
                            TestIssueKind::Unsupported,
                            qname.clone(),
                            detail.clone(),
                        );
                        self.recorder.record(TestRecord {
                            name: qname,
                            status: Status::Unsupported,
                            reason_code: Some("observed_error_unsupported".into()),
                            detail: Some(detail.clone()),
                        });
                        infrastructure_vm_error(
                            module_id,
                            format!("unsupported Lean verdict: {detail}"),
                        )
                    }
                }
            }
            Ok(ExecutionOutcome::TimedOut { timeout_secs }) => {
                let detail = format!("Lean driver exceeded {timeout_secs}s wall-clock timeout");
                self.record_issue(TestIssueKind::Timeout, qname.clone(), detail.clone());
                self.recorder.record(TestRecord {
                    name: qname,
                    status: Status::Timeout,
                    reason_code: Some("driver_timeout".into()),
                    detail: Some(detail.clone()),
                });
                infrastructure_vm_error(module_id, detail)
            }
            Err(err) => {
                let detail = format!("Lean dispatcher failure: {err:#}");
                self.record_issue(TestIssueKind::Infrastructure, qname.clone(), detail.clone());
                self.recorder.record(TestRecord {
                    name: qname,
                    status: Status::Infra,
                    reason_code: Some("driver_infrastructure".into()),
                    detail: Some(detail.clone()),
                });
                infrastructure_vm_error(module_id, detail)
            }
        };
        let info = TestRunInfo::new(started.elapsed(), 0, None);
        (result, info)
    }
}

fn infrastructure_vm_error(module_id: ModuleId, message: String) -> VMResult<ValueFrame> {
    Err(
        PartialVMError::new(StatusCode::UNKNOWN_INVARIANT_VIOLATION_ERROR)
            .with_message(message)
            .finish(Location::Module(module_id)),
    )
}

fn classify_vm_result(
    qname: &str,
    result: &VMResult<ValueFrame>,
    expected_failure: Option<&ExpectedFailure>,
    module_info: &BTreeMap<ModuleId, NamedCompiledModule>,
) -> TestRecord {
    let failure = |reason_code: &str, detail: String| TestRecord {
        name: qname.to_string(),
        status: Status::Fail,
        reason_code: Some(reason_code.into()),
        detail: Some(detail),
    };
    let passed = || TestRecord {
        name: qname.to_string(),
        status: Status::Pass,
        reason_code: None,
        detail: None,
    };

    match result {
        Ok(_) => match expected_failure {
            None => passed(),
            Some(expected) => failure(
                "expected_failure_not_observed",
                format!("expected failure {expected:?}, but the Lean driver returned normally"),
            ),
        },
        Err(error) => {
            let sub_status = error
                .sub_status()
                .and_then(|code| observed_move_error_type(code, error.location(), module_info));
            let actual =
                ExpectedMoveError(error.major_status(), sub_status, error.location().clone());
            let matches = match expected_failure {
                Some(ExpectedFailure::Expected) => true,
                Some(ExpectedFailure::ExpectedWithError(expected)) => expected == &actual,
                Some(ExpectedFailure::ExpectedWithCodeDEPRECATED(expected)) => {
                    actual.0 == StatusCode::ABORTED && actual.1.as_ref() == Some(expected)
                }
                None => false,
            };
            if matches {
                passed()
            } else if let Some(expected) = expected_failure {
                failure(
                    "wrong_error",
                    format!("expected {expected:?}, observed {actual:?}"),
                )
            } else {
                failure("unexpected_error", format!("observed {actual:?}"))
            }
        }
    }
}

fn observed_move_error_type(
    code: u64,
    location: &Location,
    module_info: &BTreeMap<ModuleId, NamedCompiledModule>,
) -> Option<MoveErrorType> {
    use move_command_line_common::error_bitset::ErrorBitset;

    let Some(bitset) = ErrorBitset::from_u64(code) else {
        return Some(MoveErrorType::Code(code));
    };
    let Location::Module(module_id) = location else {
        return None;
    };
    let identifier_index = bitset.identifier_index()?;
    let constant = module_info
        .get(module_id)?
        .module
        .constant_pool
        .get(identifier_index as usize)?;
    let bytes = bcs::from_bytes::<Vec<u8>>(&constant.data).ok()?;
    String::from_utf8(bytes)
        .ok()
        .map(MoveErrorType::ConstantName)
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
        /// Plumbed from `MoveAbort.raiseAbort` on the stderr marker path.
        /// Missing origins remain absent rather than being defaulted.
        #[serde(default)]
        module: Option<String>,
        /// Test-only new-pipeline provenance tag. Tag zero is reserved for
        /// an abort whose exact source module could not be represented.
        #[serde(default)]
        origin_tag: Option<u64>,
        #[serde(default)]
        error_kind: Option<u64>,
    },
}

/// Map an observed driver verdict to the upstream runner's `VMResult`.
/// The observed abort code is never rewritten to agree with a test's
/// expected-failure annotation. An originating module is used only when
/// it can be mapped exactly to the test module's `ModuleId`; otherwise
/// the imprecision is surfaced as an unsupported result.
fn verdict_to_vm_result(
    verdict: Verdict,
    module_id: ModuleId,
    expected_failure: Option<&ExpectedFailure>,
    module_info: &BTreeMap<ModuleId, NamedCompiledModule>,
    abort_origins: &BTreeMap<u64, ModuleId>,
    require_origin_tag: bool,
) -> std::result::Result<VMResult<ValueFrame>, String> {
    match verdict {
        Verdict::Ok => Ok(Ok(ValueFrame::empty())),
        Verdict::Abort {
            code,
            module,
            origin_tag,
            error_kind,
            ..
        } => {
            let error_kind = match error_kind {
                Some(tag) => ObservedErrorKind::try_from(tag)
                    .map_err(|tag| format!("unknown observed error kind {tag}"))?,
                None if require_origin_tag => {
                    return Err("new-pipeline failure verdict omitted its error kind".to_string())
                }
                None => ObservedErrorKind::Abort,
            };
            if error_kind == ObservedErrorKind::Unknown {
                return Err("observed error kind 0 denotes an unknown VM failure".to_string());
            }
            let location = match origin_tag {
                Some(0) => {
                    return Err("abort origin tag 0 denotes an unknown source module".to_string())
                }
                Some(tag) => {
                    Location::Module(abort_origins.get(&tag).cloned().ok_or_else(|| {
                        format!("abort origin tag {tag} is absent from the manifest")
                    })?)
                }
                None if require_origin_tag => {
                    return Err("new-pipeline abort verdict omitted its origin tag".to_string())
                }
                None => observed_abort_location(module.as_deref(), module_info)?,
            };
            let error = match error_kind {
                ObservedErrorKind::Abort => {
                    validate_abort_precision(code, &location, expected_failure, module_info)?;
                    PartialVMError::new(StatusCode::ABORTED).with_sub_status(code)
                }
                ObservedErrorKind::Arithmetic => {
                    if code != 0 {
                        return Err(format!(
                            "arithmetic failure payload must use code 0, observed {code}"
                        ));
                    }
                    PartialVMError::new(StatusCode::ARITHMETIC_ERROR)
                }
                ObservedErrorKind::VectorOperation => {
                    if !matches!(code, 1..=3) {
                        return Err(format!("unsupported vector-operation minor code {code}"));
                    }
                    PartialVMError::new(StatusCode::VECTOR_OPERATION_ERROR).with_sub_status(code)
                }
                ObservedErrorKind::Unknown => unreachable!(),
            };
            Ok(Err(error.finish(location)))
        }
    }
}

fn observed_abort_location(
    observed: Option<&str>,
    module_info: &BTreeMap<ModuleId, NamedCompiledModule>,
) -> Result<Location, String> {
    let Some(observed) = observed.filter(|value| !value.is_empty()) else {
        return Ok(Location::Undefined);
    };
    let Some((qualifier, observed_module)) = observed.rsplit_once("::") else {
        return Err(format!(
            "abort origin `{observed}` is not a fully qualified Move module"
        ));
    };
    if qualifier.starts_with("0x") {
        return parse_addressed_module(observed).map(Location::Module);
    }

    let module_name = move_core_types::identifier::Identifier::new(observed_module)
        .map_err(|_| format!("abort origin `{observed}` has an invalid module name"))?;

    let mut candidates = module_info.iter().filter_map(|(module_id, named)| {
        let package_matches = named
            .package_name()
            .is_some_and(|package| package.to_string() == qualifier);
        (package_matches && module_id.name().as_str() == observed_module).then(|| module_id.clone())
    });
    let Some(module_id) = candidates.next() else {
        return Err(format!(
            "abort origin `{observed}` cannot be resolved to an addressed module in the test plan"
        ));
    };
    if candidates.next().is_some() {
        return Err(format!(
            "abort origin `{observed}` is ambiguous across multiple addressed modules"
        ));
    }
    Ok(Location::Module(module_id))
}

fn parse_addressed_module(observed: &str) -> Result<ModuleId, String> {
    let Some((address, module)) = observed.rsplit_once("::") else {
        return Err("not a fully qualified Move module".into());
    };
    let address = move_core_types::account_address::AccountAddress::from_hex_literal(address)
        .map_err(|_| "invalid account address".to_string())?;
    let module = move_core_types::identifier::Identifier::new(module)
        .map_err(|_| "invalid module identifier".to_string())?;
    Ok(ModuleId::new(address, module))
}

fn validate_abort_precision(
    code: u64,
    location: &Location,
    expected_failure: Option<&ExpectedFailure>,
    module_info: &BTreeMap<ModuleId, NamedCompiledModule>,
) -> Result<(), String> {
    use move_command_line_common::error_bitset::ErrorBitset;

    if let Some(bitset) = ErrorBitset::from_u64(code) {
        let Location::Module(module_id) = location else {
            return Err(format!(
                "clever abort code {code} cannot be decoded without an exact originating module"
            ));
        };
        if let Some(identifier_index) = bitset.identifier_index() {
            if identifier_index as usize
                >= module_info
                    .get(module_id)
                    .map(|module| module.module.constant_pool.len())
                    .unwrap_or_default()
                || observed_move_error_type(code, location, module_info).is_none()
            {
                return Err(format!(
                    "clever abort code {code} cannot be decoded safely in `{module_id}`"
                ));
            }
        }
    }

    let expects_named_code = matches!(
        expected_failure,
        Some(ExpectedFailure::ExpectedWithCodeDEPRECATED(
            MoveErrorType::ConstantName(_)
        )) | Some(ExpectedFailure::ExpectedWithError(ExpectedMoveError(
            _,
            Some(MoveErrorType::ConstantName(_)),
            _
        )))
    );
    if expects_named_code && matches!(location, Location::Undefined) {
        return Err(
            "named abort code cannot be matched without an exact originating module".into(),
        );
    }

    if let Some(ExpectedFailure::ExpectedWithError(ExpectedMoveError(
        _,
        _,
        Location::Module(expected_module),
    ))) = expected_failure
    {
        if matches!(location, Location::Undefined) {
            return Err(format!(
                "expected abort location `{expected_module}` is exact, but the driver did not report an exact origin"
            ));
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use move_core_types::{account_address::AccountAddress, identifier::Identifier};

    fn module_id(name: &str) -> ModuleId {
        ModuleId::new(AccountAddress::ZERO, Identifier::new(name).unwrap())
    }

    #[test]
    fn new_pipeline_driver_reports_typed_failure_and_origin_tag() {
        let lookup = BTreeMap::from([(
            "0x0::tests::test_abort".to_string(),
            TestAbortsRef {
                import_path: "Pkg.Tests".to_string(),
                qualified_aborts: "Pkg.Tests.test_abort.aborts".to_string(),
                new_pipeline_shape: true,
                needs_world: false,
                ghost_param_count: 0,
            },
        )]);
        let render = make_driver_renderer(Arc::new(lookup));
        let driver = render("0x0::tests::test_abort", &[]).expect("render driver");

        assert!(driver.contains(
            r#"{\"verdict\":\"abort\",\"code\":" ++ toString a.code.toNat ++ ",\"origin_tag\":" ++ toString a.origin_tag.toNat ++ ",\"error_kind\":" ++ toString a.error_kind.toNat"#
        ));
        assert!(!driver.contains("\\\"module\\\":"));
        assert!(!driver.contains("\\\"source\\\":"));
    }

    #[test]
    fn new_pipeline_declarations_join_by_addressed_module() {
        let declaration = lean_pipeline::render::TestDeclaration {
            addressed_module: "0x0::tests".into(),
            function: "test_abort".into(),
            import_path: "Rendered.Tests".into(),
            lean_declaration: "Rendered.Tests.test_abort.aborts".into(),
            needs_world: false,
            ghost_param_count: 0,
        };
        let manifest = lean_pipeline::render::TestDeclarations {
            schema_version: 1,
            declarations: vec![declaration],
        };
        let index = index_test_declarations(&manifest).unwrap();
        let indexed = index
            .get(&(module_id("tests"), "test_abort".to_string()))
            .unwrap();

        assert_eq!(indexed.import_path, "Rendered.Tests");
        assert_eq!(indexed.lean_declaration, "Rendered.Tests.test_abort.aborts");
        assert_eq!(
            lean_file_for_import(Path::new("/tmp/output"), &indexed.import_path).unwrap(),
            PathBuf::from("/tmp/output/Rendered/Tests.lean")
        );
    }

    #[test]
    fn new_pipeline_declarations_require_canonical_address_identity() {
        let manifest = lean_pipeline::render::TestDeclarations {
            schema_version: 1,
            declarations: vec![lean_pipeline::render::TestDeclaration {
                addressed_module: "0x00::tests".into(),
                function: "test_abort".into(),
                import_path: "Rendered.Tests".into(),
                lean_declaration: "Rendered.Tests.test_abort.aborts".into(),
                needs_world: false,
                ghost_param_count: 0,
            }],
        };

        assert!(index_test_declarations(&manifest)
            .unwrap_err()
            .to_string()
            .contains("is not canonical"));
    }

    #[test]
    fn new_pipeline_declarations_reject_import_aliases_across_addresses() {
        let manifest = lean_pipeline::render::TestDeclarations {
            schema_version: 1,
            declarations: vec![
                lean_pipeline::render::TestDeclaration {
                    addressed_module: "0x2::tests".into(),
                    function: "first".into(),
                    import_path: "Rendered.Tests".into(),
                    lean_declaration: "Rendered.Tests.first.aborts".into(),
                    needs_world: false,
                    ghost_param_count: 0,
                },
                lean_pipeline::render::TestDeclaration {
                    addressed_module: "0x3::tests".into(),
                    function: "second".into(),
                    import_path: "Rendered.Tests".into(),
                    lean_declaration: "Rendered.Tests.second.aborts".into(),
                    needs_world: false,
                    ghost_param_count: 0,
                },
            ],
        };

        assert!(index_test_declarations(&manifest)
            .unwrap_err()
            .to_string()
            .contains("aliases addressed modules"));
    }

    #[test]
    fn typecheck_infrastructure_failure_is_written_to_toml() {
        let lookup = BTreeMap::from([(
            "0x0::tests::test_abort".to_string(),
            TestAbortsRef {
                import_path: "Rendered.Tests".into(),
                qualified_aborts: "Rendered.Tests.test_abort.aborts".into(),
                new_pipeline_shape: true,
                needs_world: false,
                ghost_param_count: 0,
            },
        )]);
        let recorder = Recorder::default();
        record_typecheck_infrastructure(
            &lookup,
            &recorder,
            &anyhow::anyhow!("could not start lake"),
        );
        let output = tempfile::tempdir().unwrap();
        let results_path = output.path().join("test_results.toml");
        let config = crate::prove::TestConfig {
            type_check_only: true,
            results_toml: Some(results_path.clone()),
            ..crate::prove::TestConfig::default()
        };

        write_test_results(&config, &recorder).unwrap();

        let results = std::fs::read_to_string(results_path).unwrap();
        assert!(results.contains("phase = \"typecheck\""));
        assert!(results.contains("infra = 1"));
        assert!(results.contains("reason_code = \"driver_typecheck_infrastructure\""));
        assert!(results.contains("detail = \"could not start lake\""));
    }

    #[test]
    fn declaration_manifest_failure_is_written_for_every_selected_test() {
        let recorder = Recorder::default();
        let qnames = BTreeSet::from(["0x0::tests::a".to_string(), "0x0::tests::b".to_string()]);
        record_selected_infrastructure(
            &qnames,
            &recorder,
            "test_declaration_manifest_invalid",
            &anyhow::anyhow!("bad manifest\nsecond line\n"),
        );
        let output = tempfile::tempdir().unwrap();
        let results_path = output.path().join("test_results.toml");
        let config = crate::prove::TestConfig {
            results_toml: Some(results_path.clone()),
            ..crate::prove::TestConfig::default()
        };

        write_test_results(&config, &recorder).unwrap();

        let results = std::fs::read_to_string(results_path).unwrap();
        assert!(results.contains("selected = 2"));
        assert!(results.contains("infra = 2"));
        assert_eq!(
            results
                .matches("reason_code = \"test_declaration_manifest_invalid\"")
                .count(),
            2
        );
        assert!(results.contains("second line"));
    }

    #[test]
    fn timeout_infrastructure_error_is_not_a_move_abort() {
        let err = match infrastructure_vm_error(module_id("tests"), "timed out".into()) {
            Ok(_) => panic!("infrastructure error unexpectedly succeeded"),
            Err(err) => err,
        };
        assert_eq!(
            err.major_status(),
            StatusCode::UNKNOWN_INVARIANT_VIOLATION_ERROR
        );
        assert_ne!(err.major_status(), StatusCode::ABORTED);
        assert_eq!(err.sub_status(), None);
    }

    #[cfg(windows)]
    #[test]
    fn windows_driver_timeout_terminates_the_process_tree() {
        let mut cmd = Command::new("cmd.exe");
        cmd.args(["/C", "ping.exe -n 61 127.0.0.1"]);
        let started = Instant::now();
        let output = run_with_timeout(cmd, "timeout regression", 1).unwrap();
        assert!(output.is_none());
        assert!(started.elapsed() < Duration::from_secs(15));
    }

    #[test]
    fn observed_abort_is_not_rewritten_to_expected_annotation() {
        let module_id = module_id("tests");
        let expected = ExpectedFailure::ExpectedWithError(ExpectedMoveError(
            StatusCode::ABORTED,
            Some(MoveErrorType::Code(7)),
            Location::Module(module_id.clone()),
        ));
        let result = verdict_to_vm_result(
            Verdict::Abort {
                code: 42,
                source: None,
                module: Some(format!(
                    "{}::tests",
                    module_id.address().to_canonical_string(true)
                )),
                origin_tag: None,
                error_kind: None,
            },
            module_id.clone(),
            Some(&expected),
            &BTreeMap::new(),
            &BTreeMap::new(),
            false,
        )
        .unwrap();
        let err = match result {
            Ok(_) => panic!("abort verdict unexpectedly succeeded"),
            Err(err) => err,
        };
        assert_eq!(err.sub_status(), Some(42));
        assert_eq!(err.location(), &Location::Module(module_id));
    }

    #[test]
    fn missing_abort_origin_is_explicitly_unsupported_for_exact_location() {
        let module_id = module_id("tests");
        let expected = ExpectedFailure::ExpectedWithError(ExpectedMoveError(
            StatusCode::ABORTED,
            Some(MoveErrorType::Code(42)),
            Location::Module(module_id.clone()),
        ));
        let result = verdict_to_vm_result(
            Verdict::Abort {
                code: 42,
                source: None,
                module: None,
                origin_tag: None,
                error_kind: None,
            },
            module_id,
            Some(&expected),
            &BTreeMap::new(),
            &BTreeMap::new(),
            false,
        );
        assert!(result
            .unwrap_err()
            .contains("did not report an exact origin"));
    }

    #[test]
    fn addressed_abort_origin_is_parsed_not_string_compared() {
        let module_id = module_id("tests");
        let result = verdict_to_vm_result(
            Verdict::Abort {
                code: 42,
                source: None,
                module: Some("0x00::tests".into()),
                origin_tag: None,
                error_kind: None,
            },
            module_id.clone(),
            None,
            &BTreeMap::new(),
            &BTreeMap::new(),
            false,
        )
        .unwrap();
        let err = match result {
            Ok(_) => panic!("abort verdict unexpectedly succeeded"),
            Err(err) => err,
        };
        assert_eq!(err.location(), &Location::Module(module_id));
    }

    #[test]
    fn package_named_abort_origin_is_not_guessed_without_metadata() {
        let result = verdict_to_vm_result(
            Verdict::Abort {
                code: 42,
                source: None,
                module: Some("pkg::tests".into()),
                origin_tag: None,
                error_kind: None,
            },
            module_id("tests"),
            None,
            &BTreeMap::new(),
            &BTreeMap::new(),
            false,
        );
        assert!(result
            .unwrap_err()
            .contains("cannot be resolved to an addressed module"));
    }

    #[test]
    fn new_pipeline_abort_uses_manifest_tag_not_driver_text() {
        let source = module_id("source");
        let mut origins = BTreeMap::new();
        origins.insert(7, source.clone());
        let result = verdict_to_vm_result(
            Verdict::Abort {
                code: 42,
                source: None,
                module: Some("0x0::wrong".into()),
                origin_tag: Some(7),
                error_kind: Some(ObservedErrorKind::Abort.tag()),
            },
            module_id("test"),
            None,
            &BTreeMap::new(),
            &origins,
            true,
        )
        .unwrap();
        let error = result.unwrap_err();
        assert_eq!(error.location(), &Location::Module(source));
    }

    #[test]
    fn new_pipeline_typed_vm_failures_preserve_major_status() {
        let source = module_id("source");
        let origins = BTreeMap::from([(7, source.clone())]);
        for (error_kind, code, expected_status, expected_sub_status) in [
            (
                ObservedErrorKind::Arithmetic,
                0,
                StatusCode::ARITHMETIC_ERROR,
                None,
            ),
            (
                ObservedErrorKind::VectorOperation,
                2,
                StatusCode::VECTOR_OPERATION_ERROR,
                Some(2),
            ),
        ] {
            let result = verdict_to_vm_result(
                Verdict::Abort {
                    code,
                    source: None,
                    module: None,
                    origin_tag: Some(7),
                    error_kind: Some(error_kind.tag()),
                },
                module_id("test"),
                None,
                &BTreeMap::new(),
                &origins,
                true,
            )
            .expect("typed failure is supported");
            let error = result.unwrap_err();
            assert_eq!(error.major_status(), expected_status);
            assert_eq!(error.sub_status(), expected_sub_status);
            assert_eq!(error.location(), &Location::Module(source.clone()));
        }
    }

    #[test]
    fn new_pipeline_rejects_unknown_or_malformed_error_kinds() {
        let origins = BTreeMap::from([(7, module_id("source"))]);
        for (error_kind, code) in [
            (Some(ObservedErrorKind::Unknown.tag()), 0),
            (None, 0),
            (Some(99), 0),
            (Some(ObservedErrorKind::Arithmetic.tag()), 1),
            (Some(ObservedErrorKind::VectorOperation.tag()), 4),
        ] {
            let result = verdict_to_vm_result(
                Verdict::Abort {
                    code,
                    source: None,
                    module: None,
                    origin_tag: Some(7),
                    error_kind,
                },
                module_id("test"),
                None,
                &BTreeMap::new(),
                &origins,
                true,
            );
            assert!(
                result.is_err(),
                "error kind {error_kind:?} with code {code} was accepted"
            );
        }
    }

    #[test]
    fn new_pipeline_unknown_or_missing_origin_tag_is_unsupported() {
        for origin_tag in [Some(0), Some(9), None] {
            let result = verdict_to_vm_result(
                Verdict::Abort {
                    code: 42,
                    source: None,
                    module: None,
                    origin_tag,
                    error_kind: Some(ObservedErrorKind::Abort.tag()),
                },
                module_id("test"),
                None,
                &BTreeMap::new(),
                &BTreeMap::new(),
                true,
            );
            assert!(result.is_err(), "origin tag {origin_tag:?} was accepted");
        }
    }

    #[test]
    fn clever_abort_without_identifier_index_is_a_classifiable_error() {
        let source = module_id("source");
        let mut origins = BTreeMap::new();
        origins.insert(7, source.clone());
        let result = verdict_to_vm_result(
            Verdict::Abort {
                code: 13_906_834_565_185_404_927,
                source: None,
                module: None,
                origin_tag: Some(7),
                error_kind: Some(ObservedErrorKind::Abort.tag()),
            },
            module_id("test"),
            None,
            &BTreeMap::new(),
            &origins,
            true,
        )
        .expect("clever abort without a named identifier is still precise");
        let error = result.unwrap_err();
        assert_eq!(error.location(), &Location::Module(source));
    }

    #[test]
    fn structured_result_matches_upstream_expected_failure_semantics() {
        let module = module_id("tests");
        let observed = Err(PartialVMError::new(StatusCode::ABORTED)
            .with_sub_status(42)
            .finish(Location::Module(module.clone())));
        let expected = ExpectedFailure::ExpectedWithError(ExpectedMoveError(
            StatusCode::ABORTED,
            Some(MoveErrorType::Code(42)),
            Location::Module(module),
        ));
        assert_eq!(
            classify_vm_result("test", &observed, Some(&expected), &BTreeMap::new()).status,
            Status::Pass
        );
        assert_eq!(
            classify_vm_result("test", &observed, None, &BTreeMap::new()).status,
            Status::Fail
        );
        assert_eq!(
            classify_vm_result(
                "test",
                &Ok(ValueFrame::empty()),
                Some(&expected),
                &BTreeMap::new()
            )
            .status,
            Status::Fail
        );
    }

    #[test]
    fn empty_test_plan_requires_a_successful_package_build() {
        require_successful_empty_plan_prebuild(&[]).unwrap();
        let error = require_successful_empty_plan_prebuild(&[
            "`lake build Empty` failed: type error".into(),
        ])
        .unwrap_err();
        assert!(error
            .to_string()
            .contains("no drivers to gate generated Lean"));
        assert!(error.to_string().contains("lake build Empty"));
    }

    #[test]
    fn issue_markers_are_sorted_deterministically() {
        let mut issues = vec![
            TestIssue {
                kind: TestIssueKind::Timeout,
                qname: "z".into(),
                detail: "later".into(),
            },
            TestIssue {
                kind: TestIssueKind::Unsupported,
                qname: "a".into(),
                detail: "first".into(),
            },
        ];
        sort_test_issues(&mut issues);
        assert_eq!(issues[0].qname, "a");
        assert_eq!(issues[1].qname, "z");
    }
}
