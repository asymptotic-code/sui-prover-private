use crate::build_model::build_model;
use anyhow::Context;
use clap::{Args, ValueEnum};
use move_compiler::editions::Edition;
use move_compiler::editions::Flavor;
use move_compiler::shared::known_attributes::{AttributeKind_, ModeAttribute};
use move_core_types::account_address::AccountAddress;
use move_model::model::GlobalEnv;
use move_model::ty::Type as MoveType;
use move_package::{BuildConfig as MoveBuildConfig, LintFlag};
use move_stackless_bytecode::function_target_pipeline::{
    FunctionHolderTarget, FunctionTargetPipeline, FunctionTargetsHolder,
};
use move_stackless_bytecode::number_operation::GlobalNumberOperationState;
use move_stackless_bytecode::options::ProverOptions;
use move_stackless_bytecode::package_targets::PackageTargets;
use move_stackless_bytecode::target_filter::TargetFilterOptions;
use move_stackless_bytecode::{function_stats, spec_hierarchy};
use std::{
    collections::BTreeMap,
    path::{Path, PathBuf},
};

impl From<BuildConfig> for MoveBuildConfig {
    fn from(config: BuildConfig) -> Self {
        let mut modes = vec![ModeAttribute::VERIFY_ONLY.into()];
        if config.test {
            modes.push(ModeAttribute::TEST.into());
        }

        Self {
            modes,
            dev_mode: true,
            test_mode: config.test,
            json_errors: false,
            generate_docs: false,
            silence_warnings: true,
            warnings_are_errors: false,
            default_flavor: Some(Flavor::Sui),
            lint_flag: LintFlag::default(),
            install_dir: config.install_dir,
            force_recompilation: config.force_recompilation,
            lock_file: config.lock_file,
            fetch_deps_only: config.fetch_deps_only,
            skip_fetch_latest_git_deps: config.skip_fetch_latest_git_deps,
            default_edition: config.default_edition,
            deps_as_root: config.deps_as_root,
            additional_named_addresses: config.additional_named_addresses,
            save_disassembly: false,
            implicit_dependencies: BTreeMap::new(),
            force_lock_file: false,
        }
    }
}

/// General prove options
#[derive(Args)]
#[clap(next_help_heading = "General Options")]
pub struct GeneralConfig {
    /// Don't delete temporary files after verification
    #[clap(name = "keep-temp", long, short = 'k', global = true)]
    pub keep_temp: bool,

    /// Only generate Lean code, without running the prover
    #[clap(name = "generate-only", long, short = 'g', global = true)]
    pub generate_only: bool,

    /// Display detailed verification progress
    #[clap(name = "verbose", long, short = 'v', global = true)]
    pub verbose: bool,

    /// Dump bytecode to file
    #[clap(name = "dump-bytecode", long, short = 'd', global = true)]
    pub dump_bytecode: bool,

    /// Dump control-flow graphs to file
    #[clap(name = "stats", long, global = false)]
    pub stats: bool,

    /// Whether to enable CI mode for continuous integration environments
    #[clap(name = "ci", long, global = false)]
    pub ci: bool,

    /// Lean generation mode: all (default), module, or function
    #[clap(name = "generation-mode", long, default_value = "all", global = true)]
    pub generation_mode: LeanGenerationMode,

    /// Include every function in every module in the IR build, not
    /// just functions reachable from verification targets. Useful for
    /// documentation / exploration; defaults off (faster, narrower output).
    #[clap(name = "include-all", long = "include-all", global = true)]
    pub include_all: bool,

    /// Route IR generation through the new `lean-pipeline` crate
    /// instead of `move-prover-lean-backend`. Experimental (strangler-fig
    /// migration); unsupported constructs surface as `RenderError`s.
    /// See `plans/lean-pipeline-rebuild.md`.
    #[clap(name = "new-pipeline", long = "new-pipeline", global = true)]
    pub new_pipeline: bool,

    /// With `--new-pipeline`: abort on the first per-function failure
    /// instead of leaving it as a `sorry` stub. For CI gates.
    #[clap(
        name = "new-pipeline-strict",
        long = "new-pipeline-strict",
        global = true
    )]
    pub new_pipeline_strict: bool,

    /// With `--new-pipeline` (spec mode, `--generation-mode all`): after
    /// generation, build the audited modules and check every
    /// `obligations.toml` entry's transitive axiom footprint
    /// (`Lean.collectAxioms`) against the expected trusted set. Writes
    /// `proof_status.toml` next to the manifest; fails the run on
    /// sorries (incl. transitive ones through helper lemmas), missing
    /// declarations, or axioms outside the trusted base. Vendored
    /// lean-auto/Z3 closes are reported separately as `smt_trusted`,
    /// never as kernel-proven.
    #[clap(name = "audit-proofs", long = "audit-proofs", global = true)]
    pub audit_proofs: bool,

    /// With `--audit-proofs --new-pipeline`: audit an already generated
    /// `--generation-mode all` project at `--output-dir` without rebuilding
    /// the Move model or rendering Lean again. The audit itself is not
    /// cached: it still runs the mandatory incremental `lake build --rehash`
    /// and recomputes statement matching, axiom footprints, declaration
    /// provenance, sorry detection, and the proof-overlay snapshot.
    #[clap(name = "audit-existing", long = "audit-existing", global = true)]
    pub audit_existing: bool,

    /// With `--audit-proofs`: fail the run when any obligation
    /// classifies as `conditional` -- the proof declaration concludes
    /// the obligation prop but carries extra hypotheses beyond the
    /// prop's own telescope. Off by default (conditional obligations
    /// are counted and listed in `proof_status.toml` but non-fatal);
    /// `statement_mismatch` is always fatal regardless of this flag.
    #[clap(
        name = "audit-strict-statements",
        long = "audit-strict-statements",
        global = true
    )]
    pub audit_strict_statements: bool,

    /// With `--audit-proofs`: reconstruct an isolated OLean set from cold
    /// instead of auditing the OLeans this project's own build already
    /// produced. OFF by default -- the default (cached) audits the
    /// existing build. TRUST DELTA -- the default trusts Lake's
    /// incremental correctness, which this flag refuses to trust: the
    /// default answers "do my proofs discharge the obligations, assuming
    /// the build is current", and does NOT answer "is this corpus
    /// verified" off a warm cache. This flag makes the answer
    /// unconditional. Runs are stamped `proof audit [clean-room]:` and
    /// `audit_mode = "clean-room"`.
    ///
    /// POLICY: cached is the default -- fast, and sound whenever the
    /// build cannot be stale (e.g. a fresh CI runner, which never has a
    /// prior build to trust). Reach for this to quote a result as
    /// verification off a warm local cache.
    ///
    /// What does NOT change: every check runs in full. Statement
    /// matching, axiom collection, sorry detection, declaration
    /// provenance and the overlay snapshot comparison are all recomputed
    /// from the built environment. A fast path may reuse a BUILD; it may
    /// never reuse a VERDICT.
    ///
    /// The cached default brings the audited modules up to date with an
    /// incremental `lake build --rehash` before anything is inspected.
    /// That step is not optional: without it, editing a proof and
    /// forgetting to rebuild would read as green off a stale OLean.
    /// `--rehash` keeps that closure content-based rather than
    /// mtime-based, so a file restored with an old mtime still invalidates.
    #[clap(name = "audit-clean-room", long = "audit-clean-room", global = true)]
    pub audit_clean_room: bool,

    /// With `--new-pipeline`: dump the post-pipeline IR
    /// (`lean_pipeline::ir::Program`) in a human-readable pseudocode
    /// format. If the path is an existing directory or ends in `/`,
    /// one file per module is written there (named
    /// `<package>__<module>.ir.txt`) plus a `program.ir.txt` summary;
    /// otherwise the whole program is written to the single file.
    #[clap(name = "dump-ir", long = "dump-ir", global = true)]
    pub dump_ir: Option<PathBuf>,

    /// With `--new-pipeline`: dump the IR after every pipeline stage
    /// into per-stage subdirectories of the given path. Each
    /// subdirectory carries the same per-module + `program.ir.txt`
    /// layout as `--dump-ir`, so you can diff between stages with
    /// `diff -r <dir>/stage_05_ssa <dir>/stage_06_let_inline`.
    /// Stage names (in execution order):
    /// `stage_02_post_translation`, `stage_03_mut_to_let`,
    /// `stage_04_effects`, `stage_04_ghost`, `stage_05_ssa`,
    /// `stage_05_chain_complete`, `stage_04_writeback`,
    /// `stage_10_bounded_nat_pre_stage7`, `stage_07_dejumps`,
    /// `stage_06_let_inline`, `stage_08_loops`,
    /// `stage_10_bounded_nat_final`, `stage_12_obligations`.
    #[clap(name = "dump-ir-stages", long = "dump-ir-stages", global = true)]
    pub dump_ir_stages: Option<PathBuf>,

    /// With `--new-pipeline --dump-ir-stages`: filter the per-stage
    /// dump to a single function (and its derived companions:
    /// `.aborts`, `.ensures`, `.requires`, `.while_N`, `.after`,
    /// etc.) and emit one combined file with all stages back-to-back.
    /// The filter is a bare function name (`count_up`) or a
    /// module-qualified name (`math::count_up`); matches the exact
    /// name plus any companion whose name starts with `<filter>.`.
    /// Output goes to `<dump-ir-stages>/<sanitized-filter>.ir.txt`.
    /// Has no effect without `--dump-ir-stages`.
    #[clap(name = "dump-ir-function", long = "dump-ir-function", global = true)]
    pub dump_ir_function: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, ValueEnum)]
pub enum LeanGenerationMode {
    Function,
    Module,
    All,
}

fn validate_audit_options(
    audit_proofs: bool,
    audit_existing: bool,
    audit_strict_statements: bool,
    audit_clean_room: bool,
    new_pipeline: bool,
    test_mode: bool,
    stats: bool,
    generate_only: bool,
    generation_mode: &LeanGenerationMode,
) -> anyhow::Result<()> {
    anyhow::ensure!(
        !audit_existing || audit_proofs,
        "--audit-existing requires --audit-proofs"
    );
    anyhow::ensure!(
        !audit_strict_statements || audit_proofs,
        "--audit-strict-statements requires --audit-proofs"
    );
    anyhow::ensure!(
        !audit_clean_room || audit_proofs,
        "--audit-clean-room requires --audit-proofs"
    );
    if !audit_proofs {
        return Ok(());
    }
    anyhow::ensure!(
        new_pipeline,
        "--audit-proofs requires --new-pipeline (the manifest is a new-pipeline artifact)"
    );
    anyhow::ensure!(
        !test_mode,
        "--audit-proofs cannot be used with --test (test generation has no proof obligations)"
    );
    anyhow::ensure!(
        !stats,
        "--audit-proofs cannot be used with --stats (stats mode exits before generation)"
    );
    anyhow::ensure!(
        generation_mode == &LeanGenerationMode::All,
        "--audit-proofs requires --generation-mode all (one project, one manifest)"
    );
    anyhow::ensure!(
        !audit_existing || !generate_only,
        "--audit-existing cannot be used with --generate-only"
    );
    Ok(())
}

#[derive(Args, Default, Clone)]
#[clap(next_help_heading = "Build Options (subset of sui move build)")]
pub struct BuildConfig {
    /// Installation directory for compiled artifacts. Defaults to current directory.
    #[clap(long = "install-dir", global = true)]
    pub install_dir: Option<PathBuf>,

    /// Force recompilation of all packages
    #[clap(name = "force-recompilation", long = "force", global = true)]
    pub force_recompilation: bool,

    /// Optional location to save the lock file to, if package resolution succeeds.
    #[clap(skip)]
    pub lock_file: Option<PathBuf>,

    /// Only fetch dependency repos to MOVE_HOME
    #[clap(long = "fetch-deps-only", global = true)]
    pub fetch_deps_only: bool,

    /// Skip fetching latest git dependencies
    #[clap(long = "skip-fetch-latest-git-deps", global = true)]
    pub skip_fetch_latest_git_deps: bool,

    /// Default edition for move compilation, if not specified in the package's config
    #[clap(long = "default-move-edition", global = true)]
    pub default_edition: Option<Edition>,

    /// If set, dependency packages are treated as root packages. Notably, this will remove
    /// warning suppression in dependency packages.
    #[clap(long = "dependencies-are-root", global = true)]
    pub deps_as_root: bool,

    /// Additional named address mapping. Useful for tools in rust
    #[clap(skip)]
    pub additional_named_addresses: BTreeMap<String, AccountAddress>,

    /// Run every Move `#[test]` through Lean execution and emit a
    /// `move test`-style PASS/FAIL report. Each test renders into a
    /// self-contained driver, runs via `lake env lean --run`, and
    /// matches against `#[expected_failure]`.
    #[clap(name = "test", long, global = true)]
    pub test: bool,
}

/// `--test` pipeline options. Only meaningful with `--test`; ignored
/// otherwise.
#[derive(Args, Default, Clone)]
#[clap(next_help_heading = "Test Options (only with --test)")]
pub struct TestConfig {
    /// Regex over test qnames (`<module>::<test>`). Module-name-contains
    /// the literal short-circuits the whole module. Scopes both the
    /// runner AND the IR build (only matching tests + callees emit).
    /// Has no effect without `--test`.
    #[clap(name = "test-filter", long = "test-filter", global = true)]
    pub filter: Option<String>,

    /// Number of rayon worker threads the upstream move-unit-test
    /// runner uses to execute `#[test]`s in parallel within a package.
    /// Defaults to upstream's default (8). Has no effect without
    /// `--test`.
    #[clap(name = "test-threads", long = "test-threads", global = true)]
    pub num_threads: Option<usize>,

    /// Stop after `lake build` (which type-checks every Spec-emitted
    /// package); skip the per-test `lake env lean --run` invocations.
    /// CI gate that the test pipeline produces well-typed Lean. Has
    /// no effect without `--test`.
    #[clap(name = "type-check-only", long = "type-check-only", global = true)]
    pub type_check_only: bool,

    /// Per-test wall-clock timeout in seconds for the
    /// `lake env lean --run` invocation. When a single test driver
    /// exceeds this, the subprocess is killed and the test is reported
    /// as an infrastructure failure rather than a Move abort; the runner
    /// continues with the rest of the package. `0` (the default) disables
    /// the timeout. Has no effect without `--test`.
    #[clap(
        name = "test-timeout",
        long = "test-timeout",
        global = true,
        default_value_t = 0u64
    )]
    pub per_test_timeout_secs: u64,

    /// Write a structured TOML result artifact while retaining the normal
    /// human-readable test output. Requires `--test`.
    #[clap(name = "test-results-toml", long = "test-results-toml", global = true)]
    pub results_toml: Option<PathBuf>,
}

pub async fn execute(
    path: Option<&Path>,
    general_config: GeneralConfig,
    build_config: BuildConfig,
    filter: TargetFilterOptions,
    mut test_config: TestConfig,
    output_dir: Option<&Path>,
) -> anyhow::Result<()> {
    validate_audit_options(
        general_config.audit_proofs,
        general_config.audit_existing,
        general_config.audit_strict_statements,
        general_config.audit_clean_room,
        general_config.new_pipeline,
        build_config.test,
        general_config.stats,
        general_config.generate_only,
        &general_config.generation_mode,
    )?;
    anyhow::ensure!(
        test_config.results_toml.is_none() || build_config.test,
        "--test-results-toml requires --test"
    );
    anyhow::ensure!(
        test_config.results_toml.is_none() || !general_config.generate_only,
        "--test-results-toml cannot be used with --generate-only"
    );
    if let Some(path) = test_config.results_toml.as_mut() {
        if path.is_relative() {
            *path = std::env::current_dir()?.join(&*path);
        }
        if path.exists() {
            std::fs::remove_file(&*path).with_context(|| {
                format!("removing stale test results artifact {}", path.display())
            })?;
        }
    }
    let overall_start = std::time::Instant::now();

    if general_config.audit_existing {
        let package_dir = match path {
            Some(path) => std::fs::canonicalize(path)
                .with_context(|| format!("resolving package directory {}", path.display()))?,
            None => std::env::current_dir()?,
        };
        let base_output_dir = resolve_base_output_dir(&package_dir, output_dir)?;
        crate::audit::verify_pinned_lean_toolchain(&base_output_dir)?;
        run_and_report_proof_audit(
            &base_output_dir,
            &package_dir,
            general_config.audit_clean_room,
            general_config.audit_strict_statements,
        )
        .await?;
        eprintln!("⏱ Total took: {}ms", overall_start.elapsed().as_millis());
        return Ok(());
    }

    let model = build_model(path, Some(build_config.clone()))?;
    if model.has_errors() {
        use codespan_reporting::diagnostic::Severity;
        use termcolor::Buffer;
        let mut buf = Buffer::no_color();
        model.report_diag(&mut buf, Severity::Error);
        return Err(anyhow::anyhow!(
            "Move Model compiled with errors.
{}",
            String::from_utf8_lossy(buf.as_slice())
        ));
    }
    let package_targets = PackageTargets::new(&model, filter, !general_config.ci, None);

    // Hybrid Boogie+Lean: bare names of specs marked
    // `#[spec(prove)] #[ext(backend = b"boogie")]`. Computed from the authoritative
    // `package_targets` here (not from the per-mode `FunctionTargetsHolder`,
    // whose `package_targets` is lossy after `merge_targets_from` in All mode).
    // The renderer emits these obligations as trusted axioms.
    let boogie_proven_names: std::collections::HashSet<String> = package_targets
        .boogie_backend_specs()
        .iter()
        .map(|qid| model.get_function(*qid).get_name_str())
        .collect();

    if general_config.stats {
        function_stats::display_function_stats(&model, &package_targets);
        return Ok(());
    }

    let prover_options = ProverOptions {
        skip_loop_analysis: true,
        ..ProverOptions::default()
    };

    // After build_model(), cwd is set to the package root
    let package_dir = std::env::current_dir()?;
    let base_output_dir = resolve_base_output_dir(&package_dir, output_dir)?;

    if general_config.new_pipeline {
        check_new_pipeline_layout(&package_dir)?;
    }

    if build_config.test {
        return run_test_pipeline(
            &model,
            &package_targets,
            &prover_options,
            &base_output_dir,
            &package_dir,
            &build_config,
            &test_config,
            &general_config,
            overall_start,
        )
        .await;
    }

    if general_config.dump_bytecode {
        init_global_number_state(&model, &prover_options);
        let (targets, _, _upstream_errors) = create_and_process_targets(
            &model,
            &package_targets,
            &prover_options,
            FunctionHolderTarget::All,
            false,
            general_config.include_all,
            general_config.new_pipeline,
            None,
        );
        std::fs::create_dir_all(&base_output_dir)?;
        spec_hierarchy::display_spec_hierarchy(&model, &targets, &base_output_dir);
    }

    let mut render_transaction = None;
    match general_config.generation_mode {
        LeanGenerationMode::Function => {
            for qid in package_targets.target_specs() {
                let func_name = model.get_function(*qid).get_full_name_str();
                println!("Generating Lean code for {}...", func_name);

                model.cleanup();
                init_global_number_state(&model, &prover_options);
                let (targets, _, upstream_errors) = create_and_process_targets(
                    &model,
                    &package_targets,
                    &prover_options,
                    FunctionHolderTarget::Function(*qid),
                    false,
                    general_config.include_all,
                    general_config.new_pipeline,
                    None,
                );

                let output_dir = base_output_dir.join(func_name.replace("::", "__"));
                let _ = run_lean_backend(
                    &model,
                    &targets,
                    &package_targets,
                    &output_dir,
                    &package_dir,
                    &general_config,
                    upstream_errors,
                    &boogie_proven_names,
                )
                .await?;
            }
        }
        LeanGenerationMode::Module => {
            for mid in package_targets.target_modules() {
                let module_name = model.get_module(mid).get_full_name_str();
                println!("Generating Lean code for module {}...", module_name);

                model.cleanup();
                init_global_number_state(&model, &prover_options);
                let (targets, _, upstream_errors) = create_and_process_targets(
                    &model,
                    &package_targets,
                    &prover_options,
                    FunctionHolderTarget::Module(mid),
                    false,
                    general_config.include_all,
                    general_config.new_pipeline,
                    None,
                );

                let output_dir = base_output_dir.join(module_name.replace("::", "__"));
                let _ = run_lean_backend(
                    &model,
                    &targets,
                    &package_targets,
                    &output_dir,
                    &package_dir,
                    &general_config,
                    upstream_errors,
                    &boogie_proven_names,
                )
                .await?;
            }
        }
        LeanGenerationMode::All => {
            init_global_number_state(&model, &prover_options);
            // `target_modules()` covers PROVE-spec modules only. A module
            // whose specs are ALL trusted (`#[spec(prove, skip)]`,
            // non-prove, run_on="boogie") never appears there, so it
            // would miss the fan-out entirely: its wrappers are never
            // processed, no holder keeps them, and stage 12 silently
            // emits nothing for it (current-lending borrow/market_handle
            // etc. rendered as EMPTY modules). For the new pipeline,
            // union in the modules carrying no_verify (trusted) specs so
            // their axioms materialize; the legacy path has no axiom
            // emission and keeps the original roster.
            let spec_modules: Vec<_> = if general_config.new_pipeline {
                let mut mods = package_targets.target_modules();
                mods.extend(package_targets.spec_abort_check_verify_modules());
                mods.into_iter().collect()
            } else {
                package_targets.target_modules().into_iter().collect()
            };
            let merged_targets;
            let any_upstream_errors;
            if spec_modules.is_empty() {
                // No specs in the package — keep the original single
                // FunctionHolderTarget::All path. No BiMap collision is
                // possible without specs.
                let (targets, _, upstream_errors) = create_and_process_targets(
                    &model,
                    &package_targets,
                    &prover_options,
                    FunctionHolderTarget::All,
                    false,
                    general_config.include_all,
                    general_config.new_pipeline,
                    None,
                );
                merged_targets = targets;
                any_upstream_errors = upstream_errors;
            } else {
                // Fan out per spec module — keeps upstream's
                // spec<->target BiMap 1:1 per batch (avoids the
                // "Duplicate target function" diag when multiple
                // modules spec the same function). Merged downstream
                // reads `targets` only, so the post-merge BiMap being
                // incomplete is harmless.
                let mut merged: Option<FunctionTargetsHolder> = None;
                let mut upstream_errors_accum = false;
                for mid in spec_modules {
                    let (targets, _, upstream_errors) = create_and_process_targets(
                        &model,
                        &package_targets,
                        &prover_options,
                        FunctionHolderTarget::Module(mid),
                        false,
                        general_config.include_all,
                        general_config.new_pipeline,
                        None,
                    );
                    upstream_errors_accum |= upstream_errors;
                    match merged.as_mut() {
                        None => merged = Some(targets),
                        Some(acc) => acc.merge_targets_from(targets),
                    }
                }
                merged_targets =
                    merged.expect("non-empty spec_modules produced at least one holder");
                any_upstream_errors = upstream_errors_accum;
            }

            render_transaction = run_lean_backend(
                &model,
                &merged_targets,
                &package_targets,
                &base_output_dir,
                &package_dir,
                &general_config,
                any_upstream_errors,
                &boogie_proven_names,
            )
            .await?;
        }
    }

    if general_config.audit_proofs {
        let render = render_transaction
            .as_ref()
            .expect("audited new-pipeline all-mode generation retains its render transaction");
        crate::audit::verify_pinned_lemma_bundle(&render.lemmas_dir)?;
        let toolchain = crate::audit::verify_pinned_lean_toolchain(&base_output_dir)?;
        eprintln!(
            "proof audit: pinned Lean model bundle {}, pinned Lean toolchain {}",
            render.lemmas_dir.display(),
            toolchain
        );
        // The mode goes INSIDE the summary line, not merely alongside it.
        // This line is quoted verbatim into commit messages and reports;
        // months later, in that quote, it is the only surviving evidence of
        // whether the artifacts behind these counts were compiled from these
        // bytes during the run (`[clean-room]`) or reused from a
        // content-keyed cache (`[cached]`).
        run_and_report_proof_audit(
            &base_output_dir,
            &package_dir,
            general_config.audit_clean_room,
            general_config.audit_strict_statements,
        )
        .await?;
    }

    eprintln!("⏱ Total took: {}ms", overall_start.elapsed().as_millis());
    Ok(())
}

async fn run_and_report_proof_audit(
    base_output_dir: &Path,
    package_dir: &Path,
    clean_room: bool,
    strict_statements: bool,
) -> anyhow::Result<()> {
    let mode = if clean_room {
        crate::audit::AuditMode::CleanRoom
    } else {
        crate::audit::AuditMode::Cached
    };
    let summary = crate::audit::run_proof_audit(base_output_dir, package_dir, mode).await?;
    eprintln!(
        "proof audit [{}]: {} proven, {} conditional, {} declared, {} trusted, {} smt_trusted, {} sorry, {} suspicious, {} missing, {} statement_mismatch, {} statement_unverified, {} spec_no_obligation -> {}",
        mode.label(), summary.proven, summary.conditional, summary.declared, summary.trusted,
        summary.smt_trusted, summary.sorry, summary.suspicious, summary.missing,
        summary.statement_mismatch, summary.statement_unverified, summary.spec_no_obligation,
        base_output_dir.join("proof_status.toml").display()
    );
    if summary.suspicious > 0
        || summary.missing > 0
        || summary.statement_mismatch > 0
        || summary.statement_unverified > 0
    {
        anyhow::bail!(
            "proof audit INTEGRITY FAILURE: {} suspicious, {} missing, {} statement_mismatch, {} statement_unverified (see proof_status.toml)",
            summary.suspicious, summary.missing, summary.statement_mismatch,
            summary.statement_unverified
        );
    }
    if summary.sorry > 0 {
        anyhow::bail!(
            "proof audit: {} obligation(s) unproven (sorry in footprint; see proof_status.toml)",
            summary.sorry
        );
    }
    if summary.conditional > 0 {
        eprintln!(
            "proof audit: {} obligation(s) proven CONDITIONALLY -- extra hypotheses beyond the obligation prop (see proof_status.toml)",
            summary.conditional
        );
        if strict_statements {
            anyhow::bail!(
                "proof audit: --audit-strict-statements: {} conditional obligation(s)",
                summary.conditional
            );
        }
    }
    Ok(())
}

/// Read the user's Move package name from its explicit package directory.
/// The explicit path keeps `--path` invocations
/// independent of the caller's working directory. The renderer emits the
/// user package into an output subdirectory named exactly this (no
/// sanitization -- see `render_program_to_dir`), so callers can allowlist it
/// as a lake target.
fn read_user_package_name(package_dir: &Path) -> anyhow::Result<String> {
    let path = package_dir.join("Move.toml");
    let manifest = std::fs::read_to_string(&path)
        .with_context(|| format!("reading package manifest {}", path.display()))?;
    let manifest: toml::Value =
        toml::from_str(&manifest).with_context(|| format!("parsing {}", path.display()))?;
    let name = manifest
        .get("package")
        .and_then(|package| package.get("name"))
        .and_then(toml::Value::as_str)
        .with_context(|| format!("{} has no string package.name", path.display()))?;
    anyhow::ensure!(
        !name.is_empty() && name.trim() == name,
        "{} has an invalid package.name",
        path.display()
    );
    Ok(name.to_string())
}

pub const OLEAN_SEED_ENV: &str = "SUI_LEAN_OLEAN_SEED";

/// Build the prebuilt-OLean seed for the self-contained part of the Lean model
/// bundle: render an empty program into `seed_dir` (the exact layout and
/// lakefile every output gets) and `lake build` just those modules. Point
/// `SUI_LEAN_OLEAN_SEED` at the result to reuse it from every render.
pub fn build_olean_seed(seed_dir: &Path) -> anyhow::Result<()> {
    let configured_lemmas = std::env::var_os("SUI_LEAN_LEMMAS_DIR").map(PathBuf::from);
    let executable = std::env::current_exe().ok();
    let lemmas_src =
        resolve_lean_pipeline_lemmas_dir(configured_lemmas.as_deref(), executable.as_deref())?;
    let modules = lean_pipeline::render::olean_seed::self_contained_bundle_modules(&lemmas_src)
        .map_err(|err| anyhow::anyhow!("scan Lean model bundle: {:?}", err))?;
    anyhow::ensure!(
        !modules.is_empty(),
        "the Lean model bundle at {} has no self-contained modules",
        lemmas_src.display()
    );
    lean_pipeline::render::render_program_to_dir(
        &lean_pipeline::ir::Program::default(),
        seed_dir,
        Some(&lemmas_src),
        None,
        None,
        lean_pipeline::render::loop_termination::LoopMode::Proof,
        None,
        None,
    )
    .map_err(|err| anyhow::anyhow!("render OLean seed project: {:?}", err))?;
    eprintln!(
        "olean seed: building {} self-contained module(s) of {} in {}",
        modules.len(),
        lemmas_src.display(),
        seed_dir.display()
    );
    let status = std::process::Command::new("lake")
        .arg("build")
        .args(modules.iter().map(|module| format!("+{module}")))
        .current_dir(seed_dir)
        .status()
        .map_err(|err| anyhow::anyhow!("run lake in {}: {err}", seed_dir.display()))?;
    anyhow::ensure!(
        status.success(),
        "lake build of the OLean seed failed: {status}"
    );
    let lib = seed_dir.join(".lake/build/lib/lean");
    let missing: Vec<&String> = modules
        .iter()
        .filter(|module| {
            !lib.join(format!("{}.olean", module.replace('.', "/")))
                .is_file()
        })
        .collect();
    anyhow::ensure!(
        missing.is_empty(),
        "lake reported success but these seed modules have no OLean: {missing:?}"
    );
    Ok(())
}

fn resolve_lean_pipeline_lemmas_dir(
    configured: Option<&Path>,
    executable: Option<&Path>,
) -> anyhow::Result<PathBuf> {
    let mut candidates = Vec::new();
    if let Some(configured) = configured {
        candidates.push(configured.to_path_buf());
    } else {
        if let Some(bin_dir) = executable.and_then(Path::parent) {
            candidates.push(bin_dir.join("../share/sui-lean/lemmas"));
            candidates.push(bin_dir.join("sui-lean-data/lemmas"));
            candidates.push(bin_dir.join("lemmas"));
        }
        let manifest_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        if let Some(crates_dir) = manifest_dir.parent() {
            candidates.push(crates_dir.join("lean-pipeline/lemmas"));
        }
    }

    for candidate in &candidates {
        let Ok(candidate) = candidate.canonicalize() else {
            continue;
        };
        if candidate.join("Prelude/BoundedNat.lean").is_file()
            && candidate.join("natives/Prover/MoveAuto.lean").is_file()
        {
            return Ok(candidate);
        }
    }

    let searched = candidates
        .iter()
        .map(|path| path.display().to_string())
        .collect::<Vec<_>>()
        .join(", ");
    anyhow::bail!(
        "cannot locate the Lean pipeline lemmas bundle; set SUI_LEAN_LEMMAS_DIR \
         to its `lemmas` directory (searched: {searched})"
    )
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ExpectedObligationKind {
    Theorem,
    /// A `#[spec(prove)]` wrapper with no `target=` -- a standalone
    /// lemma. Still a `theorem` obligation in the manifest (there is a
    /// real proof to write); it is a separate variant only because it
    /// authorizes against `Program::targetless_prove_specs` instead of
    /// `spec_to_impl`, and its `target` is the wrapper itself.
    TargetlessTheorem,
    TrustedAxiom(lean_pipeline::ir::TrustReason),
}

impl ExpectedObligationKind {
    fn as_str(self) -> &'static str {
        match self {
            Self::Theorem | Self::TargetlessTheorem => "theorem",
            Self::TrustedAxiom(_) => "trusted_axiom",
        }
    }

    fn reason(self) -> Option<&'static str> {
        match self {
            Self::Theorem | Self::TargetlessTheorem => None,
            Self::TrustedAxiom(lean_pipeline::ir::TrustReason::NonProve) => Some("non_prove"),
            Self::TrustedAxiom(lean_pipeline::ir::TrustReason::Skip) => Some("skip"),
            Self::TrustedAxiom(lean_pipeline::ir::TrustReason::Boogie) => Some("run_on_boogie"),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct ExpectedObligationCandidate {
    source: String,
    target: String,
    kind: ExpectedObligationKind,
    required: bool,
}

#[derive(Debug)]
struct ResolvedExpectedObligation {
    candidate: ExpectedObligationCandidate,
    source_fid: lean_pipeline::ir::FunId,
    target_fid: lean_pipeline::ir::FunId,
}

fn insert_expected_obligation_candidate(
    candidates: &mut std::collections::BTreeMap<String, ExpectedObligationCandidate>,
    candidate: ExpectedObligationCandidate,
) -> anyhow::Result<()> {
    use std::collections::btree_map::Entry;

    match candidates.entry(candidate.source.clone()) {
        Entry::Vacant(entry) => {
            entry.insert(candidate);
        }
        Entry::Occupied(mut entry) => {
            let existing = entry.get_mut();
            anyhow::ensure!(
                existing.target == candidate.target && existing.kind == candidate.kind,
                "authoritative spec `{}` has conflicting classifications: {:?} and {:?}",
                candidate.source,
                existing,
                candidate
            );
            existing.required |= candidate.required;
        }
    }
    Ok(())
}

fn resolve_expected_obligation_candidates(
    program: &lean_pipeline::ir::Program,
    candidates: std::collections::BTreeMap<String, ExpectedObligationCandidate>,
) -> anyhow::Result<Vec<ResolvedExpectedObligation>> {
    let mut resolved = Vec::new();
    let mut authorized_prove = std::collections::BTreeMap::new();
    let mut authorized_targetless = std::collections::BTreeSet::new();
    let mut authorized_trusted = std::collections::BTreeMap::new();

    for candidate in candidates.into_values() {
        // Target-package specs are mandatory. Dependency specs become active
        // only when their wrapper survived translation; requiring every
        // dependency candidate would roster thousands of unreachable specs.
        let source_fid = resolve_program_member_optional(program, &candidate.source, false)?;
        let Some(source_fid) = source_fid else {
            anyhow::ensure!(
                !candidate.required,
                "authoritative target-package spec `{}` is absent from the IR",
                candidate.source
            );
            continue;
        };
        let target_fid = resolve_program_member(program, &candidate.target, true)?;
        match candidate.kind {
            ExpectedObligationKind::Theorem => {
                anyhow::ensure!(
                    program.spec_to_impl.get(&source_fid) == Some(&target_fid),
                    "authoritative prove pair `{}` -> `{}` is absent or miswired in the IR",
                    candidate.source,
                    candidate.target
                );
                authorized_prove.insert(source_fid, target_fid);
            }
            ExpectedObligationKind::TargetlessTheorem => {
                anyhow::ensure!(
                    program.targetless_prove_specs.contains(&source_fid),
                    "authoritative targetless prove spec `{}` is absent from the IR",
                    candidate.source
                );
                anyhow::ensure!(
                    source_fid == target_fid,
                    "targetless prove spec `{}` must be its own obligation target",
                    candidate.source
                );
                authorized_targetless.insert(source_fid);
            }
            ExpectedObligationKind::TrustedAxiom(reason) => {
                anyhow::ensure!(
                    program.trusted_spec_to_impl.get(&source_fid) == Some(&(target_fid, reason)),
                    "authoritative trusted pair `{}` -> `{}` ({:?}) is absent or miswired in the IR",
                    candidate.source,
                    candidate.target,
                    candidate.kind.reason()
                );
                authorized_trusted.insert(source_fid, (target_fid, reason));
            }
        }
        resolved.push(ResolvedExpectedObligation {
            candidate,
            source_fid,
            target_fid,
        });
    }

    for (source, target) in &program.spec_to_impl {
        anyhow::ensure!(
            authorized_prove.get(source) == Some(target),
            "IR prove pair from fid {} to fid {} has no active authoritative PackageTargets source",
            source,
            target
        );
    }
    for source in &program.targetless_prove_specs {
        anyhow::ensure!(
            authorized_targetless.contains(source),
            "IR targetless prove spec fid {} has no active authoritative PackageTargets source",
            source
        );
    }
    for (source, target) in &program.trusted_spec_to_impl {
        anyhow::ensure!(
            authorized_trusted.get(source) == Some(target),
            "IR trusted pair from fid {} to fid {} ({:?}) has no active authoritative PackageTargets source",
            source,
            target.0,
            target.1
        );
    }

    Ok(resolved)
}

fn render_expected_obligations(
    env: &GlobalEnv,
    package_targets: &PackageTargets,
    program: &lean_pipeline::ir::Program,
) -> anyhow::Result<Vec<u8>> {
    use stackless_to_intermediate::package_utils::extract_package_name;

    let source_name = |qid: move_model::model::QualifiedId<move_model::model::FunId>| {
        let function = env.get_function(qid);
        let module = &function.module_env;
        let package = extract_package_name(env, module);
        let module_name = env.symbol_pool().string(module.get_name().name());
        format!("{}::{}::{}", package, module_name, function.get_name_str())
    };
    let boogie = package_targets.boogie_backend_specs();
    let mut candidates = std::collections::BTreeMap::new();

    for qid in package_targets.target_specs() {
        let function = env.get_function(*qid);
        let Some(target_qid) = package_targets.find_target_spec(qid) else {
            // No `target=` -- a standalone lemma. Boogie-backed specs are
            // trusted and have no Lean obligation to roster; every other
            // one is a declared prove target whose obligation stage 12
            // builds from the wrapper's own companions, with the wrapper
            // itself in the target slot. Skipping these here is what let
            // six sui-system lemmas stay off the authoritative roster.
            if !boogie.contains(qid) {
                insert_expected_obligation_candidate(
                    &mut candidates,
                    ExpectedObligationCandidate {
                        source: source_name(*qid),
                        target: source_name(*qid),
                        kind: ExpectedObligationKind::TargetlessTheorem,
                        required: function.module_env.is_target(),
                    },
                )?;
            }
            continue;
        };
        let kind = if boogie.contains(qid) {
            ExpectedObligationKind::TrustedAxiom(lean_pipeline::ir::TrustReason::Boogie)
        } else {
            ExpectedObligationKind::Theorem
        };
        insert_expected_obligation_candidate(
            &mut candidates,
            ExpectedObligationCandidate {
                source: source_name(*qid),
                target: source_name(target_qid),
                kind,
                required: function.module_env.is_target(),
            },
        )?;
    }
    for qid in package_targets.no_verify_specs() {
        let function = env.get_function(*qid);
        let Some(target_qid) = package_targets.find_target_spec(qid) else {
            continue;
        };
        let reason = if boogie.contains(qid) {
            lean_pipeline::ir::TrustReason::Boogie
        } else if package_targets.skipped_specs().contains_key(qid) {
            lean_pipeline::ir::TrustReason::Skip
        } else {
            lean_pipeline::ir::TrustReason::NonProve
        };
        insert_expected_obligation_candidate(
            &mut candidates,
            ExpectedObligationCandidate {
                source: source_name(*qid),
                target: source_name(target_qid),
                kind: ExpectedObligationKind::TrustedAxiom(reason),
                required: function.module_env.is_target(),
            },
        )?;
    }

    let resolved = resolve_expected_obligation_candidates(program, candidates)?;

    let mut collision_counts = std::collections::BTreeMap::new();
    for row in &resolved {
        let wrapper_module = program.functions[&row.source_fid].module;
        let target_name = program
            .lookup_callee(row.target_fid)
            .expect("resolved authoritative target")
            .name()
            .to_string();
        *collision_counts
            .entry((wrapper_module, target_name))
            .or_insert(0usize) += 1;
    }

    let mut out = String::from(
        "# Generated from authoritative PackageTargets and pre-obligation IR mappings.\nversion = 1\n",
    );
    for row in resolved {
        let obligations = planned_obligation_names(
            program,
            row.source_fid,
            row.target_fid,
            row.candidate.kind,
            &collision_counts,
        );
        out.push_str("\n[[expected]]\n");
        out.push_str(&format!(
            "source = \"{}\"\n",
            toml_string(&row.candidate.source)
        ));
        out.push_str(&format!(
            "target = \"{}\"\n",
            toml_string(&row.candidate.target)
        ));
        out.push_str(&format!("kind = \"{}\"\n", row.candidate.kind.as_str()));
        if let Some(reason) = row.candidate.kind.reason() {
            out.push_str(&format!("reason = \"{}\"\n", reason));
        }
        out.push_str("obligations = [");
        for (index, obligation) in obligations.iter().enumerate() {
            if index > 0 {
                out.push_str(", ");
            }
            out.push_str(&format!("\"{}\"", toml_string(obligation)));
        }
        out.push_str("]\n");
    }
    Ok(out.into_bytes())
}

fn resolve_program_member(
    program: &lean_pipeline::ir::Program,
    qualified_name: &str,
    include_natives: bool,
) -> anyhow::Result<lean_pipeline::ir::FunId> {
    let resolved = resolve_program_member_optional(program, qualified_name, include_natives)?;
    resolved.with_context(|| {
        format!("authoritative obligation member `{qualified_name}` is absent from the IR")
    })
}

fn resolve_program_member_optional(
    program: &lean_pipeline::ir::Program,
    qualified_name: &str,
    include_natives: bool,
) -> anyhow::Result<Option<lean_pipeline::ir::FunId>> {
    let qname = |module: lean_pipeline::ir::ModId, name: &str| {
        let module = &program.modules[&module];
        format!("{}::{}::{}", module.package_name, module.name, name)
    };
    let mut matches: Vec<_> = program
        .functions
        .iter()
        .filter_map(|(fid, function)| {
            (qname(function.module, &function.name) == qualified_name).then_some(*fid)
        })
        .collect();
    if include_natives {
        matches.extend(program.natives.decls.iter().filter_map(|(fid, decl)| {
            (qname(decl.module, &decl.name) == qualified_name).then_some(*fid)
        }));
    }
    anyhow::ensure!(
        matches.len() <= 1,
        "authoritative obligation member `{qualified_name}` resolved to {} IR functions/natives",
        matches.len()
    );
    Ok(matches.pop())
}

fn planned_obligation_names(
    program: &lean_pipeline::ir::Program,
    source_fid: lean_pipeline::ir::FunId,
    target_fid: lean_pipeline::ir::FunId,
    kind: ExpectedObligationKind,
    collision_counts: &std::collections::BTreeMap<(lean_pipeline::ir::ModId, String), usize>,
) -> Vec<String> {
    let wrapper = &program.functions[&source_fid];
    // A targetless lemma emits exactly one obligation: `<lemma>_correct`.
    // No `_asserts_correct` -- that states the IMPL aborts exactly where
    // the spec's asserts fail, and a lemma has no impl. Mirrors
    // `stage_12_obligations`, which shares the base-name rule.
    if kind == ExpectedObligationKind::TargetlessTheorem {
        let base = lean_pipeline::ir::names::targetless_obligation_base(&wrapper.name);
        let ensures_name = lean_pipeline::ir::names::ensures_name(&wrapper.name);
        let has_ensures = program
            .functions
            .values()
            .any(|function| function.module == wrapper.module && function.name == ensures_name);
        return if has_ensures {
            vec![lean_pipeline::ir::names::correct_theorem_name(base)]
        } else {
            Vec::new()
        };
    }
    let target = program
        .lookup_callee(target_fid)
        .expect("resolved authoritative target");
    let target_name = target.name().to_string();
    let target_module = target.module();
    let collides = collision_counts
        .get(&(wrapper.module, target_name.clone()))
        .copied()
        .unwrap_or(0)
        > 1;
    let stripped = wrapper.name.strip_suffix("_spec").unwrap_or(&wrapper.name);
    let base = if collides && stripped != target_name {
        stripped
    } else {
        &target_name
    };
    let find_function = |module, name: &str| {
        program
            .functions
            .iter()
            .find(|(_, function)| function.module == module && function.name == name)
            .map(|(fid, _)| *fid)
    };
    let aborts_name = lean_pipeline::ir::names::aborts_name(&target_name);
    let has_aborts = find_function(target_module, &aborts_name).is_some()
        || program.natives.decls.iter().any(|(_, decl)| {
            decl.module == target_module
                && decl.name == aborts_name
                && decl.spec_target == Some(target_fid)
        });
    let ignore_abort = program
        .spec_ignore_aborts
        .get(&source_fid)
        .copied()
        .unwrap_or(false);
    let ensures_name = lean_pipeline::ir::names::ensures_name(&wrapper.name);

    let mut obligations = Vec::new();
    if has_aborts && !ignore_abort {
        obligations.push(lean_pipeline::ir::names::asserts_correct_theorem_name(base));
    }
    if find_function(wrapper.module, &ensures_name).is_some() {
        obligations.push(lean_pipeline::ir::names::correct_theorem_name(base));
    }
    obligations.sort();
    obligations
}

fn toml_string(value: &str) -> String {
    value.replace('\\', "\\\\").replace('"', "\\\"")
}

fn proof_overlay_dir(package_dir: &Path) -> PathBuf {
    package_dir.join("lean")
}

fn use_durable_proof_overlay(test_mode: bool, generation_mode: &LeanGenerationMode) -> bool {
    !test_mode && generation_mode == &LeanGenerationMode::All
}

fn use_complete_obligation_roster(test_mode: bool, generation_mode: &LeanGenerationMode) -> bool {
    !test_mode && generation_mode == &LeanGenerationMode::All
}

/// `--test` pipeline. Emits one combined output tree, runs
/// `lake build` to warm the cache, then hands the project off to
/// upstream `move-unit-test` with `LeanExecutor`. `--generation-mode`
/// is ignored (sibling-dir trees would break driver imports).
async fn run_test_pipeline(
    model: &GlobalEnv,
    package_targets: &PackageTargets,
    prover_options: &ProverOptions,
    base_output_dir: &Path,
    package_dir: &Path,
    build_config: &BuildConfig,
    test_config: &TestConfig,
    general_config: &GeneralConfig,
    overall_start: std::time::Instant,
) -> anyhow::Result<()> {
    init_global_number_state(model, prover_options);
    // Compile up-front so a malformed regex fails fast. The wrapper
    // scopes the IR closure; the runner reuses `test_config.filter`
    // (same string) at execution time.
    let test_filter = test_config
        .filter
        .as_deref()
        .map(crate::lean_pipeline_overrides::TestFilter::from_str)
        .transpose()
        .context("compiling --test-filter regex")?;
    let (targets, _, upstream_errors) = create_and_process_targets(
        model,
        package_targets,
        prover_options,
        FunctionHolderTarget::All,
        true,
        general_config.include_all,
        general_config.new_pipeline,
        test_filter,
    );

    // Test-mode emit: option-shape `.aborts` companions plus full
    // `#[test]` bodies. Use `generate_only=true` to skip the blanket
    // `lake build` — the model includes every dep package's
    // `*_tests` modules, which the renderer doesn't yet handle, and
    // a full build would fail on dep files no user test imports.
    // `--new-pipeline` doesn't yet support the `aborts_as_option`
    // shape; failures surface as RenderError / invariant diagnostics.
    let _render_transaction: Option<lean_pipeline::render::RenderOutputLock>;
    if general_config.new_pipeline {
        // Same `upstream_errors` mitigation as the spec path.
        if upstream_errors {
            anyhow::bail!(
                "new-pipeline (--test): refusing to run after upstream emitted error-severity \
                 diagnostics. The resulting bytecode is likely malformed and stage 1's \
                 structurer can recurse unboundedly on it. Drop --new-pipeline to fall back \
                 to the legacy backend, or fix the upstream errors reported above first."
            );
        }
        _render_transaction = Some(
            run_new_pipeline_backend(
                model,
                &targets,
                package_targets,
                base_output_dir,
                package_dir,
                general_config.new_pipeline_strict,
                general_config.dump_ir.as_deref(),
                general_config.dump_ir_stages.as_deref(),
                general_config.dump_ir_function.as_deref(),
                &general_config.generation_mode,
                /*test_mode=*/ true,
            )
            .await?
            .transaction,
        );
    } else {
        move_prover_lean_backend::run_backend_with_options(
            model,
            &targets,
            base_output_dir,
            package_dir,
            true,
            true, // aborts_as_option
            derive_ghost_native_seed(model, package_targets),
        )
        .await?;
        _render_transaction = None;
    }

    if general_config.generate_only {
        eprintln!("⏱ Total took: {}ms", overall_start.elapsed().as_millis());
        return Ok(());
    }

    // Build only what the test drivers need so `lake env lean` can resolve
    // their imports (`lake env` doesn't trigger builds of unbuilt deps):
    //   * `Prelude` and `Generated` — imported directly by the driver
    //     (`Prelude.MoveAbort` / `Prelude.BoundedNat`, `Generated.World`);
    //   * the user's own package — its `.aborts` companions are what the
    //     drivers call, and `lake build <user_pkg>` pulls in every framework
    //     module it imports transitively.
    // We deliberately do NOT build the copied framework/dependency libs
    // (MoveStdlib / Sui / Prover / DeepBook / SuiSystem / ...) as standalone
    // targets: they ship hand-written lemma files (`Sui/BalanceLemmas`,
    // `Sui/CoinLemmas`, `MoveStdlib/MoveOptionLemmas`) that reference
    // `.aborts` companions per-package pruning drops, so `lake build Sui`
    // fails on files no driver imports. Transitive builds only touch the
    // modules the user package actually uses, never those leaf lemma files.
    let mut targets_to_build: Vec<String> = vec!["Prelude".to_string()];
    if base_output_dir.join("Generated").is_dir() {
        targets_to_build.push("Generated".to_string());
    }
    let mut package_build_failures = Vec::new();
    let user_package = read_user_package_name(package_dir)?;
    if base_output_dir.join(&user_package).is_dir() {
        targets_to_build.push(user_package.clone());
    } else {
        package_build_failures.push(format!(
            "rendered user package target `{user_package}` is missing from {}",
            base_output_dir.display()
        ));
    }
    let output_str = base_output_dir
        .to_str()
        .ok_or_else(|| anyhow::anyhow!("Invalid output path"))?;
    // Continue on failure: a broken Spec-rendered module (even inside the
    // user package) shouldn't block tests that don't import it; drivers that
    // do import it fail at the type-check / run step below with a Lean error
    // (rc=1), which is the real gate.
    for target in &targets_to_build {
        if let Err(err) =
            move_prover_lean_backend::run_lake_build_targets(output_str, &[target.clone()]).await
        {
            // Surface the FULL lake output (`run_lake_build_targets` embeds the
            // captured stdout/stderr in the error). Logging only the first line
            // ("lake build failed with exit code 1") threw away the actual Lean
            // errors, making `tests-lake` failures undiagnosable.
            eprintln!("⚠ skipping `lake build {target}` for --test:\n{err}");
            package_build_failures.push(format!("`lake build {target}` failed: {err:#}"));
        }
    }

    // `run_lean_tests` dispatches on `test_config.type_check_only`:
    //  * type-check mode type-checks every per-test driver (a single
    //    aggregate `lake env lean`, no `--run`), so an under-applied /
    //    mistyped `.aborts` call -- e.g. a driver missing the ghost params a
    //    callee propagated -- fails here at `tests-lake` instead of only
    //    surfacing as a `code 2000` at run time;
    //  * run mode executes the drivers.
    let test_passed = crate::lean_test::run_lean_tests(
        model,
        &targets,
        base_output_dir,
        package_dir,
        build_config,
        test_config,
        general_config.new_pipeline,
        &package_build_failures,
    )?;
    if test_config.type_check_only {
        eprintln!(
            "⏱ Total took: {}ms (type-check-only — package + test-driver type-check)",
            overall_start.elapsed().as_millis()
        );
        if !test_passed {
            anyhow::bail!("one or more Lean test drivers failed to type-check");
        }
        return Ok(());
    }
    eprintln!("⏱ Total took: {}ms", overall_start.elapsed().as_millis());
    if !test_passed {
        anyhow::bail!("one or more Lean unit tests failed");
    }
    Ok(())
}

fn init_global_number_state(model: &GlobalEnv, prover_options: &ProverOptions) {
    let mut global_state = GlobalNumberOperationState::new_with_options(prover_options.clone());
    for module_env in model.get_modules() {
        for struct_env in module_env.get_structs() {
            global_state.create_initial_struct_oper_state(&struct_env);
        }
        for fun_env in module_env.get_functions() {
            global_state.create_initial_func_oper_state(&fun_env);
        }
    }
    model.set_extension(global_state);
}

/// World-mode's synthetic `end_transaction` lowering (`world_threading.rs::
/// zero_value_for_effects_field`) needs `vec_map::empty` to exist in
/// `program.functions` to build a zero-value `TransactionEffects.<field>:
/// vec_map::VecMap`, even when nothing in the package's own reachable code
/// calls it. Reachability-based pruning (`VerificationAnalysisProcessor::
/// finalize`) runs long before world-mode is known (it's discovered later,
/// from a `sources/lean/**` `def <Module>.module_options` hook, well after
/// this pipeline stage) -- so instead of trying to reorder that discovery,
/// detect the hook directly here (world-mode is a per-package opt-in, so a
/// package either always wants this or never does) and force-keep
/// `vec_map::empty` through the same `keep_trusted_specs` mechanism used for
/// trusted spec wrappers.
fn world_mode_keep_functions(
    model: &GlobalEnv,
) -> std::collections::BTreeSet<move_model::model::QualifiedId<move_model::model::FunId>> {
    // `build_model()` leaves cwd set to the package root for the rest of
    // the run (see `reroot_path`), so this resolves the same
    // `sources/lean/` tree `run_backend` later scans for the same hook.
    let package_dir = std::env::current_dir()
        .expect("world_mode_keep_functions: cwd must be the package root after build_model");
    let decls = move_prover_lean_backend::scan_lean_termination_decls(
        &package_dir.join("sources").join("lean"),
    );
    let world_mode = decls
        .module_options
        .values()
        .any(|opts| opts.contains("world_mode"));
    if !world_mode {
        return std::collections::BTreeSet::new();
    }
    for module_env in model.get_modules() {
        let module_name = model
            .symbol_pool()
            .string(module_env.get_name().name())
            .to_string();
        if module_name != "vec_map" {
            continue;
        }
        for fun_env in module_env.get_functions() {
            if !fun_env.is_native()
                && model.symbol_pool().string(fun_env.get_name()).as_ref() == "empty"
            {
                return std::iter::once(fun_env.get_qualified_id()).collect();
            }
        }
    }
    std::collections::BTreeSet::new()
}

fn create_and_process_targets(
    model: &GlobalEnv,
    package_targets: &PackageTargets,
    prover_options: &ProverOptions,
    target: FunctionHolderTarget,
    test_mode: bool,
    include_all: bool,
    new_pipeline: bool,
    test_filter: Option<crate::lean_pipeline_overrides::TestFilter>,
) -> (FunctionTargetsHolder, Option<String>, bool) {
    // New pipeline only: trusted spec wrappers (non-prove / skip /
    // ext(backend = b"boogie")) the prune must keep so stage 12 can build their
    // `axiom` statements. Scoped to the holder target the same way
    // upstream's private `in_target` scopes verified specs, so per-
    // module fan-out doesn't drag every module's trusted wrappers (and
    // their whole callee closures) into every project.
    let mut trusted_keep: std::collections::BTreeSet<
        move_model::model::QualifiedId<move_model::model::FunId>,
    > = if new_pipeline {
        let boogie_proven = package_targets.boogie_backend_specs();
        package_targets
            .no_verify_specs()
            .iter()
            .chain(boogie_proven.iter())
            .filter(|qid| match &target {
                FunctionHolderTarget::All => true,
                FunctionHolderTarget::Module(mid) => qid.module_id == *mid,
                FunctionHolderTarget::Function(fqid) => **qid == *fqid,
                // Test / abort-check holders don't emit axioms.
                _ => false,
            })
            .copied()
            .collect()
    } else {
        std::collections::BTreeSet::new()
    };
    // World-mode's synthetic effects construction needs `vec_map::empty`
    // regardless of holder scope or reachability -- see
    // `world_mode_keep_functions` doc comment.
    trusted_keep.extend(world_mode_keep_functions(model));

    // A kept trusted wrapper is analyzed by passes that previously never
    // saw it (the prune dropped it first), and some legitimately reject
    // spec constructs the Lean flow doesn't support (e.g.
    // QuantifierIteratorAnalysis's macro-pattern errors). One poisoned
    // wrapper must not brick the whole package: on error-severity diags
    // with a non-empty keep, drop the wrappers the diagnostics point at
    // (fallback: all of them, when no diag maps back to a kept wrapper),
    // clear the diags, and retry -- same behavior as before trusted-axiom
    // emission for the dropped wrappers, with a note saying so. Errors
    // that persist once the keep is empty are genuine and flow to the
    // usual refusal in `run_lean_backend`. Terminates: every retry
    // strictly shrinks `trusted_keep`.
    loop {
        let (targets, err, upstream_errors_emitted, poisoned) = process_targets_once(
            model,
            package_targets,
            prover_options,
            target.clone(),
            test_mode,
            include_all,
            new_pipeline,
            test_filter.clone(),
            trusted_keep.clone(),
        );
        if upstream_errors_emitted && !trusted_keep.is_empty() {
            let hit: Vec<_> = poisoned.intersection(&trusted_keep).copied().collect();
            let dropped: Vec<_> = if hit.is_empty() {
                trusted_keep.iter().copied().collect()
            } else {
                hit
            };
            let names: Vec<String> = dropped
                .iter()
                .map(|qid| model.get_function(*qid).get_full_name_str())
                .collect();
            eprintln!(
                "new-pipeline: upstream analysis rejected trusted spec wrapper(s) [{}] \
                 (see diagnostics above) -- retrying without them; their `axiom` statements \
                 will NOT be emitted. Fix the reported spec pattern(s) to get the axioms.",
                names.join(", ")
            );
            for qid in dropped {
                trusted_keep.remove(&qid);
            }
            model.clear_diag();
            continue;
        }
        return (targets, err, upstream_errors_emitted);
    }
}

/// Drain (print + mark reported) all error-severity diags, recording the
/// function enclosing each diag label into `poisoned` so the trusted-keep
/// retry above can drop exactly the wrappers the errors point at.
/// Returns true iff any error-severity diag was pending.
fn drain_error_diags(
    model: &GlobalEnv,
    poisoned: &std::cell::RefCell<
        std::collections::BTreeSet<move_model::model::QualifiedId<move_model::model::FunId>>,
    >,
) -> bool {
    if !model.has_errors() {
        return false;
    }
    use codespan_reporting::diagnostic::Severity;
    use termcolor::{ColorChoice, StandardStream};
    let mut writer = StandardStream::stderr(ColorChoice::Auto);
    model.report_diag_with_filter(&mut writer, |d| {
        if d.severity < Severity::Error {
            return false;
        }
        for label in &d.labels {
            let loc = move_model::model::Loc::new(
                label.file_id,
                codespan::Span::new(label.range.start as u32, label.range.end as u32),
            );
            if let Some(fe) = model.get_enclosing_function(&loc) {
                poisoned.borrow_mut().insert(fe.get_qualified_id());
            }
        }
        true
    });
    true
}

fn process_targets_once(
    model: &GlobalEnv,
    package_targets: &PackageTargets,
    prover_options: &ProverOptions,
    target: FunctionHolderTarget,
    test_mode: bool,
    include_all: bool,
    new_pipeline: bool,
    test_filter: Option<crate::lean_pipeline_overrides::TestFilter>,
    trusted_keep: std::collections::BTreeSet<
        move_model::model::QualifiedId<move_model::model::FunId>,
    >,
) -> (
    FunctionTargetsHolder,
    Option<String>,
    bool,
    std::collections::BTreeSet<move_model::model::QualifiedId<move_model::model::FunId>>,
) {
    let mut targets =
        FunctionTargetsHolder::new(prover_options.clone(), package_targets, target.clone());

    // Sticky flag: any upstream Severity::Error diag means the
    // bytecode is malformed. We deliberately drain the diags below so
    // later passes still run, which hides this fact from downstream
    // code — `run_lean_backend` reads the flag to bail before
    // `--new-pipeline`'s stage 1 structurer recurses unboundedly.
    let mut upstream_errors_emitted = false;
    // Functions enclosing an error diag's source span -- the caller uses
    // this to drop poisoned trusted-keep wrappers before retrying.
    let poisoned = std::cell::RefCell::new(std::collections::BTreeSet::new());

    for module in model.get_modules() {
        for func_env in module.get_functions() {
            targets.add_target(&func_env);
        }
    }

    seed_scc_analysis_info(model, &mut targets);

    // Drain any `add_target` errors so `pipeline.run` doesn't bail
    // after the first processor.
    if drain_error_diags(model, &poisoned) {
        upstream_errors_emitted = true;
    }

    // After-each-processor hook drains Severity::Error diags so the
    // run continues past passes that report spec-source problems
    // (QuantifierIteratorAnalysis etc. — they emit Errors but should
    // not halt the pipeline).
    // The new pipeline skips `DynamicFieldAnalysisProcessor` (it models
    // dynamic fields directly in `World`), but later stackless passes
    // (`mono_analysis`) call `dynamic_field_analysis::get_env_info(env)`,
    // which `unwrap()`s the env extension that processor would have set.
    // Seed an empty `DynamicFieldInfo` so they observe "no df mappings"
    // instead of panicking -- df handling is entirely in the lean-pipeline
    // World layer.
    if new_pipeline {
        model.set_extension(
            move_stackless_bytecode::dynamic_field_analysis::DynamicFieldInfo::new(),
        );
    }
    let pipeline = build_lean_pipeline(
        prover_options,
        test_mode,
        include_all,
        new_pipeline,
        test_filter,
        trusted_keep,
    );
    let upstream_errors_cell = std::cell::Cell::new(upstream_errors_emitted);
    let err = pipeline
        .run_with_hook(
            model,
            &mut targets,
            |_| {},
            |_step, _processor, _holders| {
                if drain_error_diags(model, &poisoned) {
                    upstream_errors_cell.set(true);
                }
            },
        )
        .err()
        .map(|p| p.name());
    upstream_errors_emitted = upstream_errors_cell.get();

    // Whatever sits in `targets` after the pipeline is what gets
    // rendered. No post-hoc fixup — see `lean_pipeline_overrides` for
    // the `add_target` gotcha.

    (targets, err, upstream_errors_emitted, poisoned.into_inner())
}

fn seed_scc_analysis_info(model: &GlobalEnv, targets: &mut FunctionTargetsHolder) {
    // These upstream analyses read callee summaries while traversing an SCC.
    // Seed conservative summaries as already stable so earlier processors do
    // not wait on annotations they never update.
    for module in model.get_modules() {
        for func_env in module.get_functions() {
            let qid = func_env.get_qualified_id();
            if let Some(data) = targets.get_data_mut(
                &qid,
                &move_stackless_bytecode::function_target_pipeline::FunctionVariant::Baseline,
            ) {
                seed_conservative_no_abort_info(&mut data.annotations);
            }
            if func_env
                .get_toplevel_attributes()
                .get_(&AttributeKind_::SpecOnly)
                .is_some()
            {
                let mut ids = vec![qid];
                ids.extend(targets.get_spec_by_fun(&qid).copied());
                for id in ids {
                    if let Some(data) = targets.get_data_mut(
                        &id,
                        &move_stackless_bytecode::function_target_pipeline::FunctionVariant::Baseline,
                    ) {
                        seed_empty_spec_global_variable_info(&mut data.annotations);
                    }
                }
            }
        }
    }
}

fn seed_conservative_no_abort_info(
    annotations: &mut move_stackless_bytecode::annotations::Annotations,
) {
    annotations.set(
        move_stackless_bytecode::no_abort_analysis::NoAbortInfo::default(),
        true,
    );
}

fn seed_empty_spec_global_variable_info(
    annotations: &mut move_stackless_bytecode::annotations::Annotations,
) {
    annotations.set(
        move_stackless_bytecode::spec_global_variable_analysis::SpecGlobalVariableInfo::info_union(
            std::iter::empty(),
        ),
        true,
    );
}

fn resolve_base_output_dir(
    package_dir: &Path,
    output_dir: Option<&Path>,
) -> anyhow::Result<PathBuf> {
    let raw = output_dir
        .map(PathBuf::from)
        .unwrap_or_else(|| package_dir.join("output"));
    let resolved = if raw.is_absolute() {
        raw
    } else {
        package_dir.join(raw)
    };
    std::fs::create_dir_all(&resolved)
        .with_context(|| format!("creating output directory {}", resolved.display()))?;
    Ok(resolved)
}

/// Reject packages still on the pre-2026-07 hand-written-Lean layout.
/// The new pipeline reads the proof overlay from `<package-root>/lean/`
/// (seeded `<Pkg>/<Ns>_Proofs.lean` files, shared helper dirs, and
/// root native models at `lean/natives/<Module>Natives.lean` or dependency
/// models at `lean/natives/<Package>/<Module>Natives.lean`); it used to read
/// `sources/lean/` and `natives/`. The hard error is load-bearing: the proof
/// seeder creates missing files and inserts declarations whose names are absent
/// from the source-level ownership/fingerprint index,
/// so silently ignoring an unmigrated tree would seed a fresh `by sorry` file under
/// `lean/` and the lakefile would build those stubs instead
/// of the real proofs -- a proven corpus would quietly read as unproven. The
/// modular pipeline is now the sole supported proof layout, so any Lean proof
/// source left under `sources/lean/` is rejected rather than preserved as a
/// parallel legacy corpus.
fn check_new_pipeline_layout(package_dir: &Path) -> anyhow::Result<()> {
    let old_proofs = package_dir.join("sources").join("lean");
    if let Some(hit) = find_file_with_suffix(&old_proofs, "Proofs.lean") {
        anyhow::bail!(
            "new-pipeline proof files moved to <package-root>/lean/, but {} still sits in the retired sources/lean/ layout.\n\
             Migrate the proof into an exact obligation shard under lean/<Pkg>/<Module>_Proofs/<obligation>.lean and remove the legacy source",
            hit.display()
        );
    }
    let old_natives = package_dir.join("natives");
    if let Some(hit) = find_file_with_suffix(&old_natives, "Natives.lean") {
        anyhow::bail!(
            "user-declared native definitions moved to <package-root>/lean/natives/, but {} still sits in the retired natives/ layout.\n\
             Migrate with: mkdir -p lean && git mv natives lean/natives",
            hit.display()
        );
    }
    Ok(())
}

fn find_file_with_suffix(dir: &Path, suffix: &str) -> Option<PathBuf> {
    let entries = std::fs::read_dir(dir).ok()?;
    for entry in entries.flatten() {
        let path = entry.path();
        if path.is_dir() {
            if let Some(hit) = find_file_with_suffix(&path, suffix) {
                return Some(hit);
            }
        } else if path
            .file_name()
            .and_then(|n| n.to_str())
            .is_some_and(|n| n.ends_with(suffix))
        {
            return Some(path);
        }
    }
    None
}

/// Derive the Move-level ghost-native seed for the legacy backend's
/// `ghost_threading` pass: per ghost-writing NATIVE function, the concrete
/// `(K, V)` spec-global marker pairs its `#[spec(target=...)]` spec reads or
/// writes (`ghost::{global,set,borrow_mut}<K,V>` with a concrete marker
/// struct `K` and closed value type `V`), walked from the spec's RAW
/// stackless bytecode (the holder's processed form may be emptied/lowered).
///
/// Inertness gate: only markers that some TARGET-PACKAGE `#[spec]` function
/// declares (any ghost op incl. `declare_global(_mut)`) survive. The
/// framework `transfer_impl_spec` exists in every client's deps, so without
/// the gate every client calling `transfer` anywhere would re-thread; with
/// it, packages whose specs never mention the markers get an empty seed and
/// byte-identical output.
fn derive_ghost_native_seed(
    env: &GlobalEnv,
    package_targets: &PackageTargets,
) -> move_prover_lean_backend::GhostNativeSeed {
    use move_stackless_bytecode::stackless_bytecode::{Bytecode, Operation};
    use move_stackless_bytecode::stackless_bytecode_generator::StacklessBytecodeGenerator;

    let rw_ops = [
        env.global_qid(),
        env.global_set_qid(),
        env.global_borrow_mut_qid(),
    ];
    let all_ops = [
        env.global_qid(),
        env.global_set_qid(),
        env.global_borrow_mut_qid(),
        env.declare_global_qid(),
        env.declare_global_mut_qid(),
        env.havoc_global_qid(),
    ];

    // Walk one function's raw bytecode for ghost-op `(K, V)` instantiations
    // (concrete marker struct K, closed V).
    let collect = |qid: move_model::model::QualifiedId<move_model::model::FunId>,
                   ops: &[move_model::model::QualifiedId<move_model::model::FunId>]|
     -> Vec<(MoveType, MoveType)> {
        let func_env = env.get_function(qid);
        if func_env.is_native() {
            return Vec::new();
        }
        let data = StacklessBytecodeGenerator::new(&func_env).generate_function();
        let mut pairs = Vec::new();
        for bc in &data.code {
            if let Bytecode::Call(_, _, Operation::Function(mid, fid, type_inst), _, _) = bc {
                let callee = mid.qualified(*fid);
                if ops.contains(&callee)
                    && type_inst.len() == 2
                    && matches!(type_inst[0], MoveType::Datatype(..))
                    && !type_inst[1].is_open()
                {
                    let kv = (type_inst[0].clone(), type_inst[1].clone());
                    if !pairs.contains(&kv) {
                        pairs.push(kv);
                    }
                }
            }
        }
        pairs
    };

    // Gate: markers any target-package spec function touches.
    let mut declared: Vec<(MoveType, MoveType)> = Vec::new();
    for spec_qid in package_targets.target_specs() {
        for kv in collect(*spec_qid, &all_ops) {
            if !declared.contains(&kv) {
                declared.push(kv);
            }
        }
    }
    if declared.is_empty() {
        return Vec::new();
    }

    // Seed: per native with a spec, the gated markers its spec reads/writes.
    let mut seed: move_prover_lean_backend::GhostNativeSeed = Vec::new();
    for module_env in env.get_modules() {
        for func_env in module_env.get_functions() {
            if !func_env.is_native() {
                continue;
            }
            let native_qid = func_env.get_qualified_id();
            let specs = package_targets.get_specs(&native_qid).unwrap_or_default();
            if specs.is_empty() {
                continue;
            }
            // Prefer a client spec (one that is itself a target spec);
            // fall back to the framework (SuiSpecs) spec.
            let chosen = specs
                .iter()
                .find(|s| package_targets.target_specs().contains(*s))
                .or_else(|| specs.iter().next())
                .copied();
            let Some(chosen) = chosen else { continue };
            let markers: Vec<(MoveType, MoveType)> = collect(chosen, &rw_ops)
                .into_iter()
                .filter(|kv| declared.contains(kv))
                .collect();
            if !markers.is_empty() {
                seed.push((native_qid, markers));
            }
        }
    }
    seed
}

async fn run_lean_backend(
    model: &GlobalEnv,
    targets: &FunctionTargetsHolder,
    package_targets: &PackageTargets,
    output_dir: &Path,
    package_dir: &Path,
    config: &GeneralConfig,
    upstream_errors: bool,
    boogie_proven_names: &std::collections::HashSet<String>,
) -> anyhow::Result<Option<NewPipelineRender>> {
    if config.new_pipeline {
        // Bail before stage 1's structurer recurses unboundedly on
        // malformed bytecode left by upstream Error diagnostics
        // (see `upstream_errors_emitted` in `create_and_process_targets`).
        if upstream_errors {
            anyhow::bail!(
                "new-pipeline: refusing to run after upstream emitted error-severity diagnostics. \
                 The resulting bytecode is likely malformed and stage 1's structurer can recurse \
                 unboundedly on it (see plans/lean-pipeline/stage-01-bytecode-cfg.md). \
                 Drop --new-pipeline to fall back to the legacy backend, or fix the upstream \
                 errors reported above first."
            );
        }
        return run_new_pipeline_backend(
            model,
            targets,
            package_targets,
            output_dir,
            package_dir,
            config.new_pipeline_strict,
            config.dump_ir.as_deref(),
            config.dump_ir_stages.as_deref(),
            config.dump_ir_function.as_deref(),
            &config.generation_mode,
            /*test_mode=*/ false,
        )
        .await
        .map(Some);
    }
    move_prover_lean_backend::run_backend_with_boogie_proven(
        model,
        targets,
        output_dir,
        package_dir,
        config.generate_only,
        boogie_proven_names,
        derive_ghost_native_seed(model, package_targets),
    )
    .await?;
    println!(
        "Lean code generated successfully in {}",
        output_dir.display()
    );
    Ok(None)
}

/// A completed new-pipeline render: the output-directory lock plus the model
/// bundle that render actually resolved. `--audit-proofs` byte-checks the
/// binary against THAT directory, so it has to be the same value the render
/// used, not a second resolution.
struct NewPipelineRender {
    transaction: lean_pipeline::render::RenderOutputLock,
    lemmas_dir: PathBuf,
}

/// Drive the new `lean-pipeline` crate: run the full IR pipeline
/// (stages 1-8 + 10), render, and write `<output_dir>`. Unsupported
/// constructs surface as `RenderError`s.
async fn run_new_pipeline_backend(
    env: &GlobalEnv,
    targets: &FunctionTargetsHolder,
    package_targets: &PackageTargets,
    output_dir: &Path,
    package_dir: &Path,
    strict: bool,
    dump_ir: Option<&Path>,
    dump_ir_stages: Option<&Path>,
    dump_ir_function: Option<&str>,
    generation_mode: &LeanGenerationMode,
    // `--test` generation. Hard-locks loop helpers to `partial_fixpoint`
    // (a `sorry` in a termination arg would poison the drivers' `#eval`);
    // spec/proof generation passes `false` and may emit total loop `def`s.
    test_mode: bool,
) -> anyhow::Result<NewPipelineRender> {
    use stackless_to_intermediate::package_utils::extract_package_name;

    let package_policy_dir = Some(proof_overlay_dir(package_dir));
    let proof_sources_dir = use_durable_proof_overlay(test_mode, generation_mode).then(|| {
        package_policy_dir
            .clone()
            .expect("proof mode has package policy dir")
    });
    let output_lock = lean_pipeline::render::acquire_render_output_lock(
        output_dir,
        proof_sources_dir.as_deref(),
        package_policy_dir.as_deref(),
    )
    .map_err(|error| anyhow::anyhow!("new-pipeline output lock failed: {error:?}"))?;
    let pipeline_start = std::time::Instant::now();
    let mode = if strict {
        lean_pipeline::stage_02_ir_cfg::FailureMode::Strict
    } else {
        lean_pipeline::stage_02_ir_cfg::FailureMode::Permissive
    };
    let abort_payload_mode = if test_mode {
        lean_pipeline::ir::AbortPayloadMode::ObservedTest
    } else {
        lean_pipeline::ir::AbortPayloadMode::Proof
    };
    // Stage-hook closure for --dump-ir-stages. Two top-level
    // arms (Some/None on the stages path); when also given
    // --dump-ir-function FILTER, write all stages of matching
    // functions to one combined file rather than per-stage dirs.
    // Stage hook lives within each arm so the closure's captures
    // are scoped to the single `run_with_mode` invocation
    // (avoids NLL entanglement with the rest of the function).
    let pkg_lookup = |mid| {
        let module_env = env.get_module(mid);
        extract_package_name(env, &module_env)
    };
    let output = match dump_ir_stages {
        Some(stages_path) if dump_ir_function.is_some() => {
            // FILTER MODE: single combined file with all stages.
            let stages_path = stages_path.to_path_buf();
            let filter = dump_ir_function.unwrap().to_string();
            // File path: <dir>/<sanitized_filter>.ir.txt
            if let Err(err) = std::fs::create_dir_all(&stages_path) {
                anyhow::bail!(
                    "--dump-ir-stages: failed to create {}: {:?}",
                    stages_path.display(),
                    err
                );
            }
            let combined_path = stages_path.join(format!("{}.ir.txt", sanitize_segment(&filter)));
            // Truncate up-front so the closure can plain-append after.
            if let Err(err) = std::fs::write(&combined_path, "") {
                anyhow::bail!(
                    "--dump-ir-function: failed to create {}: {:?}",
                    combined_path.display(),
                    err
                );
            }
            eprintln!(
                "--dump-ir-function: writing combined file to {}",
                combined_path.display()
            );
            let mut hook = move |stage_name: &str, program: &lean_pipeline::ir::Program| {
                let body = render_filtered_functions(program, &filter);
                let banner = format!(
                    "// {sep}\n// {stage}\n// {sep}\n\n",
                    sep = "=".repeat(68),
                    stage = stage_name,
                );
                let chunk = format!("{}{}\n", banner, body);
                if let Err(err) = std::fs::OpenOptions::new()
                    .append(true)
                    .open(&combined_path)
                    .and_then(|mut f| {
                        use std::io::Write as _;
                        f.write_all(chunk.as_bytes())
                    })
                {
                    eprintln!(
                        "--dump-ir-function: failed to append to {}: {:?}",
                        combined_path.display(),
                        err
                    );
                }
            };
            lean_pipeline::stage_02_ir_cfg::run_with_abort_payload_mode(
                env,
                targets,
                Some(package_targets),
                pkg_lookup,
                mode,
                abort_payload_mode,
                Some(&mut hook),
            )
        }
        Some(stages_path) => {
            // PER-STAGE DIRS: existing behavior.
            let stages_path = stages_path.to_path_buf();
            let mut hook = move |stage_name: &str, program: &lean_pipeline::ir::Program| {
                let stage_dir = stages_path.join(stage_name);
                if let Err(err) = std::fs::create_dir_all(&stage_dir) {
                    eprintln!(
                        "--dump-ir-stages: failed to create {}: {:?}",
                        stage_dir.display(),
                        err
                    );
                    return;
                }
                if let Err(err) = dump_ir_program(program, &stage_dir) {
                    eprintln!(
                        "--dump-ir-stages: failed to write {}: {:?}",
                        stage_dir.display(),
                        err
                    );
                }
            };
            lean_pipeline::stage_02_ir_cfg::run_with_abort_payload_mode(
                env,
                targets,
                Some(package_targets),
                pkg_lookup,
                mode,
                abort_payload_mode,
                Some(&mut hook),
            )
        }
        None => {
            if dump_ir_function.is_some() {
                eprintln!("--dump-ir-function: ignored because --dump-ir-stages was not set");
            }
            lean_pipeline::stage_02_ir_cfg::run_with_abort_payload_mode(
                env,
                targets,
                Some(package_targets),
                pkg_lookup,
                mode,
                abort_payload_mode,
                None,
            )
        }
    }
    .map_err(|err| anyhow::anyhow!("new-pipeline driver failed: {err}"))?;
    let diagnostic_rows: Vec<_> = output
        .diagnostics
        .iter()
        .map(|diagnostic| {
            let severity = match diagnostic.severity {
                lean_pipeline::stage_02_ir_cfg::DiagnosticSeverity::Warning => "warning",
                lean_pipeline::stage_02_ir_cfg::DiagnosticSeverity::Error => "error",
            };
            serde_json::json!({
                "severity": severity,
                "pass": diagnostic.pass,
                "code": diagnostic.code,
                "function": diagnostic.function,
                "detail": diagnostic.detail,
            })
        })
        .collect();
    let diagnostics =
        serde_json::to_vec_pretty(&serde_json::json!({ "diagnostics": diagnostic_rows }))?;
    if !output.skipped.is_empty() {
        // NOT "sorry stubs": `lift_function_stub` emits an
        // unconditional `BlockTail::Abort`, so the value side renders as
        // the `default` placeholder and `.aborts` as constant `Aborted`.
        // No `sorry` reaches the output, which is why `--audit-proofs`
        // counts zero of them while the function stays unmodelled.
        eprintln!(
            "new-pipeline: {} function(s) UNMODELLED (left as unconditionally-aborting `default` stubs, NOT sorries -- the proof audit cannot see these):",
            output.skipped.len()
        );
        for (name, err) in output.skipped.iter().take(20) {
            eprintln!("  - {}: {:?}", name, err);
        }
        if output.skipped.len() > 20 {
            eprintln!("  ... ({} more skipped)", output.skipped.len() - 20);
        }
    }
    eprintln!(
        "\u{23F1} new-pipeline IR pipeline took: {}ms",
        pipeline_start.elapsed().as_millis()
    );

    if let Some(dump_path) = dump_ir {
        dump_ir_program(&output.program, dump_path)
            .map_err(|err| anyhow::anyhow!("--dump-ir failed: {:?}", err))?;
        eprintln!("new-pipeline: IR dumped to {}", dump_path.display());
    }

    let render_start = std::time::Instant::now();
    let configured_lemmas = std::env::var_os("SUI_LEAN_LEMMAS_DIR").map(PathBuf::from);
    let executable = std::env::current_exe().ok();
    let lemmas_src =
        resolve_lean_pipeline_lemmas_dir(configured_lemmas.as_deref(), executable.as_deref())?;
    // The bundle is the MODEL half of the world-threading contract; this
    // binary is the EMISSION half. A binary copied out of its build tree
    // finds no adjacent bundle and falls back to the compile-time
    // `CARGO_MANIFEST_DIR` sibling -- i.e. it silently reads whatever
    // branch that source tree happens to be on now. The only symptom is a
    // wall of `Function expected at <Native>.new .. ctx.val ... applied to
    // the argument world` out of the native-model classification query.
    // Naming the bundle makes that a one-line diagnosis.
    eprintln!("new-pipeline: Lean model bundle: {}", lemmas_src.display());
    // Discover the user's Move package name from its explicit package root.
    let user_pkg = read_user_package_name(package_dir)?;
    // Per-module file emission allows rendering every non-native
    // module without the cycle that single-file emission had.
    // Loop-emission mode + optional measure/proof registry. The registry
    // lives at the explicit package root, so it sits in the client repo
    // alongside the Move sources and is durable /
    // committable across regeneration. A missing file means every loop
    // helper stays `partial_fixpoint` (the zero-config default).
    let loop_mode = if test_mode {
        lean_pipeline::render::loop_termination::LoopMode::Test
    } else {
        lean_pipeline::render::loop_termination::LoopMode::Proof
    };
    let loop_registry_path = package_dir.join("loop_termination.txt");
    let expected_obligations = if use_complete_obligation_roster(test_mode, generation_mode) {
        Some(render_expected_obligations(
            env,
            package_targets,
            &output.program,
        )?)
    } else {
        None
    };
    let mut sidecars = vec![lean_pipeline::render::RenderSidecar::write(
        "pipeline_diagnostics.json",
        diagnostics,
    )];
    sidecars.push(match expected_obligations {
        Some(contents) => {
            lean_pipeline::render::RenderSidecar::write("expected_obligations.toml", contents)
        }
        None => lean_pipeline::render::RenderSidecar::remove("expected_obligations.toml"),
    });
    lean_pipeline::render::render_program_to_dir_with_policy_locked_and_sidecars(
        &output.program,
        output_dir,
        Some(&lemmas_src),
        None,
        proof_sources_dir.as_deref(),
        package_policy_dir.as_deref(),
        loop_mode,
        Some(&loop_registry_path),
        Some(user_pkg.as_str()),
        &output_lock,
        &sidecars,
    )
    .map_err(|err| anyhow::anyhow!("new-pipeline render failed: {:?}", err))?;
    eprintln!(
        "\u{23F1} new-pipeline render took: {}ms",
        render_start.elapsed().as_millis()
    );
    if let Some(seed) = std::env::var_os(OLEAN_SEED_ENV).map(PathBuf::from) {
        let seeded = lean_pipeline::render::olean_seed::seed_lake_build(&seed, output_dir)
            .map_err(|err| anyhow::anyhow!("{OLEAN_SEED_ENV}: {:?}", err))?;
        eprintln!(
            "new-pipeline: seeded {seeded} prebuilt bundle module(s) from {}",
            seed.display()
        );
    }

    println!(
        "new-pipeline Lean project written to {}",
        output_dir.display()
    );
    Ok(NewPipelineRender {
        transaction: output_lock,
        lemmas_dir: lemmas_src,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use tempfile::tempdir;

    struct RestoreCwd(PathBuf);

    impl Drop for RestoreCwd {
        fn drop(&mut self) {
            std::env::set_current_dir(&self.0).expect("restore test cwd");
        }
    }

    #[test]
    fn scc_analysis_seeds_are_present_and_at_fixedpoint() {
        let mut annotations = move_stackless_bytecode::annotations::Annotations::default();

        seed_conservative_no_abort_info(&mut annotations);
        seed_empty_spec_global_variable_info(&mut annotations);

        let no_abort = annotations
            .get::<move_stackless_bytecode::no_abort_analysis::NoAbortInfo>()
            .expect("seeded no-abort info");
        assert!(!no_abort.does_not_abort);
        let info = annotations
            .get::<move_stackless_bytecode::spec_global_variable_analysis::SpecGlobalVariableInfo>()
            .expect("seeded spec-global info");
        assert!(info.all_vars().next().is_none());
        assert!(annotations.reached_fixedpoint());
    }

    #[test]
    fn translated_spec_only_scc_completes_summary_analyses() {
        let temp = tempdir().expect("tempdir");
        let original_cwd = std::env::current_dir().expect("current dir");
        let _restore_cwd = RestoreCwd(original_cwd);
        std::fs::create_dir_all(temp.path().join("sources")).expect("create sources");
        std::fs::write(
            temp.path().join("Move.toml"),
            r#"[package]
name = "spec_only_scc_fixture"
edition = "2024.beta"

[addresses]
spec_only_scc_fixture = "0x0"

[dependencies]
"#,
        )
        .expect("write Move.toml");
        std::fs::write(
            temp.path().join("sources").join("spec_only_scc.move"),
            r#"module spec_only_scc_fixture::spec_only_scc;

#[spec_only]
use prover::prover::ensures;

#[spec_only, ext(world)]
native fun world_predicate(x: &u64): bool;

#[spec_only]
fun cycle_a(x: &u64): bool {
    cycle_b(x)
}

#[spec_only]
fun cycle_b(x: &u64): bool {
    cycle_c(x)
}

#[spec_only]
fun cycle_c(x: &u64): bool {
    world_predicate(x) && cycle_a(x)
}

#[spec(prove)]
fun verify_cycle(x: &u64): bool {
    let result = cycle_a(x);
    ensures(result);
    result
}
"#,
        )
        .expect("write SCC source");

        let model = build_model(
            Some(temp.path()),
            Some(BuildConfig {
                skip_fetch_latest_git_deps: true,
                ..BuildConfig::default()
            }),
        )
        .expect("build model");
        assert!(!model.has_errors(), "fixture model has errors");
        let package_targets =
            PackageTargets::new(&model, TargetFilterOptions::default(), false, None);
        let mut targets = FunctionTargetsHolder::new(
            ProverOptions::default(),
            &package_targets,
            FunctionHolderTarget::All,
        );
        for module in model.get_modules() {
            for function in module.get_functions() {
                targets.add_target(&function);
            }
        }
        seed_scc_analysis_info(&model, &mut targets);
        let mut pipeline = FunctionTargetPipeline::default();
        pipeline.add_processor(
            crate::lean_pipeline_overrides::LeanVerificationAnalysisProcessor::new(
                false,
                std::collections::BTreeSet::new(),
            ),
        );
        pipeline.add_processor(
            move_stackless_bytecode::spec_global_variable_analysis::SpecGlobalVariableAnalysisProcessor::new(),
        );
        pipeline.add_processor(
            move_stackless_bytecode::no_abort_analysis::NoAbortAnalysisProcessor::new(),
        );
        pipeline
            .run(&model, &mut targets)
            .unwrap_or_else(|processor| panic!("{} failed", processor.name()));

        let native_qid = model
            .get_modules()
            .find_map(|module| {
                module
                    .get_functions()
                    .find(|function| function.get_name_str() == "world_predicate")
                    .map(|function| function.get_qualified_id())
            })
            .expect("world_predicate function");
        let native_data = targets
            .get_data(
                &native_qid,
                &move_stackless_bytecode::function_target_pipeline::FunctionVariant::Baseline,
            )
            .expect("retained native target");
        assert!(native_data
            .annotations
            .has::<move_stackless_bytecode::spec_global_variable_analysis::SpecGlobalVariableInfo>(
        ));
        assert!(native_data
            .annotations
            .has::<move_stackless_bytecode::no_abort_analysis::NoAbortInfo>());
    }

    #[test]
    fn configured_lemmas_bundle_supports_a_relocated_binary() {
        let temp = tempdir().unwrap();
        let lemmas = temp.path().join("distribution/lemmas");
        for relative in ["Prelude/BoundedNat.lean", "natives/Prover/MoveAuto.lean"] {
            let path = lemmas.join(relative);
            std::fs::create_dir_all(path.parent().unwrap()).unwrap();
            std::fs::write(path, "").unwrap();
        }

        assert_eq!(
            resolve_lean_pipeline_lemmas_dir(Some(&lemmas), None).unwrap(),
            lemmas.canonicalize().unwrap()
        );
    }

    fn roster_function(
        module: lean_pipeline::ir::ModId,
        name: &str,
    ) -> lean_pipeline::ir::Function {
        lean_pipeline::ir::Function {
            module,
            name: name.to_string(),
            signature: lean_pipeline::ir::Signature {
                type_params: Vec::new(),
                params: Vec::new(),
                return_type: lean_pipeline::ir::Type::Unit,
            },
            body: lean_pipeline::ir::Block::just(lean_pipeline::ir::Expr::Unit),
            kind: lean_pipeline::ir::FunctionKind::Source,
            effects: lean_pipeline::ir::Effects::PURE,
            explicit_pure: false,
        }
    }

    fn framework_roster_program() -> lean_pipeline::ir::Program {
        let mut program = lean_pipeline::ir::Program::default();
        program.modules.insert(
            0,
            lean_pipeline::ir::Module {
                name: "tx_context_spec".to_string(),
                package_name: "SuiSpecs".to_string(),
                address: String::new(),
                required_imports: Vec::new(),
                is_native: false,
            },
        );
        program.modules.insert(
            1,
            lean_pipeline::ir::Module {
                name: "tx_context".to_string(),
                package_name: "Sui".to_string(),
                address: String::new(),
                required_imports: Vec::new(),
                is_native: false,
            },
        );
        program
            .functions
            .insert(10, roster_function(0, "fresh_object_address_spec"));
        program
            .functions
            .insert(20, roster_function(1, "fresh_object_address"));
        program
            .trusted_spec_to_impl
            .insert(10, (20, lean_pipeline::ir::TrustReason::NonProve));
        program
    }

    fn framework_candidate(source: &str, required: bool) -> ExpectedObligationCandidate {
        ExpectedObligationCandidate {
            source: source.to_string(),
            target: "Sui::tx_context::fresh_object_address".to_string(),
            kind: ExpectedObligationKind::TrustedAxiom(lean_pipeline::ir::TrustReason::NonProve),
            required,
        }
    }

    #[test]
    fn expected_roster_includes_active_framework_trusted_spec_only() {
        let program = framework_roster_program();
        let mut candidates = std::collections::BTreeMap::new();
        insert_expected_obligation_candidate(
            &mut candidates,
            framework_candidate(
                "SuiSpecs::tx_context_spec::fresh_object_address_spec",
                false,
            ),
        )
        .unwrap();
        insert_expected_obligation_candidate(
            &mut candidates,
            framework_candidate("SuiSpecs::unused_spec::inactive_spec", false),
        )
        .unwrap();

        let resolved = resolve_expected_obligation_candidates(&program, candidates).unwrap();

        assert_eq!(resolved.len(), 1);
        assert_eq!(
            resolved[0].candidate.source,
            "SuiSpecs::tx_context_spec::fresh_object_address_spec"
        );
        assert_eq!(resolved[0].source_fid, 10);
        assert_eq!(resolved[0].target_fid, 20);
        assert_eq!(resolved[0].candidate.kind.reason(), Some("non_prove"));
    }

    #[test]
    fn expected_roster_rejects_unauthorized_ir_trust_pair() {
        let mut program = framework_roster_program();
        program
            .functions
            .insert(11, roster_function(0, "unexpected_spec"));
        program
            .trusted_spec_to_impl
            .insert(11, (20, lean_pipeline::ir::TrustReason::NonProve));
        let mut candidates = std::collections::BTreeMap::new();
        insert_expected_obligation_candidate(
            &mut candidates,
            framework_candidate(
                "SuiSpecs::tx_context_spec::fresh_object_address_spec",
                false,
            ),
        )
        .unwrap();

        let error = resolve_expected_obligation_candidates(&program, candidates).unwrap_err();

        assert!(
            error
                .to_string()
                .contains("has no active authoritative PackageTargets source"),
            "{error:#}"
        );
    }

    #[test]
    fn expected_roster_rejects_wrong_framework_trust_reason() {
        let mut program = framework_roster_program();
        program
            .trusted_spec_to_impl
            .insert(10, (20, lean_pipeline::ir::TrustReason::Skip));
        let mut candidates = std::collections::BTreeMap::new();
        insert_expected_obligation_candidate(
            &mut candidates,
            framework_candidate(
                "SuiSpecs::tx_context_spec::fresh_object_address_spec",
                false,
            ),
        )
        .unwrap();

        let error = resolve_expected_obligation_candidates(&program, candidates).unwrap_err();

        assert!(
            error.to_string().contains("absent or miswired"),
            "{error:#}"
        );
    }

    #[test]
    fn expected_roster_keeps_target_package_specs_mandatory() {
        let program = lean_pipeline::ir::Program::default();
        let mut candidates = std::collections::BTreeMap::new();
        insert_expected_obligation_candidate(
            &mut candidates,
            ExpectedObligationCandidate {
                source: "ClientSpecs::m::f_spec".to_string(),
                target: "Client::m::f".to_string(),
                kind: ExpectedObligationKind::Theorem,
                required: true,
            },
        )
        .unwrap();

        let error = resolve_expected_obligation_candidates(&program, candidates).unwrap_err();

        assert!(
            error
                .to_string()
                .contains("target-package spec `ClientSpecs::m::f_spec` is absent"),
            "{error:#}"
        );
    }

    #[test]
    fn resolve_base_output_dir_creates_missing_relative_dir() {
        let temp = tempdir().expect("tempdir");
        let package_dir = temp.path().join("pkg");
        std::fs::create_dir_all(&package_dir).expect("create package dir");

        let resolved =
            resolve_base_output_dir(&package_dir, Some(Path::new("nested/out"))).unwrap();

        assert_eq!(resolved, package_dir.join("nested/out"));
        assert!(
            resolved.is_dir(),
            "missing relative output dir should be created"
        );
    }

    #[test]
    fn package_name_is_read_with_toml_semantics() {
        let temp = tempdir().unwrap();
        std::fs::write(
            temp.path().join("Move.toml"),
            "[package]\nname = 'InlineComment' # valid TOML comment\n",
        )
        .unwrap();
        assert_eq!(
            read_user_package_name(temp.path()).unwrap(),
            "InlineComment"
        );

        std::fs::write(temp.path().join("Move.toml"), "[package]\nversion = 1\n").unwrap();
        assert!(read_user_package_name(temp.path()).is_err());
    }

    /// `-h` renders only a doc comment's FIRST paragraph; `--help` renders
    /// all of it. The trust delta therefore has to live in that first
    /// paragraph, or the person who reaches for `--audit-clean-room` at 2am
    /// and types `-h` is told only that it makes the audit slower. This test
    /// exists because that was in fact the case until it was measured: the
    /// risk statement sat in paragraph three and `-h` silently dropped it.
    #[test]
    fn the_clean_room_flag_states_its_trust_delta_in_the_short_help() {
        use clap::CommandFactory;

        #[derive(clap::Parser)]
        struct HelpProbe {
            #[clap(flatten)]
            _general: GeneralConfig,
        }

        let flatten = |text: String| text.split_whitespace().collect::<Vec<_>>().join(" ");
        let short = flatten(HelpProbe::command().render_help().to_string());
        let long = flatten(HelpProbe::command().render_long_help().to_string());

        for (form, rendered) in [("-h", &short), ("--help", &long)] {
            assert!(
                rendered.contains("--audit-clean-room"),
                "{form}: {rendered}"
            );
            assert!(
                rendered.contains("TRUST DELTA"),
                "{form} dropped the trust delta: {rendered}"
            );
            assert!(
                rendered.contains("trusts Lake's incremental correctness"),
                "{form} dropped what the fast path trusts: {rendered}"
            );
            assert!(
                rendered.contains("assuming the build is current"),
                "{form} dropped what the fast path actually answers: {rendered}"
            );
            assert!(
                rendered.contains("does NOT answer \"is this corpus verified\""),
                "{form} dropped what the fast path does NOT answer: {rendered}"
            );
        }
        // Only the long form has room for the policy and the full rationale.
        assert!(long.contains("cached is the default"), "{long}");
        assert!(long.contains("may never reuse a VERDICT"), "{long}");
        assert!(
            long.contains("content-based rather than mtime-based"),
            "{long}"
        );
    }

    #[test]
    fn proof_audit_options_cannot_be_silently_ignored_by_early_exit_modes() {
        validate_audit_options(
            false,
            false,
            false,
            false,
            false,
            true,
            true,
            false,
            &LeanGenerationMode::Function,
        )
        .unwrap();

        let err = validate_audit_options(
            true,
            false,
            false,
            false,
            false,
            false,
            false,
            false,
            &LeanGenerationMode::All,
        )
        .unwrap_err();
        assert!(err.to_string().contains("requires --new-pipeline"), "{err}");

        let err = validate_audit_options(
            true,
            false,
            false,
            false,
            true,
            true,
            false,
            false,
            &LeanGenerationMode::All,
        )
        .unwrap_err();
        assert!(
            err.to_string().contains("cannot be used with --test"),
            "{err}"
        );

        let err = validate_audit_options(
            true,
            false,
            false,
            false,
            true,
            false,
            true,
            false,
            &LeanGenerationMode::All,
        )
        .unwrap_err();
        assert!(
            err.to_string().contains("cannot be used with --stats"),
            "{err}"
        );

        let err = validate_audit_options(
            true,
            false,
            false,
            false,
            true,
            false,
            false,
            false,
            &LeanGenerationMode::Module,
        )
        .unwrap_err();
        assert!(err.to_string().contains("--generation-mode all"), "{err}");

        let err = validate_audit_options(
            false,
            false,
            true,
            false,
            true,
            false,
            false,
            false,
            &LeanGenerationMode::All,
        )
        .unwrap_err();
        assert!(err.to_string().contains("requires --audit-proofs"), "{err}");

        let err = validate_audit_options(
            false,
            true,
            false,
            false,
            true,
            false,
            false,
            false,
            &LeanGenerationMode::All,
        )
        .unwrap_err();
        assert!(
            err.to_string()
                .contains("--audit-existing requires --audit-proofs"),
            "{err}"
        );

        let err = validate_audit_options(
            true,
            true,
            false,
            false,
            true,
            false,
            false,
            true,
            &LeanGenerationMode::All,
        )
        .unwrap_err();
        assert!(
            err.to_string()
                .contains("--audit-existing cannot be used with --generate-only"),
            "{err}"
        );

        // The clean-room switch is a proof-audit knob and must never be
        // reachable without the audit it modifies.
        let err = validate_audit_options(
            false,
            false,
            false,
            true,
            true,
            false,
            false,
            false,
            &LeanGenerationMode::All,
        )
        .unwrap_err();
        assert!(
            err.to_string()
                .contains("--audit-clean-room requires --audit-proofs"),
            "{err}"
        );

        validate_audit_options(
            true,
            false,
            true,
            true,
            true,
            false,
            false,
            false,
            &LeanGenerationMode::All,
        )
        .unwrap();

        validate_audit_options(
            true,
            true,
            true,
            true,
            true,
            false,
            false,
            false,
            &LeanGenerationMode::All,
        )
        .unwrap();
    }

    #[test]
    fn proof_overlay_is_anchored_to_explicit_package_root() {
        let temp = tempdir().unwrap();
        let package_dir = temp.path().join("selected-by-path");
        assert_eq!(proof_overlay_dir(&package_dir), package_dir.join("lean"));
    }

    #[test]
    fn durable_overlay_and_roster_follow_generation_mode() {
        for (test_mode, generation_mode, expected_overlay, expected_roster) in [
            (false, LeanGenerationMode::All, true, true),
            (false, LeanGenerationMode::Module, false, false),
            (false, LeanGenerationMode::Function, false, false),
            (true, LeanGenerationMode::All, false, false),
            (true, LeanGenerationMode::Module, false, false),
            (true, LeanGenerationMode::Function, false, false),
        ] {
            assert_eq!(
                use_durable_proof_overlay(test_mode, &generation_mode),
                expected_overlay,
                "test_mode={test_mode}, generation_mode={generation_mode:?}"
            );
            assert_eq!(
                use_complete_obligation_roster(test_mode, &generation_mode),
                expected_roster,
                "test_mode={test_mode}, generation_mode={generation_mode:?}"
            );
        }
    }

    #[test]
    fn resolve_base_output_dir_creates_missing_absolute_dir() {
        let temp = tempdir().expect("tempdir");
        let package_dir = temp.path().join("pkg");
        let output_dir = temp.path().join("new-output");
        std::fs::create_dir_all(&package_dir).expect("create package dir");

        let resolved = resolve_base_output_dir(&package_dir, Some(&output_dir)).unwrap();

        assert_eq!(resolved, output_dir);
        assert!(
            resolved.is_dir(),
            "missing absolute output dir should be created"
        );
    }

    #[test]
    fn layout_guard_rejects_unmigrated_proof_tree() {
        let temp = tempdir().expect("tempdir");
        let old = temp.path().join("sources/lean/FooSpecs");
        std::fs::create_dir_all(&old).unwrap();
        std::fs::write(old.join("Bar_specs_Proofs.lean"), "-- proof").unwrap();

        let err = check_new_pipeline_layout(temp.path()).unwrap_err();
        assert!(err.to_string().contains("sources/lean"), "{err}");
    }

    #[test]
    fn layout_guard_rejects_unmigrated_natives_dir() {
        let temp = tempdir().expect("tempdir");
        let old = temp.path().join("natives");
        std::fs::create_dir_all(&old).unwrap();
        std::fs::write(old.join("BarNatives.lean"), "-- native").unwrap();

        let err = check_new_pipeline_layout(temp.path()).unwrap_err();
        assert!(err.to_string().contains("lean/natives"), "{err}");
    }

    #[test]
    fn layout_guard_rejects_legacy_proofs_beside_migrated_tree() {
        let temp = tempdir().expect("tempdir");
        let new = temp.path().join("lean/FooSpecs");
        std::fs::create_dir_all(&new).unwrap();
        std::fs::write(new.join("Bar_specs_Proofs.lean"), "-- proof").unwrap();
        std::fs::create_dir_all(temp.path().join("lean/natives")).unwrap();
        std::fs::write(
            temp.path().join("lean/natives/BarNatives.lean"),
            "-- native",
        )
        .unwrap();
        let legacy = temp.path().join("sources/lean/Proofs");
        std::fs::create_dir_all(&legacy).unwrap();
        std::fs::write(legacy.join("Tick_mathProofs.lean"), "-- legacy").unwrap();

        let err = check_new_pipeline_layout(temp.path()).unwrap_err();
        assert!(err.to_string().contains("legacy source"), "{err}");
    }
}

/// Write `program` to disk in the human-readable pseudocode format
/// (see `lean_pipeline::ir::fmt`). If `dest` is an existing directory
/// or ends in a path separator, writes one file per module
/// (`<package>__<module>.ir.txt`) plus a top-level `program.ir.txt`.
/// Otherwise writes everything to the single `dest` file. Creates
/// parent directories as needed.
fn dump_ir_program(program: &lean_pipeline::ir::Program, dest: &Path) -> anyhow::Result<()> {
    let treat_as_dir = dest.is_dir()
        || dest
            .to_str()
            .map(|s| s.ends_with(std::path::MAIN_SEPARATOR) || s.ends_with('/'))
            .unwrap_or(false);

    if treat_as_dir {
        std::fs::create_dir_all(dest).context("create --dump-ir directory")?;
        let summary = dest.join("program.ir.txt");
        std::fs::write(&summary, format!("{}", program))
            .with_context(|| format!("writing {}", summary.display()))?;
        for (mid, module) in &program.modules {
            let safe_pkg = sanitize_segment(&module.package_name);
            let safe_mod = sanitize_segment(&module.name);
            let path = dest.join(format!("{}__{}.ir.txt", safe_pkg, safe_mod));
            let body = render_module_subset(program, *mid);
            std::fs::write(&path, body).with_context(|| format!("writing {}", path.display()))?;
        }
    } else {
        if let Some(parent) = dest.parent() {
            if !parent.as_os_str().is_empty() {
                std::fs::create_dir_all(parent)
                    .with_context(|| format!("create parent of {}", dest.display()))?;
            }
        }
        std::fs::write(dest, format!("{}", program))
            .with_context(|| format!("writing {}", dest.display()))?;
    }
    Ok(())
}

/// Render a single module's subset of the program: its structs, native
/// decls and translated functions. The module-id header makes the file
/// self-explanatory.
fn render_module_subset(
    program: &lean_pipeline::ir::Program,
    mid: lean_pipeline::ir::ModId,
) -> String {
    use std::fmt::Write as _;
    let mut out = String::new();
    let m = match program.modules.get(&mid) {
        Some(m) => m,
        None => return out,
    };
    let _ = writeln!(out, "// {} (M#{})", m, mid);
    let _ = writeln!(
        out,
        "//   structs / natives / functions belonging to this module"
    );
    let _ = writeln!(out);

    let mut wrote = false;
    for (sid, s) in &program.structs {
        if s.module_id != mid {
            continue;
        }
        if !wrote {
            let _ = writeln!(out, "// ---- Structs ----");
            wrote = true;
        }
        let _ = writeln!(
            out,
            "{}",
            DisplayStruct {
                sid: *sid,
                s,
                program
            }
        );
    }
    wrote = false;
    for (fid, d) in &program.natives.decls {
        if d.module != mid {
            continue;
        }
        if !wrote {
            let _ = writeln!(out);
            let _ = writeln!(out, "// ---- Natives ----");
            wrote = true;
        }
        let _ = writeln!(
            out,
            "{}",
            DisplayNative {
                fid: *fid,
                d,
                program
            }
        );
    }
    wrote = false;
    for (fid, fun) in &program.functions {
        if fun.module != mid {
            continue;
        }
        if !wrote {
            let _ = writeln!(out);
            let _ = writeln!(out, "// ---- Functions ----");
            wrote = true;
        }
        let _ = writeln!(
            out,
            "{}",
            DisplayFunction {
                fid: *fid,
                fun,
                program
            }
        );
    }
    out
}

/// Render every function (and native) whose name matches `filter`,
/// using the IR's `Display` impls with full `Program` context so
/// callee names, struct names and field names are resolved.
///
/// Filter forms:
///   - bare name (`count_up`)  -> matches across all modules
///   - qualified name (`math::count_up`) -> matches only inside `math`
///
/// Match rule: a function name matches `<filter>` if its bare name
/// is exactly `<filter>` OR starts with `<filter>.` (so `count_up`
/// matches `count_up`, `count_up.aborts`, `count_up.while_0`,
/// `count_up.while_0.aborts`, ...).
fn render_filtered_functions(program: &lean_pipeline::ir::Program, filter: &str) -> String {
    use std::fmt::Write as _;
    let (filter_module, filter_name) = match filter.split_once("::") {
        Some((m, n)) => (Some(m), n),
        None => (None, filter),
    };
    let module_name = |mid: lean_pipeline::ir::ModId| -> Option<&str> {
        program.modules.get(&mid).map(|m| m.name.as_str())
    };
    let prefix = format!("{}.", filter_name);
    let matches = |module: Option<&str>, name: &str| -> bool {
        if let Some(fm) = filter_module {
            match module {
                Some(m) if m == fm => {}
                _ => return false,
            }
        }
        name == filter_name || name.starts_with(&prefix)
    };

    let mut out = String::new();
    let mut any = false;
    for (fid, fun) in &program.functions {
        let mname = module_name(fun.module);
        if matches(mname, &fun.name) {
            let _ = writeln!(
                out,
                "{}",
                DisplayFunction {
                    fid: *fid,
                    fun,
                    program
                }
            );
            any = true;
        }
    }
    for (fid, decl) in &program.natives.decls {
        let mname = module_name(decl.module);
        if matches(mname, &decl.name) {
            let _ = writeln!(
                out,
                "{}",
                DisplayNative {
                    fid: *fid,
                    d: decl,
                    program
                }
            );
            any = true;
        }
    }
    if !any {
        let _ = writeln!(out, "// (no functions match filter `{}`)", filter);
    }
    out
}

/// Sanitize a name segment for safe filesystem use: replace anything
/// outside `[A-Za-z0-9_.-]` with `_`, collapse repeats. Path
/// separators and the empty string both become `_`.
fn sanitize_segment(s: &str) -> String {
    if s.is_empty() {
        return "_".to_string();
    }
    let mut out = String::with_capacity(s.len());
    let mut last_was_underscore = false;
    for c in s.chars() {
        let ok = c.is_ascii_alphanumeric() || c == '_' || c == '.' || c == '-';
        if ok {
            out.push(c);
            last_was_underscore = false;
        } else if !last_was_underscore {
            out.push('_');
            last_was_underscore = true;
        }
    }
    if out.is_empty() {
        "_".to_string()
    } else {
        out
    }
}

/// Tiny `Display` wrappers used by `render_module_subset` so each
/// item is printed with full program context (callee names, struct
/// names, field names). The top-level `Display for Program` is fine
/// for the global dump but doesn't expose per-item helpers.
struct DisplayStruct<'a> {
    sid: lean_pipeline::ir::StructId,
    s: &'a lean_pipeline::ir::Struct,
    program: &'a lean_pipeline::ir::Program,
}
impl<'a> std::fmt::Display for DisplayStruct<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        lean_pipeline::ir::fmt::fmt_struct_pub(f, self.sid, self.s, Some(self.program))
    }
}

struct DisplayNative<'a> {
    fid: lean_pipeline::ir::FunId,
    d: &'a lean_pipeline::ir::NativeDecl,
    program: &'a lean_pipeline::ir::Program,
}
impl<'a> std::fmt::Display for DisplayNative<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        lean_pipeline::ir::fmt::fmt_native_pub(f, self.fid, self.d, Some(self.program))
    }
}

struct DisplayFunction<'a> {
    fid: lean_pipeline::ir::FunId,
    fun: &'a lean_pipeline::ir::Function,
    program: &'a lean_pipeline::ir::Program,
}
impl<'a> std::fmt::Display for DisplayFunction<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        lean_pipeline::ir::fmt::fmt_function_pub(f, self.fid, self.fun, Some(self.program))
    }
}

/// Lean-backend analysis pipeline. Mirrors
/// `pipeline_factory::default_pipeline_with_options` minus
/// `ConditionalMergeInsertionProcessor` — our structure discovery handles
/// merge points uniformly, the upstream pass only covers pure/axiom fns.
fn build_lean_pipeline(
    options: &ProverOptions,
    test_mode: bool,
    include_all: bool,
    new_pipeline: bool,
    test_filter: Option<crate::lean_pipeline_overrides::TestFilter>,
    trusted_keep: std::collections::BTreeSet<
        move_model::model::QualifiedId<move_model::model::FunId>,
    >,
) -> FunctionTargetPipeline {
    use crate::lean_pipeline_overrides::{
        LeanDeterministicAnalysisProcessor, LeanNoAbortAnalysisProcessor,
        LeanSpecGlobalVariableAnalysisProcessor, LeanSpecInstrumentationProcessor,
        LeanVerificationAnalysisProcessor,
    };
    use move_stackless_bytecode::{
        borrow_analysis::BorrowAnalysisProcessor, clean_and_optimize::CleanAndOptimizeProcessor,
        debug_instrumentation::DebugInstrumenter,
        dynamic_field_analysis::DynamicFieldAnalysisProcessor,
        eliminate_imm_refs::EliminateImmRefsProcessor, livevar_analysis::LiveVarAnalysisProcessor,
        memory_instrumentation::MemoryInstrumentationProcessor,
        mono_analysis::MonoAnalysisProcessor, move_loop_invariants::MoveLoopInvariantsProcessor,
        mut_ref_instrumentation::MutRefInstrumenter,
        number_operation_analysis::NumberOperationProcessor,
        pure_callee_detection::PureCalleeDetectionProcessor,
        quantifier_iterator_analysis::QuantifierIteratorAnalysisProcessor,
        reaching_def_analysis::ReachingDefProcessor,
        replacement_analysis::ReplacementAnalysisProcessor,
        spec_purity_analysis::SpecPurityAnalysis, usage_analysis::UsageProcessor,
        well_formed_instrumentation::WellFormedInstrumentationProcessor,
    };

    // Entry pass for both spec and test paths; see
    // `lean_pipeline_overrides` for the wrapper's semantics.
    let entry_processor: Box<
        dyn move_stackless_bytecode::function_target_pipeline::FunctionTargetProcessor,
    > = if test_mode {
        LeanVerificationAnalysisProcessor::new_for_testing(include_all, test_filter, trusted_keep)
    } else {
        // The non-test path doesn't have a notion of test filtering; drop
        // any test_filter that snuck in.
        let _ = test_filter;
        LeanVerificationAnalysisProcessor::new(include_all, trusted_keep)
    };

    let mut processors: Vec<
        Box<dyn move_stackless_bytecode::function_target_pipeline::FunctionTargetProcessor>,
    > = vec![
        entry_processor,
        LeanSpecGlobalVariableAnalysisProcessor::new(),
        SpecPurityAnalysis::new(),
        DebugInstrumenter::new(),
        EliminateImmRefsProcessor::new(),
        MutRefInstrumenter::new(),
        LeanNoAbortAnalysisProcessor::new(),
        LeanDeterministicAnalysisProcessor::new(),
        PureCalleeDetectionProcessor::new(),
        DynamicFieldAnalysisProcessor::new(),
        MoveLoopInvariantsProcessor::new(),
        ReachingDefProcessor::new(),
        LiveVarAnalysisProcessor::new(),
        BorrowAnalysisProcessor::new_borrow_natives(options.borrow_natives.clone()),
        MemoryInstrumentationProcessor::new(),
        // ConditionalMergeInsertionProcessor and its liveness rerun omitted —
        // our structure discovery handles merge points for all functions.
        CleanAndOptimizeProcessor::new(),
        UsageProcessor::new(),
        // Convert begin_*_lambda / end_*_lambda call patterns into Operation::Quantifier
        // so the IR translator (translate_quantifier) consumes the structured form.
        // Mirrors upstream `default_pipeline_with_options` ordering.
        QuantifierIteratorAnalysisProcessor::new(),
        ReplacementAnalysisProcessor::new(),
    ];

    // Skip loop analysis (transforms loops into Havoc/Assume/Stop for Boogie)
    // We always skip this for Lean backend.

    processors.append(&mut vec![
        // Wrapper preserves Baseline bytecode for non-verified non-inlined
        // functions (loop_inv helpers, spec_only predicates, etc.) that the
        // upstream processor would clear. Lean code-gen needs the bodies.
        LeanSpecInstrumentationProcessor::new(),
        WellFormedInstrumentationProcessor::new(),
        MonoAnalysisProcessor::new(),
    ]);

    if !options.for_interpretation {
        processors.push(NumberOperationProcessor::new());
    }

    // The new pipeline models dynamic fields directly in `World` (keyed
    // by UID) and does not consume `DynamicFieldInfo`; drop the analysis
    // (and its parent-rewrite / Boogie well-foundedness checks) so df ops
    // keep their natural `&mut UID` form. The legacy lean backend still
    // reads `DynamicFieldInfo`, so it is kept there.
    if new_pipeline {
        processors.retain(|p| p.name() != "dynamic_field_analysis_processor");
        // Re-run live-variable analysis after memory instrumentation. The
        // instrumentation inserts post-merge `is_parent`/write-back uses of
        // arm-local reference temps, and only livevar's transform emits the
        // `Operation::Uninit` entry markers that stage 2 lowers to
        // `Mutation.uninit` sentinels; without a rerun those temps reach
        // stage 5/7 unbound (SuiSystem `convert_to_fungible_staked_sui`).
        // The pre-instrumentation run stays: borrow analysis requires it.
        let after_memory_instr = processors
            .iter()
            .position(|p| p.name() == "memory_instr")
            .expect("memory_instr must be in the lean pipeline")
            + 1;
        processors.insert(after_memory_instr, LiveVarAnalysisProcessor::new());
    }

    let mut res = FunctionTargetPipeline::default();
    for p in processors {
        res.add_processor(p);
    }
    res
}
