//! End-to-end bytecode-to-renderable-IR driver.
//!
//! Walks every Move module in a `GlobalEnv`, lifts module + struct
//! definitions via [`super::module_lift`], runs stage 1
//! ([`crate::stage_01_bytecode_cfg::run`]) on each function's
//! bytecode to produce a [`BytecodeCfg`], then stage 2
//! ([`super::run`]) to produce function bodies. It then applies the
//! post-translation lowering steps in semantic order. Structural correctness
//! is enforced by the invariant registry between stages and at the render gate.
//!
//! ## What this DOES
//!
//! - Emits `Module` entries for every Move module, marking native
//!   ones (per [`super::natives::is_native_function_module`])
//!   `is_native: true`. Functions in native modules are registered
//!   as [`crate::ir::NativeDecl`] entries in `Program::natives.decls`
//!   by `module_lift`; `Program::functions` remains body-only.
//! - Lifts struct + enum definitions for non-native modules.
//! - Lifts function bodies for non-native functions whose bytecode
//!   is available in the targets holder. Native functions remain
//!   body-less declarations in `Program::natives.decls`.
//! - Lowers mutable references, effects, SSA, writebacks, bounded arithmetic,
//!   control flow, spec companions, and proof obligations.
//! - Runs the registered invariant gate before rendering.
//!
//! Package-name resolution stays caller-owned: sui-lean supplies a
//! `package_name_for_module` callback backed by its `Move.toml` lookup.

use move_model::model::{GlobalEnv, ModuleId};
use move_stackless_bytecode::function_target_pipeline::{FunctionTargetsHolder, FunctionVariant};
use move_stackless_bytecode::package_targets::PackageTargets;

use crate::ir::invariants::{display_table, verify_at, InvariantViolation, Stage};
use crate::ir::{Program, ProgramBuilder};

use super::operand_normalization::{self, NormalizeMode};
use super::Stage2Error;

const STAGE_10_PRE_STAGE_7: &str = "stage_10_bounded_nat_pre_stage7";
const STAGE_10_FINAL: &str = "stage_10_bounded_nat_final";

/// Output of [`run`]: the assembled IR program plus diagnostics collected
/// while building it.
#[derive(Debug)]
pub struct PipelineOutput {
    pub program: Program,
    pub diagnostics: Vec<PipelineDiagnostic>,
    /// Per-function failures encountered when `strict == false`.
    /// Empty when strict mode is on (any failure aborts the run).
    pub skipped: Vec<(String, DriverError)>,
    /// Always empty: a render-time invariant violation aborts the run
    /// in BOTH modes. Retained so callers that matched on it keep
    /// compiling. Each violation is still reported individually (with
    /// the offending function resolved) before the run fails, so the
    /// diagnostics are the Permissive ones and the outcome is the
    /// Strict one.
    pub renderer_invariant_warnings: Vec<InvariantViolation>,
}

/// How to handle per-function failures (stage 1 / stage 2
/// `NotImplemented`, `UnsupportedLoop`, etc.) and invariant violations.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FailureMode {
    /// First failure aborts the whole driver. Use for CI gates where
    /// any regression in coverage should surface immediately.
    Strict,
    /// Per-function failures leave the function as a `sorry` stub and
    /// continue. Whole-program pass failures remain fatal so later passes
    /// never consume mixed-phase IR. Invariant violations are recorded.
    /// Use for exploratory runs against real packages where the new
    /// pipeline hasn't reached parity with the legacy backend yet.
    Permissive,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DiagnosticSeverity {
    Warning,
    Error,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PipelineDiagnostic {
    pub severity: DiagnosticSeverity,
    pub pass: &'static str,
    pub code: &'static str,
    pub function: Option<String>,
    pub detail: String,
}

impl PipelineDiagnostic {
    fn error(
        pass: &'static str,
        code: &'static str,
        function: Option<String>,
        detail: String,
    ) -> Self {
        Self {
            severity: DiagnosticSeverity::Error,
            pass,
            code,
            function,
            detail,
        }
    }
}

/// Errors produced by the stage-1 + stage-2 driver.
#[derive(Debug)]
pub enum DriverError {
    /// Stage 1 failed for a specific function.
    Stage1 {
        function: String,
        err: crate::stage_01_bytecode_cfg::Stage1Error,
    },
    /// Stage 2 failed for a specific function.
    Stage2 { function: String, err: Stage2Error },
    /// Module-level lifting failed for a specific module.
    ModuleLift { module: String, err: Stage2Error },
    /// Stage 3 (mut-to-let) failed.
    Stage3(crate::stage_03_mut_to_let::Stage3Error),
    /// First-class global lowering failed before stage 3.
    GlobalThreading(crate::global_threading::ThreadGlobalsError),
    /// Stage 4 (effects) failed.
    Stage4(crate::stage_04_effects::Stage4Error),
    /// Stage 5 (SSA) failed.
    Stage5(crate::stage_05_ssa::Stage5Error),
    /// Stage 6 (let-inline + DCE) failed.
    Stage6(crate::stage_06_let_inline::Stage6Error),
    /// Stage 7 (`.aborts` variant + unified control-flow
    /// extraction) failed.
    Stage7(crate::stage_07_dejumps::Stage7Error),
    /// Installing the permissive-mode fallback stub failed after the
    /// original per-function lift had already failed. Both causes are
    /// retained so the signature-lift failure cannot hide the original.
    StubLift {
        function: String,
        original: Box<DriverError>,
        stub_err: Stage2Error,
    },
    /// One of the two stage-10 bounded-nat lowering passes failed.
    Stage10 {
        pass: &'static str,
        err: crate::stage_10_bounded_nat::Stage10Error,
    },
    /// A post-SSA typed normalization walk failed. Every failed function
    /// retains its exact input body; later passes never consume a partial
    /// rewrite.
    OperandNormalization {
        phase: &'static str,
        failures: Vec<(String, String)>,
    },
    /// At least one renderer-time invariant is violated on the
    /// final IR. Strict-mode only -- in Permissive mode the
    /// violations land in
    /// [`PipelineOutput::renderer_invariant_warnings`].
    RenderInvariantViolation {
        violations: Vec<InvariantViolation>,
        report: String,
    },
}

impl std::fmt::Display for DriverError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Stage1 { function, err } => {
                write!(f, "stage 1 failed for `{function}`: {err:?}")
            }
            Self::Stage2 { function, err } => {
                write!(f, "stage 2 failed for `{function}`: {err:?}")
            }
            Self::ModuleLift { module, err } => {
                write!(f, "module lift failed for `{module}`: {err:?}")
            }
            Self::Stage3(err) => write!(f, "stage 3 failed: {err:?}"),
            Self::GlobalThreading(err) => write!(f, "global threading failed: {err:?}"),
            Self::Stage4(err) => write!(f, "stage 4 failed: {err:?}"),
            Self::Stage5(err) => write!(f, "stage 5 failed: {err:?}"),
            Self::Stage6(err) => write!(f, "stage 6 failed: {err:?}"),
            Self::Stage7(err) => write!(f, "stage 7 failed: {err:?}"),
            Self::StubLift {
                function,
                original,
                stub_err,
            } => write!(
                f,
                "fallback stub lift failed for `{function}` after `{original}`: {stub_err:?}"
            ),
            Self::Stage10 { pass, err } => write!(f, "{pass} failed: {err:?}"),
            Self::OperandNormalization { phase, failures } => write!(
                f,
                "{phase} operand normalization failed for {} function(s): {}",
                failures.len(),
                failures
                    .iter()
                    .map(|(function, error)| format!("{function}: {error}"))
                    .collect::<Vec<_>>()
                    .join("; ")
            ),
            Self::RenderInvariantViolation { violations, report } => write!(
                f,
                "render contract failed with {} invariant violation(s):\n{}",
                violations.len(),
                report.trim_end()
            ),
        }
    }
}

impl std::error::Error for DriverError {}

/// Run stages 1 + 2 over every module in `env`, producing a fully
/// assembled [`Program`].
///
/// `package_name_for_module` is called for each Move module to get
/// the IR-side package name (matches `natives::NativeFunctionModule::package`
/// for natives; for user code, the Move-package name from `Move.toml`).
pub fn run<F>(
    env: &GlobalEnv,
    targets: &FunctionTargetsHolder,
    package_targets: Option<&PackageTargets>,
    package_name_for_module: F,
) -> Result<PipelineOutput, DriverError>
where
    F: FnMut(ModuleId) -> String,
{
    run_with_mode(
        env,
        targets,
        package_targets,
        package_name_for_module,
        FailureMode::Permissive,
        None,
    )
}

/// Fire a stage hook if one is registered. Called at every
/// post-translation phase boundary so observers (e.g. `--dump-ir-stages`)
/// can snapshot the IR after each stage's mutations land.
fn fire_hook(hook: &mut Option<&mut dyn FnMut(&str, &Program)>, name: &str, program: &Program) {
    if let Some(h) = hook.as_deref_mut() {
        h(name, program);
    }
}

fn run_stage_10(program: &mut Program, pass: &'static str) -> Result<(), DriverError> {
    crate::stage_10_bounded_nat::run(program).map_err(|err| DriverError::Stage10 { pass, err })
}

fn program_function_name(program: &Program, fid: crate::ir::FunId) -> Option<String> {
    program
        .lookup_callee(fid)
        .map(|callee| callee.name().to_string())
}

fn finalize_stub_fallback(
    function: String,
    original: DriverError,
    stub_result: Result<crate::ir::FunId, Stage2Error>,
) -> Result<DriverError, DriverError> {
    match stub_result {
        Ok(_) => Ok(original),
        Err(stub_err) => Err(DriverError::StubLift {
            function,
            original: Box::new(original),
            stub_err,
        }),
    }
}

fn render_invariant_driver_error(
    program: &Program,
    violations: Vec<InvariantViolation>,
) -> DriverError {
    let report = display_table(&violations, program);
    DriverError::RenderInvariantViolation { violations, report }
}

pub fn run_with_mode<F>(
    env: &GlobalEnv,
    targets: &FunctionTargetsHolder,
    package_targets: Option<&PackageTargets>,
    package_name_for_module: F,
    mode: FailureMode,
    stage_hook: Option<&mut dyn FnMut(&str, &Program)>,
) -> Result<PipelineOutput, DriverError>
where
    F: FnMut(ModuleId) -> String,
{
    run_with_abort_payload_mode(
        env,
        targets,
        package_targets,
        package_name_for_module,
        mode,
        crate::ir::AbortPayloadMode::Proof,
        stage_hook,
    )
}

pub fn run_with_abort_payload_mode<F>(
    env: &GlobalEnv,
    targets: &FunctionTargetsHolder,
    package_targets: Option<&PackageTargets>,
    mut package_name_for_module: F,
    mode: FailureMode,
    abort_payload_mode: crate::ir::AbortPayloadMode,
    mut stage_hook: Option<&mut dyn FnMut(&str, &Program)>,
) -> Result<PipelineOutput, DriverError>
where
    F: FnMut(ModuleId) -> String,
{
    let mut prog = ProgramBuilder::new();
    let mut diagnostics = Vec::new();

    // Lift program declarations: modules, struct/enum definitions, and stubs.
    for module_env in env.get_modules() {
        let pkg = package_name_for_module(module_env.get_id());
        super::module_lift::lift_module(&module_env, &pkg, &mut prog).map_err(|err| {
            DriverError::ModuleLift {
                module: env
                    .symbol_pool()
                    .string(module_env.get_name().name())
                    .to_string(),
                err,
            }
        })?;
    }

    // The former ghost dynamic_fields_<K>_<V> augmentation
    // pre-pass was deleted in step-2 slice C: every df/dof op routes
    // through the World model -- see
    // plans/lean-pipeline/container-df-unification.md.)

    // Analyze wrapper MapKey metadata. Walk
    // every non-native function's bytecode once, finds all internal
    // calls to recognised MapKey natives (`table::borrow_mut`,
    // `dynamic_field::borrow_mut`, etc.), and records each call's
    // (K, V) -- in the callee's own type-parameter frame -- as the
    // ordered list of per-step pairs for that callee.
    // `translate_function_call` consumes the cache when a user
    // wrapper is called, instantiates each (K, V) against the
    // outer call's `type_args`, and seeds `borrow_mut_kv` for the
    // dest temp. `fill_map_key_types` then patches the
    // corresponding placeholders in the downstream WriteBack
    // chain. See `plans/lean-pipeline/native-field-collapse-loses-map-key.md`
    // Step 3.
    super::wrapper_kv::build(env, targets, &mut prog);

    // Translate function bodies. Skip native modules.
    //
    // Per-function failures are recorded as `skipped_functions` and
    // the function keeps its empty-stub body (which renders as
    // `sorry`). This lets a package with one unsupported function
    // (e.g., a `loop {}` or a borrow shape stage 2 hasn't lifted)
    // still emit the rest of its modules.
    let mut skipped: Vec<(String, DriverError)> = Vec::new();
    for module_env in env.get_modules() {
        let pkg = package_name_for_module(module_env.get_id());
        let module_name = env
            .symbol_pool()
            .string(module_env.get_name().name())
            .to_string();
        for func_env in module_env.get_functions() {
            // Natives are registered by `module_lift` as NativeDecls;
            // the per-function lift loop only walks translated bodies.
            // This covers three sources: the Move `native fun`
            // keyword, an entry in the `native_effects` table, and
            // membership in the `NATIVE_FUNCTION_MODULES` allowlist.
            let func_name = env.symbol_pool().string(func_env.get_name()).to_string();
            if super::natives::is_native_function(
                &pkg,
                &module_name,
                &func_name,
                func_env.is_native(),
            ) {
                continue;
            }
            let target = match targets.get_target_opt(&func_env, &FunctionVariant::Baseline) {
                Some(t) => t,
                None => continue,
            };
            let display_name = func_env.get_name().display(env.symbol_pool()).to_string();
            let code = target.get_bytecode().to_vec();
            let cfg = match crate::stage_01_bytecode_cfg::run(&code, &target) {
                Ok(c) => {
                    if let Some(want) = std::env::var_os("FOXY_DUMP_STAGE1") {
                        if want.is_empty() || want == std::ffi::OsStr::new(&display_name) {
                            eprintln!(
                                "=== stage1 Region: {display_name} ===\n{}",
                                crate::stage_01_bytecode_cfg::pretty_region(&c)
                            );
                        }
                    }
                    c
                }
                Err(err) => {
                    let de = DriverError::Stage1 {
                        function: display_name.clone(),
                        err,
                    };
                    match mode {
                        FailureMode::Strict => return Err(de),
                        FailureMode::Permissive => {
                            // Insert a sorry-bodied stub so callers can
                            // still resolve this FunId. If signature lifting
                            // also fails, stop here with both errors instead
                            // of letting a secondary `UnknownFunctionId`
                            // obscure the real causes downstream.
                            let stub_result =
                                super::function_lift::lift_function_stub(&target, &mut prog);
                            let de = finalize_stub_fallback(display_name.clone(), de, stub_result)?;
                            diagnostics.push(PipelineDiagnostic::error(
                                "stage_01_bytecode_cfg",
                                "function-lift-failed",
                                Some(display_name.clone()),
                                format!("{de:?}"),
                            ));
                            skipped.push((display_name, de));
                            continue;
                        }
                    }
                }
            };
            if let Err(err) = super::function_lift::lift_function(cfg, &target, &mut prog) {
                let de = DriverError::Stage2 {
                    function: display_name.clone(),
                    err,
                };
                match mode {
                    FailureMode::Strict => return Err(de),
                    FailureMode::Permissive => {
                        let stub_result =
                            super::function_lift::lift_function_stub(&target, &mut prog);
                        let de = finalize_stub_fallback(display_name.clone(), de, stub_result)?;
                        diagnostics.push(PipelineDiagnostic::error(
                            "stage_02_ir_cfg",
                            "function-lift-failed",
                            Some(display_name.clone()),
                            format!("{de:?}"),
                        ));
                        skipped.push((display_name, de));
                        continue;
                    }
                }
            }
        }
    }
    // Skipped-list printing happens at the call site (caller has the
    // human-readable context).

    // Finalize the translated Program. Register the World-backed `store_*` /
    // `set` natives now that module lifting has registered the
    // `Sui::dynamic_field` module
    // (it isn't present at the pre-pass). `route_df_to_world` (called
    // below, after build) routes every df/dof op to them. (The former
    // ghost-TypedMap rewrite that lived here was deleted in step-2
    // slice C -- see plans/lean-pipeline/container-df-unification.md.)
    super::dynamic_fields::register_store_natives(&mut prog).map_err(|err| {
        DriverError::ModuleLift {
            module: "<store-natives>".to_string(),
            err,
        }
    })?;

    // Capture the spec-wrapper -> impl `FunId` map from the Move spec
    // hierarchy before the builder is consumed; stage 12 uses it to
    // build correctness obligations.
    let prove_roster =
        prog.compute_spec_to_impl(env, package_targets, &mut package_name_for_module);
    let trusted_spec_to_impl = prog.compute_trusted_spec_to_impl(env, package_targets);
    let spec_ignore_aborts = prog.compute_spec_ignore_aborts(package_targets);
    // Derive the per-native ghost-marker seed from the Move model
    // (`#[spec(target=...)]` via `PackageTargets::get_specs`, NOT the
    // holder bimap). Requires `package_targets`; absent in unit-test
    // callers that pass `None`, where there is no ghost to thread.
    let ghost_native_seed = if let Some(pt) = package_targets {
        prog.derive_native_ghost_seed(env, pt, &mut package_name_for_module)
            .map_err(|err| DriverError::ModuleLift {
                module: "<ghost-native-seed>".to_string(),
                err,
            })?
    } else {
        std::collections::BTreeMap::new()
    };
    let (mut program, prover_fn_ids) = prog.build_with_prover_ids();
    program.spec_to_impl = prove_roster.spec_to_impl;
    program.targetless_prove_specs = prove_roster.targetless;
    program.prove_spec_names = prove_roster.names;
    program.unmapped_prove_specs = prove_roster.unmapped;
    program.trusted_spec_to_impl = trusted_spec_to_impl;
    program.spec_ignore_aborts = spec_ignore_aborts;
    program.ghost_native_seed = ghost_native_seed;
    // 3-dim Effects classification. Pointwise meet across
    // (aborts, det, mutation); pre-seeded from
    // `program.natives.decls[fid].effects`.
    super::effects::classify_effects(&mut program);
    fire_hook(&mut stage_hook, "stage_02_post_translation", &program);

    // C frontends may attach first-class global nodes to the assembled IR.
    // Lower them to ordinary hidden parameters before stage 3 consumes
    // mutable references. Move-built programs have an empty global table and
    // this pass is an exact no-op.
    crate::global_threading::thread_globals(&mut program).map_err(DriverError::GlobalThreading)?;

    // Lower mutable references: shift in-body WriteRef/WriteBack
    // into Stmt::Let value positions so bodies are value-form.
    crate::stage_03_mut_to_let::run(&mut program).map_err(DriverError::Stage3)?;
    fire_hook(&mut stage_hook, "stage_03_mut_to_let", &program);

    // Canonicalize dynamic-field calls and pre-SSA auto-derefs.
    // Route dynamic fields to the World `store_*` natives after mut-to-let:
    // `add`/`borrow_mut` take `&mut self.id` and write back, so only here
    // are they flattened to plain Calls / `borrowMapKey` (not Mutation-
    // wrapped during body lifting). Runs before effects threading so the resulting
    // GlobalMut `store_*` calls get `world` threaded.
    super::dynamic_field_rewrite::route_df_to_world(&mut program);

    // Stage 3/dynamic-field routing can leave bytecode-level auto-deref
    // comparisons in the IR, such as `&Ownership == Ownership` in spec
    // postconditions. Normalize those before stage 4's precondition gate.
    // `Early` mode: pre-SSA a single Move local can carry MULTIPLE
    // `Stmt::Let` defs of differing ref-ness (an outer `&T` borrow plus
    // an arm-local `T` value that escapes its block -- the pre-SSA
    // shape). Wrapping such a var's use from its enclosing-scope type
    // would contradict the other def; after SSA merges them into a
    // mixed-type phi that leaves a `ReadRef` over a value and stage 7
    // panics. Early therefore declines multi-def operands and leaves
    // them to the post-SSA `Full` call below.
    operand_normalization::run(&mut program, NormalizeMode::Early)
        .map_err(|failures| normalization_driver_error("pre-SSA", &program, failures))?;

    debug_assert_precondition(Stage::S04Effects, &program);

    // Thread runtime World effects through
    // every GlobalMut function so observable side effects (events,
    // transfers, deletes, receives) become explicit in the IR.
    // Re-classifies effects internally so mutref-only-GlobalMut
    // functions that became LocalMut after stage 3 are correctly
    // demoted.
    crate::stage_04_effects::run(&mut program).map_err(DriverError::Stage4)?;
    fire_hook(&mut stage_hook, "stage_04_effects", &program);

    // Thread per-function spec-only
    // ghost variables (`program.ghost_vars`) and lower the ghost ops
    // (`global` read / `set`/`*borrow_mut()=` write / `declare_global_mut`)
    // onto them. Independent of world/effects; its own stage. Runs after
    // stage 4 (ghost slots append after the `world` slot) and before SSA
    // (so the op-lowering rebinds get versioned -- a post-write `global`
    // read resolves to the written value). See
    // `plans/lean-pipeline/ghost-support.md`.
    crate::stage_04_ghost::run(&mut program);
    fire_hook(&mut stage_hook, "stage_04_ghost", &program);
    debug_assert_precondition(Stage::S05Ssa, &program);

    // Construct SSA: alpha-rename every binding fresh,
    // introduce explicit phi via Tuple-Let at If/Match merges, thread
    // `loop_state` tuples through every While. Stage 5's design says
    // it's required by stages 6/7 -- stage 6's single-use inliner
    // relies on "one Let per VarId" for use-count accuracy, and
    // stage 7's loop-extract walks `iter_locals`.
    //
    crate::stage_05_ssa::run(&mut program).map_err(DriverError::Stage5)?;
    fire_hook(&mut stage_hook, "stage_05_ssa", &program);

    // Complete writeback chains (S4b of
    // plans/lean-pipeline/writeback-lowering.md). Post-SSA (fresh
    // __wbc binders preserve uniqueness), before the writeback
    // lowering below and before stage 7 (the loop tail IS the
    // threading; completing it here lets extraction carry the
    // updated roots automatically).
    crate::stage_05_chain_complete::run(&mut program);
    fire_hook(&mut stage_hook, "stage_05_chain_complete", &program);

    // Lower in-stage WriteBack nodes
    // (plans/lean-pipeline/writeback-lowering.md). After stage 4 so
    // world threading is final, and AFTER stage 5 so cloned step
    // operands (vec indices / map keys) are position-independent --
    // pre-SSA the loop counter is a REBOUND name, and a clone of
    // `Var(i)` placed at the writeback position would resolve to the
    // post-increment version (momentum update_reward_infos wrote
    // slot i+1). SSA's single-assignment names make the borrow-site
    // operand expression valid at any later position.
    crate::stage_04_writeback::run(&mut program);
    fire_hook(&mut stage_hook, "stage_04_writeback", &program);

    // Repair post-SSA reference operands on aborting UInt arithmetic before
    // bounded lowering. Stage 7 must see those lowered calls to derive their
    // `.aborts` conditions. Total operations stay in their existing
    // auto-deref-compatible shape until final normalization; the following
    // precondition still rejects incompatible operand value types.
    operand_normalization::run(&mut program, NormalizeMode::Aborting)
        .map_err(|failures| normalization_driver_error("post-SSA", &program, failures))?;
    debug_assert_precondition(Stage::S10BoundedNat, &program);

    // Lower bounded-nat operations. Runs before dejumping
    // so the new `Call`s into `BoundedU{N}_<op>` natives are visible
    // when stage 7 derives `.aborts` companions -- the aborts
    // companions for arithmetic / shift / narrowing-cast ops are
    // registered with `FunctionKind::Spec(Aborts)` so stage 7's
    // existing `aborts_map` picks them up automatically; bitwise and
    // comparison ops carry `AbortBit::Total` on their NativeDecl
    // and contribute `Bool(false)` through the effects-based abort
    // walker.
    run_stage_10(&mut program, STAGE_10_PRE_STAGE_7)?;
    fire_hook(&mut stage_hook, STAGE_10_PRE_STAGE_7, &program);
    debug_assert_precondition(Stage::S07Dejumps, &program);

    // Extract abort/spec/control-flow companions. Runs
    // BEFORE stage 6 so spec calls get pulled into companions while
    // they're still observable in the source bodies -- stage 6's
    // DCE classifies `prover::requires`/`ensures` as `PureTotal` and
    // would drop the `Stmt::Eval(Prover.ensures p)` sites otherwise.
    //
    // Stage 7 (`stage_07_dejumps`): materialise a sibling `.aborts`
    // companion per source function returning `Option<MoveAbortCode>`,
    // then run unified control-flow extraction (loops +
    // break/continue/return) over both variants. This is the sole
    // stage-7 implementation; the former Bool-predicate abort
    // derivation was retired.
    crate::stage_07_dejumps::run_with_payload_mode(
        &mut program,
        &prover_fn_ids,
        abort_payload_mode,
    )
    .map_err(DriverError::Stage7)?;
    fire_hook(&mut stage_hook, "stage_07_dejumps", &program);

    // Dejumping synthesizes packed loop-state values after the early
    // auto-dereference pass. Normalize those values (including references
    // nested in tuple fields) before enforcing stage 6's Pack invariant.
    operand_normalization::run(&mut program, NormalizeMode::PackedValues)
        .map_err(|failures| normalization_driver_error("post-dejump packs", &program, failures))?;

    // Dejumping also synthesizes continuation parameters and bodies.  That
    // can expose fresh UInt operations (and can remove a stale implicit
    // ReadRef as above), so re-establish stage 10 before stage 6's combined
    // precondition checks its bounded-arithmetic postcondition.
    run_stage_10(&mut program, "stage_10_bounded_nat_post_dejump")?;

    debug_assert_precondition(Stage::S06LetInline, &program);

    // Inline lets and eliminate dead code. After dejumping, source
    // bodies have no spec calls left and stage 6 is free to drop /
    // inline pure-total bindings. Companion bodies (`.aborts`,
    // `.requires`, `.ensures`) also get cleaned up by the same pass.
    crate::stage_06_let_inline::run(&mut program).map_err(DriverError::Stage6)?;
    fire_hook(&mut stage_hook, "stage_06_let_inline", &program);
    debug_assert_precondition(Stage::S08Loops, &program);

    // Recompute final loop-helper World-write effects. Stage 7 has
    // established the final recursive call graph; loop termination itself is
    // rendered with `partial_fixpoint`.
    crate::stage_08_loops::run(&mut program);
    fire_hook(&mut stage_hook, "stage_08_loops", &program);

    // Finish Move's implicit auto-dereference normalization after cleanup,
    // preserving the established Lean expression shape for total comparisons
    // and value-typed Pack fields. Stage 7 and the active stage 8 do not create
    // UInt operations, so the old post-stage-7 bounded pass was redundant; one
    // final idempotent pass lowers everything exposed by this normalization.
    operand_normalization::run(&mut program, NormalizeMode::Full)
        .map_err(|failures| normalization_driver_error("post-cleanup", &program, failures))?;
    run_stage_10(&mut program, STAGE_10_FINAL)?;
    fire_hook(&mut stage_hook, STAGE_10_FINAL, &program);

    // Synthesize proof obligations. Stage 12 creates the per-prove-target
    // `FunctionKind::Theorem` correctness obligations -- now that every
    // companion is in its final signature shape. It only references the
    // `.asserts` companion (built earlier, in stage 7 spec_companion);
    // it does not build it. Purely additive; runs before the render-time
    // invariant gate so the new functions are checked too.
    crate::stage_12_obligations::run(&mut program);
    fire_hook(&mut stage_hook, "stage_12_obligations", &program);

    // Enforce the render contract.
    // Runs every invariant whose `held_through` includes
    // `Stage::Render` -- baseline well-formedness, every stage's
    // surviving postconditions, and cross-stage invariants.
    //
    // Strict mode aborts on any violation. Permissive mode collects
    // them into `PipelineOutput::renderer_invariant_warnings`.
    let renderer_invariant_warnings: Vec<InvariantViolation> =
        match verify_at(Stage::Render, &program) {
            Ok(()) => Vec::new(),
            Err(violations) => match mode {
                FailureMode::Strict => {
                    return Err(render_invariant_driver_error(&program, violations));
                }
                FailureMode::Permissive => {
                    for v in &violations {
                        let header_fn = v
                            .function
                            .and_then(|fid| program_function_name(&program, fid));
                        // Also try to extract a fid embedded in the detail string
                        // (some invariants encode the offending function inside
                        // the detail rather than in InvariantViolation::function).
                        // Pattern matches `function: <N>` and `callee <N>`.
                        let mut extra = String::new();
                        for needle in &["function: ", "callee: ", "callee "] {
                            let mut s = v.detail.as_str();
                            while let Some(i) = s.find(needle) {
                                let after = &s[i + needle.len()..];
                                let end = after
                                    .find(|c: char| !c.is_ascii_digit())
                                    .unwrap_or(after.len());
                                if end == 0 {
                                    break;
                                }
                                if let Ok(fid) = after[..end].parse::<crate::ir::FunId>() {
                                    if let Some(name) = program_function_name(&program, fid) {
                                        extra.push_str(&format!(" [{}={}]", fid, name));
                                    }
                                }
                                s = &after[end..];
                            }
                        }
                        eprintln!(
                            "new-pipeline: render-time invariant {} violation [{}{}]: {}{}",
                            v.invariant,
                            v.function
                                .map(|fid| format!("fid={}", fid))
                                .unwrap_or_default(),
                            header_fn
                                .as_ref()
                                .map(|n| format!(" fn={}", n))
                                .unwrap_or_default(),
                            v.detail,
                            extra,
                        );
                        diagnostics.push(PipelineDiagnostic::error(
                            "render",
                            "invariant-violation",
                            header_fn,
                            format!("{}: {}{}", v.invariant, v.detail, extra),
                        ));
                    }
                    // A render-time violation says the IR is not fit to
                    // render, so consuming it anyway emits Lean the
                    // generator has already judged wrong. Permissive mode
                    // used to do exactly that: report every violation as an
                    // ERROR and then hand the same IR to the renderer.
                    // `mmt_v3::tick::update` shipped an `if` whose arms were
                    // `&mut TickInfo` and `AbortResult<AbortCode>` that way --
                    // reported, written out, and only discovered when an
                    // unrelated change widened the set of modules the
                    // native-model classification actually compiles.
                    //
                    // Permissive still governs PER-FUNCTION translation
                    // failures (`skipped`): dropping one function keeps the
                    // rest of a corpus usable. A render-invariant violation
                    // is not per-function in that sense -- it is a statement
                    // that the program about to be rendered is malformed.
                    return Err(render_invariant_driver_error(&program, violations));
                }
            },
        };

    Ok(PipelineOutput {
        program,
        diagnostics,
        skipped,
        renderer_invariant_warnings,
    })
}

fn normalization_driver_error(
    phase: &'static str,
    program: &Program,
    failures: Vec<(crate::ir::FunId, crate::ir::analysis::type_of::TypeOfError)>,
) -> DriverError {
    DriverError::OperandNormalization {
        phase,
        failures: failures
            .into_iter()
            .map(|(fid, error)| {
                let function = program
                    .functions
                    .get(&fid)
                    .map(|function| format!("{} (fid={fid})", function.name))
                    .unwrap_or_else(|| format!("fid={fid}"));
                (function, format!("{error:?}"))
            })
            .collect(),
    }
}

/// Debug-build precondition check between stages.
///
/// Walks every invariant in the registry that should already hold at
/// `next_stage`'s input. Reports violations via the pretty-print
/// helper for easy triage; panics in debug builds to halt the
/// pipeline at the corruption point.
///
/// In release builds this is a no-op.
fn debug_assert_precondition(next_stage: Stage, program: &Program) {
    #[cfg(debug_assertions)]
    {
        if let Err(mut violations) = crate::ir::invariants::verify_precondition(next_stage, program)
        {
            // Full scope validation is intentionally too strong before
            // SSA. Stage 2 can emit branch-local assignment merges that
            // stage 5 later rewrites into explicit phi `let`s; see the
            // pre-SSA branch-merge discussion above. Keep all other checks
            // active in debug builds.
            if matches!(next_stage, Stage::S04Effects | Stage::S05Ssa) {
                violations.retain(|v| v.invariant != "baseline-well-formedness");
            }
            if violations.is_empty() {
                return;
            }
            let table = crate::ir::invariants::display_table(&violations, program);
            debug_assert!(
                false,
                "precondition for {:?} failed ({} violation{}):\n{}",
                next_stage,
                violations.len(),
                if violations.len() == 1 { "" } else { "s" },
                table,
            );
        }
    }
    let _ = (next_stage, program);
}

#[cfg(test)]
mod tests {
    use super::super::operand_normalization::test_support::{let1, multi_def_cascade_program};
    use super::*;
    use crate::ir::{
        BinOp, Block, BlockTail, Effects, Expr, Function, FunctionKind, Module, Param, Program,
        Signature, SpecKind, Type, VarId,
    };

    #[test]
    fn pipeline_completes_no_readref_over_value_survives() {
        // Early -> SSA -> Full -> stage 7. Before the fix, Early wrapped
        // the multi-def var and its arithmetic descendants; SSA produced
        // `ReadRef(value)`, and stage 7's scope build panicked. With the
        // fix the run completes and no `ReadRef` sits over a value type.
        let mut program = multi_def_cascade_program();
        operand_normalization::run(&mut program, NormalizeMode::Early).unwrap();
        crate::stage_05_ssa::run(&mut program).expect("stage 5 (SSA) runs");
        // No malformed ReadRef right after SSA (the exact regression).
        assert!(
            crate::stage_05_ssa::postcondition::readref_over_value_findings(&program).is_empty(),
            "no ReadRef-over-value must survive SSA",
        );
        operand_normalization::run(&mut program, NormalizeMode::Full).unwrap();
        crate::stage_07_dejumps::run(&mut program, &crate::ir::ProverFnIds::default())
            .expect("stage 7 completes without a scope-build panic");
        assert!(
            crate::stage_05_ssa::postcondition::readref_over_value_findings(&program).is_empty(),
            "no ReadRef-over-value must survive the pipeline",
        );
    }

    #[test]
    fn bounded_nat_postcondition_survives_active_late_stages_and_render_gate() {
        let mut program = Program::default();
        program.modules.insert(
            0,
            Module {
                name: "m".to_string(),
                package_name: "p".to_string(),
                address: String::new(),
                required_imports: vec![],
                is_native: false,
            },
        );
        program.functions.insert(
            0,
            Function {
                module: 0,
                name: "f".to_string(),
                signature: Signature {
                    type_params: vec![],
                    params: vec![
                        Param {
                            name: "r".to_string(),
                            var: VarId::from("r"),
                            ty: Type::Reference(Box::new(Type::UInt(64))),
                        },
                        Param {
                            name: "x".to_string(),
                            var: VarId::from("x"),
                            ty: Type::UInt(64),
                        },
                    ],
                    return_type: Type::UInt(64),
                },
                body: Block {
                    stmts: vec![let1(
                        "result",
                        Expr::BinOp {
                            op: BinOp::Sub,
                            lhs: Box::new(Expr::Var(VarId::from("r"))),
                            rhs: Box::new(Expr::Var(VarId::from("x"))),
                        },
                    )],
                    tail: BlockTail::Value(Expr::Var(VarId::from("result"))),
                },
                kind: FunctionKind::Source,
                effects: Effects::CONSERVATIVE,
                explicit_pure: false,
            },
        );

        operand_normalization::run(&mut program, NormalizeMode::Aborting).unwrap();
        crate::stage_10_bounded_nat::run(&mut program).unwrap();
        crate::stage_10_bounded_nat::postcondition::check(&program).unwrap();

        crate::stage_07_dejumps::run(&mut program, &crate::ir::ProverFnIds::default()).unwrap();
        crate::stage_10_bounded_nat::postcondition::check(&program).unwrap();

        let aborts_fid = program
            .functions
            .iter()
            .find_map(|(fid, function)| match function.kind {
                FunctionKind::Spec {
                    kind: SpecKind::Aborts,
                    target: 0,
                } => Some(*fid),
                _ => None,
            })
            .expect("f.aborts emitted");
        let bounded_sub_aborts = program
            .natives
            .decls
            .iter()
            .find_map(|(fid, decl)| (decl.name == "BoundedU64_sub_aborts").then_some(*fid))
            .expect("bounded subtraction abort companion registered");

        struct CallFinder {
            target: crate::ir::FunId,
            found: bool,
        }
        impl crate::ir::visit::Visitor for CallFinder {
            fn visit_expr(&mut self, expr: &Expr) {
                if matches!(expr, Expr::Call { fun, .. } if *fun == self.target) {
                    self.found = true;
                }
                crate::ir::visit::walk_expr_default(self, expr);
            }
        }
        let mut finder = CallFinder {
            target: bounded_sub_aborts,
            found: false,
        };
        crate::ir::visit::Visitor::visit_block(&mut finder, &program.functions[&aborts_fid].body);
        assert!(
            finder.found,
            "normalization must precede stage 7 so f.aborts observes subtraction"
        );

        crate::stage_06_let_inline::run(&mut program).unwrap();
        crate::stage_10_bounded_nat::postcondition::check(&program).unwrap();
        crate::stage_08_loops::run(&mut program);
        crate::stage_10_bounded_nat::postcondition::check(&program).unwrap();
        operand_normalization::run(&mut program, NormalizeMode::Full).unwrap();
        crate::stage_10_bounded_nat::run(&mut program).unwrap();
        crate::stage_12_obligations::run(&mut program);
        crate::stage_10_bounded_nat::postcondition::check(&program).unwrap();
        crate::ir::invariants::verify_at(Stage::Render, &program).unwrap();
    }

    #[test]
    fn strict_render_error_display_includes_grouped_violation_details() {
        let program = multi_def_cascade_program();
        let error = render_invariant_driver_error(
            &program,
            vec![InvariantViolation::new(
                "test-render-contract",
                Some(0),
                "offending expression",
            )],
        );
        let message = error.to_string();
        assert!(message.contains("1 invariant violation(s)"));
        assert!(message.contains("[test-render-contract]"));
        assert!(message.contains("f (fid 0): offending expression"));
    }

    #[test]
    fn stub_lift_failure_is_fail_closed_and_retains_both_causes() {
        let original = DriverError::Stage2 {
            function: "f".to_string(),
            err: Stage2Error::NotImplemented {
                reason: "original-body-lift",
            },
        };
        let error = finalize_stub_fallback(
            "f".to_string(),
            original,
            Err(Stage2Error::NotImplemented {
                reason: "fallback-signature-lift",
            }),
        )
        .unwrap_err();
        assert!(matches!(&error, DriverError::StubLift { .. }));
        let message = error.to_string();
        assert!(message.contains("original-body-lift"));
        assert!(message.contains("fallback-signature-lift"));
    }

    #[test]
    fn stage_10_driver_error_identifies_each_pipeline_boundary() {
        for pass in [STAGE_10_PRE_STAGE_7, STAGE_10_FINAL] {
            let error = DriverError::Stage10 {
                pass,
                err: crate::stage_10_bounded_nat::Stage10Error::Postcondition(
                    "raw UInt BinOp survived".to_string(),
                ),
            };
            let message = error.to_string();
            assert!(message.starts_with(pass));
            assert!(message.contains("raw UInt BinOp survived"));
        }
    }

    #[test]
    fn stage_hook_names_and_order_are_stable() {
        let env = GlobalEnv::new();
        let package_targets = PackageTargets::new(
            &env,
            move_stackless_bytecode::target_filter::TargetFilterOptions::default(),
            false,
            None,
        );
        let targets = FunctionTargetsHolder::new(
            move_stackless_bytecode::options::ProverOptions::default(),
            &package_targets,
            move_stackless_bytecode::function_target_pipeline::FunctionHolderTarget::All,
        );
        let mut stages = Vec::new();
        let mut hook = |stage: &str, _: &Program| stages.push(stage.to_string());

        run_with_mode(
            &env,
            &targets,
            None,
            |_| "test".to_string(),
            FailureMode::Strict,
            Some(&mut hook),
        )
        .unwrap();

        assert_eq!(
            stages,
            [
                "stage_02_post_translation",
                "stage_03_mut_to_let",
                "stage_04_effects",
                "stage_04_ghost",
                "stage_05_ssa",
                "stage_05_chain_complete",
                "stage_04_writeback",
                "stage_10_bounded_nat_pre_stage7",
                "stage_07_dejumps",
                "stage_06_let_inline",
                "stage_08_loops",
                "stage_10_bounded_nat_final",
                "stage_12_obligations",
            ]
        );
    }
}
