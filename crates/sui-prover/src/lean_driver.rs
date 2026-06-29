// Lean backend driver: runs the move-stackless analysis pipeline with the
// Lean-specific processor overrides, then hands the resulting
// `FunctionTargetsHolder` to `move_prover_lean_backend` to render Lean 4 and
// (unless `generate_only`) invoke `lake build`. This mirrors the standalone
// `sui-lean` tool's spec path, integrated behind `--backend lean`.

use move_model::model::GlobalEnv;
use move_stackless_bytecode::function_target_pipeline::{
    FunctionHolderTarget, FunctionTargetPipeline, FunctionTargetsHolder,
};
use move_stackless_bytecode::number_operation::GlobalNumberOperationState;
use move_stackless_bytecode::options::ProverOptions;
use move_stackless_bytecode::package_targets::PackageTargets;

use crate::lean_pipeline_overrides::{
    LeanSpecInstrumentationProcessor, LeanVerificationAnalysisProcessor,
};

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

/// The Lean analysis pipeline: the shared upstream passes with
/// `ConditionalMergeInsertionProcessor` removed (our structure discovery
/// handles merge points uniformly) and two Lean wrappers — one that keeps
/// `#[spec_only(loop_inv)]` predicates and one that restores bodies the
/// upstream spec-instrumentation would clear. See `lean_pipeline_overrides`.
fn build_lean_pipeline(options: &ProverOptions, include_all: bool) -> FunctionTargetPipeline {
    use move_stackless_bytecode::{
        borrow_analysis::BorrowAnalysisProcessor, clean_and_optimize::CleanAndOptimizeProcessor,
        debug_instrumentation::DebugInstrumenter,
        deterministic_analysis::DeterministicAnalysisProcessor,
        dynamic_field_analysis::DynamicFieldAnalysisProcessor,
        eliminate_imm_refs::EliminateImmRefsProcessor, livevar_analysis::LiveVarAnalysisProcessor,
        memory_instrumentation::MemoryInstrumentationProcessor,
        mono_analysis::MonoAnalysisProcessor, move_loop_invariants::MoveLoopInvariantsProcessor,
        mut_ref_instrumentation::MutRefInstrumenter, no_abort_analysis::NoAbortAnalysisProcessor,
        number_operation_analysis::NumberOperationProcessor,
        pure_callee_detection::PureCalleeDetectionProcessor,
        quantifier_iterator_analysis::QuantifierIteratorAnalysisProcessor,
        reaching_def_analysis::ReachingDefProcessor,
        replacement_analysis::ReplacementAnalysisProcessor,
        spec_global_variable_analysis::SpecGlobalVariableAnalysisProcessor,
        spec_purity_analysis::SpecPurityAnalysis, usage_analysis::UsageProcessor,
        well_formed_instrumentation::WellFormedInstrumentationProcessor,
    };

    let mut processors: Vec<
        Box<dyn move_stackless_bytecode::function_target_pipeline::FunctionTargetProcessor>,
    > = vec![
        LeanVerificationAnalysisProcessor::new(include_all),
        SpecGlobalVariableAnalysisProcessor::new(),
        SpecPurityAnalysis::new(),
        DebugInstrumenter::new(),
        EliminateImmRefsProcessor::new(),
        MutRefInstrumenter::new(),
        NoAbortAnalysisProcessor::new(),
        DeterministicAnalysisProcessor::new(),
        PureCalleeDetectionProcessor::new(),
        DynamicFieldAnalysisProcessor::new(),
        MoveLoopInvariantsProcessor::new(),
        ReachingDefProcessor::new(),
        LiveVarAnalysisProcessor::new(),
        BorrowAnalysisProcessor::new_borrow_natives(options.borrow_natives.clone()),
        MemoryInstrumentationProcessor::new(),
        // ConditionalMergeInsertionProcessor deliberately omitted.
        CleanAndOptimizeProcessor::new(),
        UsageProcessor::new(),
        QuantifierIteratorAnalysisProcessor::new(),
        ReplacementAnalysisProcessor::new(),
        LeanSpecInstrumentationProcessor::new(),
        WellFormedInstrumentationProcessor::new(),
        MonoAnalysisProcessor::new(),
    ];

    if !options.for_interpretation {
        processors.push(NumberOperationProcessor::new());
    }

    let mut res = FunctionTargetPipeline::default();
    for p in processors {
        res.add_processor(p);
    }
    res
}

fn create_and_process_targets(
    model: &GlobalEnv,
    package_targets: &PackageTargets,
    prover_options: &ProverOptions,
    target: FunctionHolderTarget,
    include_all: bool,
) -> FunctionTargetsHolder {
    let mut targets =
        FunctionTargetsHolder::new(prover_options.clone(), package_targets, target);

    // Add every function in every module, then let the pipeline's prune keep
    // only what the verification roots reach.
    for module in model.get_modules() {
        for func_env in module.get_functions() {
            targets.add_target(&func_env);
        }
    }

    // Drain add_target diagnostics so the pipeline still runs to completion.
    if model.has_errors() {
        use codespan_reporting::diagnostic::Severity;
        use termcolor::{ColorChoice, StandardStream};
        let mut writer = StandardStream::stderr(ColorChoice::Auto);
        model.report_diag(&mut writer, Severity::Error);
    }

    let pipeline = build_lean_pipeline(prover_options, include_all);
    let _ = pipeline.run_with_hook(
        model,
        &mut targets,
        |_| {},
        |_step, _processor, _holders| {
            if model.has_errors() {
                use codespan_reporting::diagnostic::Severity;
                use termcolor::{ColorChoice, StandardStream};
                let mut writer = StandardStream::stderr(ColorChoice::Auto);
                model.report_diag(&mut writer, Severity::Error);
            }
        },
    );

    targets
}

/// Run the Lean backend over the whole package (one combined Lean project).
/// `include_all` keeps every function (skips the reachability prune);
/// `generate_only` emits Lean without invoking `lake build`.
pub async fn execute_backend_lean(
    model: GlobalEnv,
    package_targets: &PackageTargets,
    include_all: bool,
    generate_only: bool,
) -> anyhow::Result<()> {
    let prover_options = ProverOptions {
        skip_loop_analysis: true,
        ..ProverOptions::default()
    };

    // After build_model(), cwd is the package root.
    let package_dir = std::env::current_dir()?;
    let output_dir = package_dir.join("output");

    init_global_number_state(&model, &prover_options);
    let targets = create_and_process_targets(
        &model,
        package_targets,
        &prover_options,
        FunctionHolderTarget::All,
        include_all,
    );

    move_prover_lean_backend::run_backend(
        &model,
        &targets,
        &output_dir,
        &package_dir,
        generate_only,
    )
    .await
}
