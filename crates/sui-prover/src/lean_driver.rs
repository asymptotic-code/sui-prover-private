// Lean backend driver: runs the move-stackless analysis pipeline with the
// Lean-specific processor overrides, then hands the resulting
// `FunctionTargetsHolder` to `move_prover_lean_backend` to render Lean 4 and
// (unless `generate_only`) invoke `lake build`. This mirrors the standalone
// `sui-lean` tool's spec path, integrated behind `--backend lean`.

use move_model::model::GlobalEnv;
use move_model::ty::Type as MoveType;
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
fn build_lean_pipeline(
    options: &ProverOptions,
    include_all: bool,
    keep_functions: std::collections::BTreeSet<
        move_model::model::QualifiedId<move_model::model::FunId>,
    >,
) -> FunctionTargetPipeline {
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
        LeanVerificationAnalysisProcessor::new(include_all, keep_functions),
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

fn world_mode_keep_functions(
    model: &GlobalEnv,
) -> std::collections::BTreeSet<
    move_model::model::QualifiedId<move_model::model::FunId>,
> {
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
    include_all: bool,
) -> FunctionTargetsHolder {
    let mut targets = FunctionTargetsHolder::new(prover_options.clone(), package_targets, target);

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

    let pipeline = build_lean_pipeline(
        prover_options,
        include_all,
        world_mode_keep_functions(model),
    );
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

/// Find the ghost marker/value pairs used by native specs, gated to markers
/// declared by the target package so unrelated framework specs stay inert.
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
                    let pair = (type_inst[0].clone(), type_inst[1].clone());
                    if !pairs.contains(&pair) {
                        pairs.push(pair);
                    }
                }
            }
        }
        pairs
    };

    let mut declared = Vec::new();
    for spec_qid in package_targets.target_specs() {
        for pair in collect(*spec_qid, &all_ops) {
            if !declared.contains(&pair) {
                declared.push(pair);
            }
        }
    }
    if declared.is_empty() {
        return Vec::new();
    }

    let mut seed = Vec::new();
    for module_env in env.get_modules() {
        for func_env in module_env.get_functions() {
            if !func_env.is_native() {
                continue;
            }
            let native_qid = func_env.get_qualified_id();
            let specs = package_targets.get_specs(&native_qid).unwrap_or_default();
            let chosen = specs
                .iter()
                .find(|spec| package_targets.target_specs().contains(*spec))
                .or_else(|| specs.iter().next())
                .copied();
            let Some(chosen) = chosen else { continue };
            let markers: Vec<_> = collect(chosen, &rw_ops)
                .into_iter()
                .filter(|pair| declared.contains(pair))
                .collect();
            if !markers.is_empty() {
                seed.push((native_qid, markers));
            }
        }
    }
    seed
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

    let boogie_proven_names: std::collections::HashSet<String> = package_targets
        .boogie_proven_specs()
        .iter()
        .map(|qid| model.get_function(*qid).get_name_str())
        .collect();

    init_global_number_state(&model, &prover_options);
    let spec_modules: Vec<_> = package_targets.target_modules().into_iter().collect();
    let targets = if spec_modules.is_empty() {
        create_and_process_targets(
            &model,
            package_targets,
            &prover_options,
            FunctionHolderTarget::All,
            include_all,
        )
    } else {
        // Keep each module's spec-to-target map one-to-one, then merge the
        // processed holders for a single combined Lean project.
        let mut merged: Option<FunctionTargetsHolder> = None;
        for module_id in spec_modules {
            let targets = create_and_process_targets(
                &model,
                package_targets,
                &prover_options,
                FunctionHolderTarget::Module(module_id),
                include_all,
            );
            match merged.as_mut() {
                Some(accumulator) => accumulator.merge_targets_from(targets),
                None => merged = Some(targets),
            }
        }
        merged.expect("non-empty spec module set produced a target holder")
    };

    move_prover_lean_backend::run_backend_with_boogie_proven(
        &model,
        &targets,
        &output_dir,
        &package_dir,
        generate_only,
        &boogie_proven_names,
        derive_ghost_native_seed(&model, package_targets),
    )
    .await
}
