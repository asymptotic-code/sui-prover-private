//! Lean-backend variants of upstream pipeline processors.
//!
//! Lean code-gen emits a body for every function in the holder, so any
//! upstream pass that drops a function or empties its bytecode breaks
//! it. The fix shape is always: wrap the responsible pass here. Never
//! re-add via `add_target` — that emits raw `StacklessBytecodeGenerator`
//! output and bypasses every later pass (notably
//! `QuantifierIteratorAnalysisProcessor`, which folds `begin_*_lambda` /
//! `end_*_lambda` chains into `Operation::Quantifier`).
//!
//! - [`LeanVerificationAnalysisProcessor`]: by default delegates to
//!   upstream's `finalize()` (prunes non-verified/inlined/essential/
//!   reachable). `include_all` skips the prune. `test_filter` (test
//!   path only) leaves non-matching `#[test]`s unmarked so the prune
//!   drops them.
//! - [`LeanSpecInstrumentationProcessor`]: restores `data.code` if
//!   upstream's non-verified branch emptied it (upstream zeros it to
//!   skip Boogie work; Lean still needs the body).
//! - [`LeanDeterministicAnalysisProcessor`]: preserves upstream's
//!   transitive analysis while classifying `#[ext(world)]` natives as
//!   deterministic world readers.
use move_compiler::shared::known_attributes::AttributeKind_;
use move_model::model::{FunId, FunctionEnv, GlobalEnv, QualifiedId};
use move_stackless_bytecode::{
    deterministic_analysis::DeterministicInfo,
    function_target::FunctionData,
    function_target_pipeline::{FunctionTargetProcessor, FunctionTargetsHolder, FunctionVariant},
    no_abort_analysis::{NoAbortAnalysisProcessor, NoAbortInfo},
    spec_global_variable_analysis::{SpecGlobalVariableAnalysisProcessor, SpecGlobalVariableInfo},
    spec_instrumentation::SpecInstrumentationProcessor,
    stackless_bytecode::{Bytecode, Operation},
    verification_analysis::{VerificationAnalysisProcessor, VerificationInfo},
};
use regex::Regex;
use std::collections::{BTreeMap, BTreeSet};

/// Lean's target closure can contain a call edge which the upstream call-graph
/// sorter deliberately omits (most notably an implementation-to-spec
/// substitution).  `SpecGlobalVariableAnalysisProcessor` nevertheless follows
/// that substituted edge and assumes the callee summary is already present.
/// Seed the lattice bottom for every baseline target before delegating to the
/// upstream SCC/fixed-point processor.  Existing summaries (including global
/// declarations attached to spec functions) are never overwritten.
pub struct LeanSpecGlobalVariableAnalysisProcessor {
    inner: Box<SpecGlobalVariableAnalysisProcessor>,
}

impl LeanSpecGlobalVariableAnalysisProcessor {
    pub fn new() -> Box<Self> {
        Box::new(Self {
            inner: SpecGlobalVariableAnalysisProcessor::new(),
        })
    }
}

impl FunctionTargetProcessor for LeanSpecGlobalVariableAnalysisProcessor {
    fn initialize(&self, env: &GlobalEnv, targets: &mut FunctionTargetsHolder) {
        // Record authoritative declarations for mapped spec functions first;
        // lattice-bottom summaries are only for targets the upstream
        // initializer did not cover.
        self.inner.initialize(env, targets);

        let fids = targets.get_funs().collect::<Vec<_>>();
        for fid in fids {
            let Some(data) = targets.get_data_mut(&fid, &FunctionVariant::Baseline) else {
                continue;
            };
            if !data.annotations.has::<SpecGlobalVariableInfo>() {
                data.annotations.set(
                    SpecGlobalVariableInfo::info_union(std::iter::empty()),
                    false,
                );
            }
        }
    }

    fn process_and_maybe_remove(
        &self,
        targets: &mut FunctionTargetsHolder,
        func_env: &FunctionEnv,
        data: FunctionData,
        scc_opt: Option<&[FunctionEnv]>,
    ) -> Option<FunctionData> {
        let env = func_env.module_env.env;
        let has_declaration = data.code.iter().any(|bc| {
            matches!(
                bc,
                Bytecode::Call(_, _, Operation::Function(module, function, _), _, _)
                    if module.qualified(*function) == env.declare_global_qid()
                        || module.qualified(*function) == env.declare_global_mut_qid()
            )
        });
        let qid = func_env.get_qualified_id();
        let mapped_spec = targets.is_spec(&qid);
        let declared_spec = func_env
            .get_toplevel_attributes()
            .get_(&AttributeKind_::Spec)
            .is_some();

        if std::env::var_os("SUI_LEAN_TRACE_SPEC_GLOBAL").is_some() && has_declaration {
            eprintln!(
                "spec-global trace: function={} is_spec={} target={:?} listed={} declared_spec={}",
                func_env.get_full_name_str(),
                mapped_spec,
                targets.get_fun_by_spec(&qid),
                targets.specs().any(|spec| spec == &qid),
                declared_spec,
            );
        }

        // `--include-all` runs several independent FunctionTargetsHolder
        // modes. A syntactic `#[spec]` can consequently appear in a holder
        // where its target relation is intentionally absent; upstream then
        // classifies its valid declaration calls as ordinary implementation
        // code and emits E0014. The same function is processed authoritatively
        // in the holder that owns its spec-target mapping. Drop only this
        // irrelevant duplicate variant instead of weakening declaration
        // checking or fabricating a target relation.
        if has_declaration && declared_spec && !mapped_spec {
            return None;
        }

        Some(self.inner.process(targets, func_env, data, scc_opt))
    }

    fn name(&self) -> String {
        "lean_spec_global_variable_analysis_processor".to_owned()
    }
}

/// As above, the upstream no-abort pass can inspect a substituted callee which
/// is absent from its scheduling graph. Its lattice bottom is `false`
/// ("may abort"), so pre-seeding it is sound and merely forgoes an optimization
/// if such an omitted edge is encountered before its callee is analyzed.
pub struct LeanNoAbortAnalysisProcessor {
    inner: Box<NoAbortAnalysisProcessor>,
}

impl LeanNoAbortAnalysisProcessor {
    pub fn new() -> Box<Self> {
        Box::new(Self {
            inner: NoAbortAnalysisProcessor::new(),
        })
    }
}

impl FunctionTargetProcessor for LeanNoAbortAnalysisProcessor {
    fn initialize(&self, _env: &GlobalEnv, targets: &mut FunctionTargetsHolder) {
        let fids = targets.get_funs().collect::<Vec<_>>();
        for fid in fids {
            let Some(data) = targets.get_data_mut(&fid, &FunctionVariant::Baseline) else {
                continue;
            };
            if !data.annotations.has::<NoAbortInfo>() {
                data.annotations.set(NoAbortInfo::default(), true);
            }
        }
    }

    fn process(
        &self,
        targets: &mut FunctionTargetsHolder,
        func_env: &FunctionEnv,
        data: FunctionData,
        scc_opt: Option<&[FunctionEnv]>,
    ) -> FunctionData {
        self.inner.process(targets, func_env, data, scc_opt)
    }

    fn name(&self) -> String {
        "lean_no_abort_analysis".to_owned()
    }
}

/// Whole-program determinism analysis. The upstream processor depends on the
/// target-pruned scheduling graph, returns `false` when a callee summary is
/// absent, and explicitly does not handle recursion. Quantifier validation is
/// performed later and needs the semantic call-graph result, not that
/// scheduling artifact.
pub struct LeanDeterministicAnalysisProcessor;

impl LeanDeterministicAnalysisProcessor {
    pub fn new() -> Box<Self> {
        Box::new(Self)
    }
}

impl FunctionTargetProcessor for LeanDeterministicAnalysisProcessor {
    fn is_single_run(&self) -> bool {
        true
    }

    fn run(&self, env: &GlobalEnv, targets: &mut FunctionTargetsHolder) {
        let mut function_ids = Vec::new();
        for module in env.get_modules() {
            function_ids.extend(module.get_functions().map(|fun| fun.get_qualified_id()));
        }

        // Greatest fixed point: a recursive component is deterministic unless
        // it reaches a declared non-deterministic native leaf.
        let mut summaries = function_ids
            .iter()
            .map(|qid| {
                let fun = env.get_function(*qid);
                let deterministic = if targets.is_pure_fun(qid) {
                    true
                } else if fun.is_native() {
                    lean_pipeline::stage_02_ir_cfg::has_ext_world(&fun)
                        || env.is_deterministic(*qid).unwrap_or(false)
                } else {
                    true
                };
                (*qid, deterministic)
            })
            .collect::<BTreeMap<_, _>>();

        loop {
            let mut changed = false;
            for qid in &function_ids {
                let fun = env.get_function(*qid);
                if targets.is_pure_fun(qid) || fun.is_native() || !summaries[&qid] {
                    continue;
                }
                if fun
                    .get_called_functions()
                    .iter()
                    .any(|callee| !summaries.get(callee).copied().unwrap_or(false))
                {
                    summaries.insert(*qid, false);
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }

        let target_ids = targets.get_funs_and_variants().collect::<Vec<_>>();
        for (qid, variant) in target_ids {
            if let Some(data) = targets.get_data_mut(&qid, &variant) {
                data.annotations.set(
                    DeterministicInfo {
                        is_deterministic: summaries.get(&qid).copied().unwrap_or(false),
                    },
                    true,
                );
            }
        }
    }

    fn name(&self) -> String {
        "lean_deterministic_analysis".to_owned()
    }
}

/// Compiled `--test-filter` regex plus the literal slice for upstream's
/// "module name contains literal" short-circuit (mirrored in `matches`).
#[derive(Clone)]
pub struct TestFilter {
    slice: String,
    regex: Regex,
}

impl TestFilter {
    pub fn from_str(s: &str) -> anyhow::Result<Self> {
        Ok(Self {
            slice: s.to_string(),
            regex: Regex::new(s)?,
        })
    }

    /// Mirrors `move_unit_test::test_runner::TestRunner::filter`:
    /// module-name-contains-literal short-circuits the whole module;
    /// otherwise regex-match against both `<module>::<func>` and
    /// `<addr>::<module>::<func>`. Over-includes relative to the
    /// runner's exact `format_module_id` qname — safe because the IR
    /// closure must be a superset of what executes, and the runner's
    /// own filter runs at execution time.
    fn matches(&self, fun_env: &FunctionEnv<'_>) -> bool {
        let env = fun_env.module_env.env;
        let module_name = env
            .symbol_pool()
            .string(fun_env.module_env.get_name().name())
            .to_string();
        if module_name.contains(&self.slice) {
            return true;
        }
        let func_name = env.symbol_pool().string(fun_env.get_name()).to_string();
        let bare_qname = format!("{}::{}", module_name, func_name);
        if self.regex.is_match(&bare_qname) {
            return true;
        }
        let addr = fun_env.module_env.self_address().to_canonical_string(true);
        let addr_qname = format!("{}::{}::{}", addr, module_name, func_name);
        self.regex.is_match(&addr_qname)
    }
}

pub struct LeanVerificationAnalysisProcessor {
    inner: Box<VerificationAnalysisProcessor>,
    /// `--include-all`: skip upstream's prune in `finalize()`.
    include_all: bool,
    /// `--test-filter` regex; non-matching `#[test]`s fall through
    /// `process()` unmarked and get pruned. `None` outside test mode.
    test_filter: Option<TestFilter>,
    /// New-pipeline only: TRUSTED spec wrappers (`#[spec(target=...)]`
    /// without `prove` or with `skip`, plus `run_on="boogie"` specs)
    /// to keep through the prune. They are not verification targets,
    /// so upstream never marks them verified and reachability alone
    /// rarely saves them -- but stage 12 needs their translated bodies
    /// (and companions, and their target's) to build the trusted
    /// `axiom` statements. Same keep shape as `loop_inv` below. Empty
    /// for the legacy path (which has no axiom emission from the new
    /// pipeline's stage 12).
    keep_trusted_specs: BTreeSet<QualifiedId<FunId>>,
}

impl LeanVerificationAnalysisProcessor {
    pub fn new(include_all: bool, keep_trusted_specs: BTreeSet<QualifiedId<FunId>>) -> Box<Self> {
        Box::new(Self {
            inner: VerificationAnalysisProcessor::new(),
            include_all,
            test_filter: None,
            keep_trusted_specs,
        })
    }

    pub fn new_for_testing(
        include_all: bool,
        test_filter: Option<TestFilter>,
        keep_trusted_specs: BTreeSet<QualifiedId<FunId>>,
    ) -> Box<Self> {
        Box::new(Self {
            inner: VerificationAnalysisProcessor::new_for_testing(),
            include_all,
            test_filter,
            keep_trusted_specs,
        })
    }
}

impl FunctionTargetProcessor for LeanVerificationAnalysisProcessor {
    fn process(
        &self,
        targets: &mut FunctionTargetsHolder,
        fun_env: &FunctionEnv,
        data: FunctionData,
        scc_opt: Option<&[FunctionEnv]>,
    ) -> FunctionData {
        // Non-matching `#[test]`s skip `mark_verified` and get
        // pruned in `finalize()`.
        if let Some(filter) = &self.test_filter {
            if fun_env.module_env.is_target()
                && fun_env
                    .get_toplevel_attributes()
                    .get_(&AttributeKind_::Test)
                    .is_some()
                && !filter.matches(fun_env)
            {
                return data;
            }
        }
        let mut data = self.inner.process(targets, fun_env, data, scc_opt);
        // `#[spec_only(loop_inv(...))]` functions are referenced only by their
        // attribute (never called), so the reachability prune in `finalize()`
        // would drop them. The Lean backend needs the invariant body rendered —
        // it types the hypothesis parameter injected on the loop helpers. Mirror
        // upstream's datatype-invariant handling: mark the predicate `inlined`
        // and `mark_callees_inlined` so the predicate AND everything it calls
        // survive the prune. (Upstream's own loop-invariant keeping fires via
        // the `loop_invariants` registry inside `mark_callees_inlined`, but that
        // registry is populated by `MoveLoopInvariantsProcessor`, which runs
        // after this pass — so for the Lean ordering we keep them here.)
        if is_spec_only_loop_inv(fun_env)
            || self
                .keep_trusted_specs
                .contains(&fun_env.get_qualified_id())
        {
            let info = data
                .annotations
                .get_or_default_mut::<VerificationInfo>(true);
            if !info.inlined {
                info.inlined = true;
                info.reachable = false;
                VerificationAnalysisProcessor::mark_callees_inlined(fun_env, targets);
            }
        }
        data
    }

    fn name(&self) -> String {
        self.inner.name()
    }

    fn initialize(&self, env: &GlobalEnv, targets: &mut FunctionTargetsHolder) {
        self.inner.initialize(env, targets);
    }

    fn finalize(&self, env: &GlobalEnv, targets: &mut FunctionTargetsHolder) {
        if !self.include_all {
            self.inner.finalize(env, targets);
        }
    }
}

/// True for `#[spec_only(loop_inv(...))]` functions — the loop-invariant
/// predicates the worker pipeline attaches to a target's loop. They are
/// referenced only by attribute, so the verification reachability prune would
/// drop them unless we mark them essential.
fn is_spec_only_loop_inv(fun_env: &FunctionEnv) -> bool {
    use move_compiler::shared::known_attributes::{KnownAttribute, VerificationAttribute};
    if let Some(attr) = fun_env
        .get_toplevel_attributes()
        .get_(&AttributeKind_::SpecOnly)
    {
        if let KnownAttribute::Verification(VerificationAttribute::SpecOnly { loop_inv, .. }) =
            &attr.value
        {
            return loop_inv.is_some();
        }
    }
    false
}

pub struct LeanSpecInstrumentationProcessor {
    inner: Box<SpecInstrumentationProcessor>,
}

impl LeanSpecInstrumentationProcessor {
    pub fn new() -> Box<Self> {
        Box::new(Self {
            inner: SpecInstrumentationProcessor::new(),
        })
    }
}

impl FunctionTargetProcessor for LeanSpecInstrumentationProcessor {
    fn process(
        &self,
        targets: &mut FunctionTargetsHolder,
        fun_env: &FunctionEnv,
        data: FunctionData,
        scc_opt: Option<&[FunctionEnv]>,
    ) -> FunctionData {
        // Restore `data.code` if upstream's non-verified branch
        // emptied it; Lean code-gen needs the body.
        let saved_code = data.code.clone();
        let saved_was_empty = saved_code.is_empty();
        let mut result = self.inner.process(targets, fun_env, data, scc_opt);
        if !fun_env.is_native() && !saved_was_empty && result.code.is_empty() {
            result.code = saved_code;
        }
        result
    }

    fn name(&self) -> String {
        self.inner.name()
    }

    fn initialize(&self, env: &GlobalEnv, targets: &mut FunctionTargetsHolder) {
        self.inner.initialize(env, targets);
    }

    fn finalize(&self, env: &GlobalEnv, targets: &mut FunctionTargetsHolder) {
        self.inner.finalize(env, targets);
    }
}
