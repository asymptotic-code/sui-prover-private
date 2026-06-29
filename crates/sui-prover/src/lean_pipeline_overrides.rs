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
use move_compiler::shared::known_attributes::AttributeKind_;
use move_model::model::{FunctionEnv, GlobalEnv};
use move_stackless_bytecode::{
    function_target::FunctionData,
    function_target_pipeline::{FunctionTargetProcessor, FunctionTargetsHolder},
    spec_instrumentation::SpecInstrumentationProcessor,
    verification_analysis::{VerificationAnalysisProcessor, VerificationInfo},
};
use regex::Regex;

/// Compiled `--test-filter` regex plus the literal slice for upstream's
/// "module name contains literal" short-circuit (mirrored in `matches`).
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
}

impl LeanVerificationAnalysisProcessor {
    pub fn new(include_all: bool) -> Box<Self> {
        Box::new(Self {
            inner: VerificationAnalysisProcessor::new(),
            include_all,
            test_filter: None,
        })
    }

    pub fn new_for_testing(include_all: bool, test_filter: Option<TestFilter>) -> Box<Self> {
        Box::new(Self {
            inner: VerificationAnalysisProcessor::new_for_testing(),
            include_all,
            test_filter,
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
        if is_spec_only_loop_inv(fun_env) {
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
