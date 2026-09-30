use std::collections::{BTreeMap, BTreeSet};

use crate::{
    function_target::FunctionData,
    function_target_pipeline::{FunctionTargetProcessor, FunctionTargetsHolder, FunctionVariant},
    verification_analysis::VerificationInfo,
};
use codespan_reporting::diagnostic::Severity;
use move_model::model::{FunId, FunctionEnv, GlobalEnv, QualifiedId};

/// Rejects recursion the backend cannot translate soundly.
///
/// Callees are inlined (`{:inline 1}`), so a cycle of inlined calls cannot be
/// unrolled: past the bound Boogie assumes `false` and every path through the
/// recursion would verify vacuously. A call whose callee has a usable,
/// opaque spec is not inlined -- the caller gets the spec's contract -- so a
/// cycle cut by such calls is fine, provided each contract use is nested in
/// the execution of the function it describes (induction on call depth).
/// Mutual spec reliance with no code recursion (issue-355: `foo_spec`
/// assumes `bar_spec`, which assumes `foo_spec`) is circular and stays
/// rejected.
pub struct RecursionAnalysisProcessor();

impl RecursionAnalysisProcessor {
    pub fn new() -> Box<Self> {
        Box::new(Self())
    }

    /// The spec whose contract replaces `caller`'s call to `callee`, if any.
    fn contract_of(
        targets: &FunctionTargetsHolder,
        caller: &QualifiedId<FunId>,
        callee: &QualifiedId<FunId>,
    ) -> Option<QualifiedId<FunId>> {
        targets
            .get_callee_spec_qid(caller, callee)
            .filter(|spec| !targets.omits_opaque(spec))
            .copied()
    }

    fn reaches(
        graph: &BTreeMap<QualifiedId<FunId>, BTreeSet<QualifiedId<FunId>>>,
        from: QualifiedId<FunId>,
        to: QualifiedId<FunId>,
    ) -> bool {
        let mut seen = BTreeSet::new();
        let mut stack = vec![from];
        while let Some(node) = stack.pop() {
            if node == to {
                return true;
            }
            if seen.insert(node) {
                if let Some(next) = graph.get(&node) {
                    stack.extend(next.iter().copied());
                }
            }
        }
        false
    }

    fn has_cycle(graph: &BTreeMap<QualifiedId<FunId>, BTreeSet<QualifiedId<FunId>>>) -> bool {
        graph.iter().any(|(node, next)| {
            next.iter()
                .any(|succ| succ == node || Self::reaches(graph, *succ, *node))
        })
    }

    /// Whether the recursion among `members` is cut by opaque specs.
    /// `members` are the component's functions this pass translates; `scc`
    /// is the whole component, whose code calls decide whether a contract use
    /// is nested (a caller outside `members` still carries the recursion).
    fn is_cut_by_contracts(
        env: &GlobalEnv,
        targets: &FunctionTargetsHolder,
        members: &BTreeSet<QualifiedId<FunId>>,
        scc: &BTreeSet<QualifiedId<FunId>>,
    ) -> bool {
        let mut inlined: BTreeMap<_, BTreeSet<_>> = BTreeMap::new();
        let mut code: BTreeMap<_, BTreeSet<_>> = BTreeMap::new();
        for caller in scc {
            if !targets.is_spec(caller) {
                code.entry(*caller)
                    .or_default()
                    .extend(env.get_function(*caller).get_called_functions());
            }
        }
        let mut contract_calls = vec![];
        for caller in members {
            for callee in env.get_function(*caller).get_called_functions() {
                match Self::contract_of(targets, caller, &callee) {
                    Some(spec) => {
                        if members.contains(&callee) || members.contains(&spec) {
                            contract_calls.push((*caller, callee));
                        }
                    }
                    None => {
                        if members.contains(&callee) {
                            inlined.entry(*caller).or_default().insert(callee);
                        }
                    }
                }
            }
        }
        if Self::has_cycle(&inlined) {
            return false;
        }
        contract_calls
            .iter()
            .all(|(caller, callee)| Self::reaches(&code, *callee, *caller))
    }

    /// Whether this pass translates the function: verified or inlined. A
    /// function kept only as `reachable` (for borrow analysis) never reaches
    /// the backend, so its recursion cannot be unrolled anywhere.
    fn translated(info: Option<&VerificationInfo>) -> bool {
        info.map_or(false, |info| info.verified || info.inlined)
    }

    fn scc_members(
        fun_env: &FunctionEnv,
        scc_opt: Option<&[FunctionEnv]>,
    ) -> Option<BTreeSet<QualifiedId<FunId>>> {
        match scc_opt {
            Some(scc) => Some(scc.iter().map(|f| f.get_qualified_id()).collect()),
            // Direct self-recursion is a single node, which the SCC sort does
            // not report as a component.
            None => fun_env
                .get_called_functions()
                .contains(&fun_env.get_qualified_id())
                .then(|| BTreeSet::from([fun_env.get_qualified_id()])),
        }
    }
}

impl FunctionTargetProcessor for RecursionAnalysisProcessor {
    fn process(
        &self,
        targets: &mut FunctionTargetsHolder,
        fun_env: &FunctionEnv,
        data: FunctionData,
        scc_opt: Option<&[FunctionEnv]>,
    ) -> FunctionData {
        let Some(scc) = Self::scc_members(fun_env, scc_opt) else {
            return data;
        };
        if !Self::translated(data.annotations.get::<VerificationInfo>()) {
            return data;
        }
        let own = fun_env.get_qualified_id();
        let members: BTreeSet<_> = scc
            .iter()
            .copied()
            .filter(|qid| {
                *qid == own
                    || Self::translated(
                        targets
                            .get_data(qid, &FunctionVariant::Baseline)
                            .and_then(|d| d.annotations.get::<VerificationInfo>()),
                    )
            })
            .collect();
        let env = fun_env.module_env.env;
        if Self::is_cut_by_contracts(env, targets, &members, &scc) {
            return data;
        }
        let trace: Vec<String> = match scc_opt {
            Some(scc) => scc.iter().map(|f| f.get_full_name_str()).collect(),
            None => vec![fun_env.get_full_name_str(), fun_env.get_full_name_str()],
        };
        env.diag(
            Severity::Error,
            &fun_env.get_loc(),
            &format!(
                "Recursive functions are not supported for specifications.\nPath: {}\n\
                 Cut the recursion with a spec for one of these functions: its callers then \
                 use the spec's contract instead of inlining the body.",
                trace.join(" -> ")
            ),
        );
        data
    }

    fn name(&self) -> String {
        "recursion_analysis".to_string()
    }
}
