//! Identifies functions transitively called by pure or axiom functions and
//! marks them as pure callee candidates. Validation is done later by
//! `PureFunctionAnalysisProcessor`.

use std::collections::{BTreeSet, VecDeque};

use move_model::model::{FunId, GlobalEnv, QualifiedId};

use crate::function_target_pipeline::{
    FunctionTargetProcessor, FunctionTargetsHolder, FunctionVariant,
};
use crate::quantifier_iterator_analysis::quantifier_body_functions;

pub struct PureCalleeDetectionProcessor();

impl PureCalleeDetectionProcessor {
    pub fn new() -> Box<Self> {
        Box::new(Self())
    }

    /// Whether `qid` may be pulled into the pure closure at all. A function
    /// already in one of the pure sets needs nothing; the rest are exclusions
    /// the closure has always made.
    fn can_be_pure_callee(
        env: &GlobalEnv,
        targets: &FunctionTargetsHolder,
        qid: &QualifiedId<FunId>,
    ) -> bool {
        if targets.is_pure_callee(qid) || targets.is_pure_fun(qid) || targets.is_axiom_fun(qid) {
            return false;
        }
        let fun_env = env.get_function(*qid);
        if fun_env.is_native() || fun_env.is_intrinsic() {
            return false;
        }
        // Skip functions with loop invariants: MoveLoopInvariantsProcessor
        // injects `ensures` calls into their bytecode, which is incompatible
        // with pure callee validation. TODO: fix MoveLoopInvariantsProcessor
        // to handle pure callee targets without injecting `ensures`.
        if targets.get_loop_invariants(qid).is_some() {
            return false;
        }
        true
    }
}

impl FunctionTargetProcessor for PureCalleeDetectionProcessor {
    fn is_single_run(&self) -> bool {
        true
    }

    fn run(&self, env: &GlobalEnv, targets: &mut FunctionTargetsHolder) {
        let funs: Vec<_> = targets.get_funs().collect();

        // Seed BFS with pure and axiom functions
        let mut queue: VecDeque<_> = funs
            .iter()
            .copied()
            .filter(|qid| {
                (targets.is_pure_fun(qid) || targets.is_axiom_fun(qid))
                    && !targets.is_backend_uninterpreted(qid)
            })
            .collect();

        // ... and with the body of every quantifier. The backend renders such a
        // body by its `$pure` name whatever attribute carries it, so a body that
        // no pure function happens to reach still needs a `$pure` declaration --
        // which only exists for the sets seeded here. `#[ext(no_abort)]` bodies
        // are the case in point: legal as a quantifier body, outside the pure
        // sets, and previously emitted as a reference with nothing declaring it.
        let mut bodies = BTreeSet::new();
        for qid in &funs {
            if let Some(data) = targets.get_data(qid, &FunctionVariant::Baseline) {
                bodies.extend(quantifier_body_functions(env, &data.code));
            }
        }
        for qid in bodies {
            if targets.is_backend_uninterpreted(&qid) {
                continue;
            }
            if !Self::can_be_pure_callee(env, targets, &qid) {
                continue;
            }
            targets.add_pure_callee(qid);
            queue.push_back(qid);
        }

        while let Some(qid) = queue.pop_front() {
            for callee in env.get_function(qid).get_called_functions() {
                if !Self::can_be_pure_callee(env, targets, &callee) {
                    continue;
                }
                targets.add_pure_callee(callee);
                queue.push_back(callee);
            }
        }
    }

    fn name(&self) -> String {
        "pure_callee_detection".to_string()
    }
}
