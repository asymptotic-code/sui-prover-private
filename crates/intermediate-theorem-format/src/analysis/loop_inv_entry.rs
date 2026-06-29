// Loop-invariant entry cascade.
//
// A loop whose target carries `#[spec_only(loop_inv(...))]` only terminates
// under a precondition, so the generated impl cannot discharge the loop
// invariant at the entry call from its plain arguments — `emit_while` leaves a
// `sorry` placeholder (`IRNode::Abort`) there. This pass threads a precondition
// hypothesis (`hpre`) onto the impl and every same-module function that
// references it, so the renderer can replace the placeholder with a real proof
// (`<helper>.loop_entry … hpre h`, a user lemma) instead of `sorry`.
//
// Un-opinionated by design: the codegen never assumes the precondition is the
// spec's `requires` or assumes a branch shape. It injects a parameter typed by
// a *user-named* `<impl>.precond` predicate (parallel to `loop_hyp`); the user
// defines `precond` (e.g. as the spec's requires) and the `loop_entry` lemma
// that derives the invariant from it. Where the invariant actually comes from
// lives entirely in that user proof.

use crate::data::Program;
use crate::{FunctionID, IRNode};
use std::collections::HashSet;

/// True for a body that contains a loop-helper entry call: a `Call` to a
/// loop_inv helper whose trailing argument is the `sorry` placeholder. Recursive
/// `Continue` calls pass `Var(hinv)` rather than `Abort`, so this selects only
/// the impl's entry sites, not the loop body's self-calls.
fn has_entry_call(body: &IRNode, helper_ids: &HashSet<FunctionID>) -> bool {
    body.iter().any(|n| {
        matches!(n, IRNode::Call { function, args, .. }
            if helper_ids.contains(function)
                && matches!(args.last(), Some(IRNode::Abort { .. })))
    })
}

/// Variable names a function passes as positional args to `target` (from the
/// first such call), or the function's own parameter names as a fallback. Used
/// to apply the `precond` predicate at the right arguments in each caller.
fn call_arg_names(body: &IRNode, target: FunctionID) -> Option<Vec<String>> {
    body.fold(None, |acc, n| {
        if acc.is_some() {
            return acc;
        }
        if let IRNode::Call { function, args, .. } = n {
            if *function == target {
                let names: Vec<String> = args
                    .iter()
                    .filter_map(|a| match a {
                        IRNode::Var(v) => Some(v.to_string()),
                        _ => None,
                    })
                    .collect();
                if names.len() == args.len() {
                    return Some(names);
                }
            }
        }
        acc
    })
}

pub fn thread_loop_inv_entry(program: &mut Program) {
    if program.loop_inv_hyps.is_empty() {
        return;
    }

    // Loop helper function IDs (those carrying an injected `hinv` param).
    // `loop_inv_hyps` is keyed by helper ID, so this is a direct read.
    let helper_ids: HashSet<FunctionID> = program.loop_inv_hyps.keys().copied().collect();

    // Impls = functions with a loop-helper entry call.
    let impl_ids: Vec<FunctionID> = program
        .functions
        .iter()
        .filter(|(_, f)| has_entry_call(&f.body, &helper_ids))
        .map(|(id, _)| id)
        .collect();

    for impl_id in impl_ids {
        let impl_module_id = program.functions.get(&impl_id).module_id;
        let impl_module_name = program.modules.get(&impl_module_id).name.clone();
        let (impl_name, base, hook, impl_params) = {
            let func = program.functions.get(&impl_id);
            let base = func
                .name
                .strip_suffix(".aborts")
                .unwrap_or(&func.name)
                .to_string();
            let params: Vec<String> = func
                .signature
                .parameters
                .iter()
                .map(|p| p.name.clone())
                .collect();
            (
                func.name.clone(),
                base.clone(),
                format!("{}_spec.requires", base),
                params,
            )
        };

        // The hook `<base>_spec.requires` is an unqualified name; it only resolves
        // where the target's spec (`<base>_spec`) is rendered. That spec lives in
        // a `*_specs` module which the renderer MERGES into the impl's module iff
        // the spec module's name (minus `_specs`) equals the impl module's name —
        // the `spec_to_impl` rule, replicated here because that map isn't computed
        // until render time. Find the module of the `<base>_spec` companion that
        // actually merges into the impl's namespace (there may be several
        // same-named specs across sibling spec files); only companions FROM that
        // module can name the hook. If none merges (e.g. a loop_inv declared in a
        // differently-named spec file), neither the impl nor its callers can name
        // the hook, and the whole `hpre` cascade is skipped.
        let spec_name = format!("{}_spec", base);
        let spec_module_id = program.functions.iter().find_map(|(_, f)| {
            let is_companion =
                f.name == spec_name || f.name.starts_with(&format!("{}.", spec_name));
            if is_companion
                && program
                    .modules
                    .get(&f.module_id)
                    .name
                    .trim_end_matches("_specs")
                    == impl_module_name
            {
                Some(f.module_id)
            } else {
                None
            }
        });

        if spec_module_id.is_none() {
            // No resolvable spec: skip the whole `hpre` cascade. Replace the
            // entry-call placeholder — the `hinv` argument, an `IRNode::Abort`
            // that would otherwise render as a `MoveAbort` *value* and mistype the
            // loop_hyp `Prop` — with `sorry`, which inhabits any `Prop`, so the
            // entry call type-checks. (Co-located targets keep the `Abort`
            // placeholder, which the renderer rewrites into a `requires`-derived
            // `by`-macro at the dependent-if use-site.)
            program.loop_inv_entry_impls.insert(impl_name);
            let body = std::mem::take(&mut program.functions.get_mut(impl_id).body);
            let rewritten = body.map(&mut |n| match n {
                IRNode::Call {
                    function,
                    type_args,
                    mut args,
                } if helper_ids.contains(&function)
                    && matches!(args.last(), Some(IRNode::Abort { .. })) =>
                {
                    *args.last_mut().unwrap() = IRNode::Var("sorry".into());
                    IRNode::Call {
                        function,
                        type_args,
                        args,
                    }
                }
                other => other,
            });
            program.functions.get_mut(impl_id).body = rewritten;
            continue;
        }

        // The impl carries `(hpre : <spec>.requires <impl params>)`. Keyed by
        // `impl_id`, and each impl is visited exactly once, so a single push is
        // correct — no idempotency guard needed (the historical duplicate-`hpre`
        // bug came from name-keying collapsing two distinct same-named IDs).
        program.fn_proof_params.entry(impl_id).or_default().push((
            "hpre".to_string(),
            format!("{} {}", hook, impl_params.join(" ")),
        ));
        program.loop_inv_entry_impls.insert(impl_name);

        // The impl now expects one extra (proof) argument beyond its value
        // params. Every call site must supply it; `value_arity` distinguishes a
        // not-yet-threaded call from one already carrying the hypothesis.
        let value_arity = program.functions.get(&impl_id).signature.parameters.len();

        let caller_ids: Vec<FunctionID> = program
            .functions
            .iter()
            .filter(|(id, f)| *id != impl_id && f.body.calls().any(|c| c == impl_id))
            .map(|(id, _)| id)
            .collect();

        for caller_id in caller_ids {
            // Only a companion of the target's OWN spec — `<base>_spec` or its
            // `.ensures` / `.aborts` companions — forwards a real `hpre`. Such a
            // companion is co-located with the `<base>_spec.requires` hook by
            // construction (same spec module), and the generated correctness
            // obligation that references it accounts for the parameter. An
            // ordinary implementation function that calls the loop-inv target
            // (e.g. `set_voting_power`, `check_balance_invariants`), or a sibling
            // spec for a DIFFERENT target that merely calls this one, must NOT
            // gain an `hpre` parameter — its own callers cannot name the hook.
            // Those callers (and any whose call args aren't simple names)
            // discharge the entry hypothesis with `sorry`, which inhabits any
            // `Prop`; it is NOT `IRNode::Abort`, which now renders as a
            // `MoveAbort` *value* and would mistype the `Prop` proof parameter.
            let sorry = IRNode::Var("sorry".into());
            let caller = program.functions.get(&caller_id);
            let is_own_spec_companion =
                caller.name.starts_with(&spec_name) && Some(caller.module_id) == spec_module_id;
            let simple_args = call_arg_names(&caller.body, impl_id);
            let hpre_arg = if is_own_spec_companion {
                if let Some(args) = simple_args {
                    let caller_entry = program.fn_proof_params.entry(caller_id).or_default();
                    if !caller_entry.iter().any(|(n, _)| n == "hpre") {
                        caller_entry
                            .push(("hpre".to_string(), format!("{} {}", hook, args.join(" "))));
                    }
                    IRNode::Var("hpre".into())
                } else {
                    sorry
                }
            } else {
                sorry
            };

            // Forward the hypothesis on every value-arity call to the impl (i.e.
            // one not already carrying a proof argument).
            let body = std::mem::take(&mut program.functions.get_mut(caller_id).body);
            let rewritten = body.map(&mut |n| match n {
                IRNode::Call {
                    function,
                    type_args,
                    args,
                } if function == impl_id && args.len() == value_arity => {
                    let mut args = args;
                    args.push(hpre_arg.clone());
                    IRNode::Call {
                        function,
                        type_args,
                        args,
                    }
                }
                other => other,
            });
            program.functions.get_mut(caller_id).body = rewritten;
        }
    }
}
