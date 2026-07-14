// Callee-`requires` entry cascade.
//
// A function F may call a function G that carries a `requires` precondition. The
// renderer cannot discharge G's `requires` from inside F's body when F is a
// plain value `def` (or its `.aborts` companion): there are no hypotheses in a
// def, so the generated `(by <G>_requires)` macro falls through to `sorry`,
// tainting F and everything proved about it.
//
// This pass mirrors `loop_inv_entry` but for a CALLEE's `requires` rather than a
// loop helper's invariant. When F calls such a G with the trailing `sorry`
// placeholder (`IRNode::Abort`) in the `requires` slot, it threads a proof
// parameter `(hpreN : <G>_spec.requires <G's call args>)` onto F and rewrites
// the call to forward `Var(hpreN)`. F's own callers then forward the hypothesis
// the same way `loop_inv_entry` does: a `_spec` companion co-located with F's
// own `<base>_spec.requires` hook threads a real `hpre` (its correctness
// obligation already carries that hypothesis); every other caller leaves the
// placeholder, which renders as `sorry` (it may legitimately stay tainted — a
// caller without the invariant cannot supply the precondition).
//
// Detection is deliberately narrow: only a `Call` to a loop-inv entry impl
// (`loop_inv_entry_impls`) whose trailing arg is `Abort` is rewritten. Those are
// exactly the call sites where the renderer would otherwise emit the
// `<G>_requires` `sorry` macro. No loops, no other passes are touched.

use crate::data::Program;
use crate::{FunctionID, IRNode};
use std::collections::HashSet;

/// Capitalize the first letter — matches `escape::module_name_to_namespace` for
/// the simple (non-colliding) module names this pass qualifies against.
fn module_namespace(name: &str) -> String {
    let mut chars = name.chars();
    match chars.next() {
        Some(c) => c.to_uppercase().chain(chars).collect(),
        None => String::new(),
    }
}

/// Render a call-argument expression to a Lean term string, in terms of the
/// carrying function's value parameters. Supports the shapes that appear in
/// these wrapper calls: a bare `Var`, and a `Field` access on such an
/// expression (`base.field_name`). Returns `None` for any other shape so the
/// caller can fall back to leaving the `sorry` placeholder.
fn render_arg(node: &IRNode, program: &Program) -> Option<String> {
    match node {
        IRNode::Var(v) => Some(v.to_string()),
        IRNode::Field {
            struct_id,
            field_index,
            base,
        } => {
            let s = program.structs.get(struct_id);
            let field_name = &s.fields[*field_index].name;
            let base_str = render_arg(base, program)?;
            Some(format!("({}.{})", base_str, field_name))
        }
        _ => None,
    }
}

/// Qualified `<G-namespace>.<base>_spec.requires` for a callee G in `callee_mod`,
/// viewed from the function in `caller_mod`. Same module → unqualified.
fn requires_hook(
    program: &Program,
    callee_mod: crate::ModuleID,
    caller_mod: crate::ModuleID,
    g_base: &str,
) -> String {
    let bare = format!("{}_spec.requires", g_base);
    if callee_mod == caller_mod {
        return bare;
    }
    let ns = program
        .namespace_overrides
        .get(&callee_mod)
        .cloned()
        .unwrap_or_else(|| module_namespace(&program.modules.get(&callee_mod).name));
    format!("{}.{}", ns, bare)
}

/// Positional value args a function passes to `target` (first such call), if all
/// are simple `Var`s — used to apply F's own spec hook in a `_spec` caller.
fn call_var_args(body: &IRNode, target: FunctionID) -> Option<Vec<String>> {
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

/// A `Call` to one of `g_ids` whose trailing arg is the `sorry` placeholder.
fn entry_call_to(body: &IRNode, g_ids: &HashSet<FunctionID>) -> Option<(FunctionID, usize)> {
    body.fold(None, |acc, n| {
        if acc.is_some() {
            return acc;
        }
        if let IRNode::Call { function, args, .. } = n {
            if g_ids.contains(function) && matches!(args.last(), Some(IRNode::Abort { .. })) {
                return Some((*function, args.len()));
            }
        }
        acc
    })
}

/// The non-placeholder args of an entry call to some `g_id`, preferring the call
/// whose args are all renderable in terms of `caller_params` (so the `hpre`
/// type references only the carrying function's parameters). The callee's
/// `requires` is invariant across the differing args at the multiple call sites
/// (they share the same precondition predicate), so any param-only call's args
/// type the single threaded `hpre` for all of them.
fn best_entry_args(
    body: &IRNode,
    g_ids: &HashSet<FunctionID>,
    program: &Program,
    caller_params: &HashSet<String>,
) -> Option<Vec<IRNode>> {
    let arg_is_param = |a: &IRNode| -> bool {
        render_arg(a, program)
            .map(|s| {
                let head = s.trim_start_matches('(').split(['.', ' ']).next().unwrap();
                caller_params.contains(head)
            })
            .unwrap_or(false)
    };
    let mut fallback: Option<Vec<IRNode>> = None;
    let mut param_only: Option<Vec<IRNode>> = None;
    body.fold((), |_, n| {
        if let IRNode::Call { function, args, .. } = n {
            if g_ids.contains(function) && matches!(args.last(), Some(IRNode::Abort { .. })) {
                let value_args = args[..args.len() - 1].to_vec();
                if fallback.is_none() {
                    fallback = Some(value_args.clone());
                }
                if param_only.is_none() && value_args.iter().all(arg_is_param) {
                    param_only = Some(value_args);
                }
            }
        }
    });
    param_only.or(fallback)
}

pub fn thread_callee_requires_entry(program: &mut Program) {
    if program.loop_inv_entry_impls.is_empty() {
        return;
    }

    // Candidate callees G: loop-inv entry impls (the only call sites the renderer
    // turns into a `<G>_requires` sorry macro), keyed by ID.
    let g_ids: HashSet<FunctionID> = program
        .functions
        .iter()
        .filter(|(_, f)| program.loop_inv_entry_impls.contains(&f.name))
        .map(|(id, _)| id)
        .collect();
    if g_ids.is_empty() {
        return;
    }

    // F candidates: any function that calls such a G with the trailing `sorry`
    // placeholder AND is itself a plain value def / `.aborts` (NOT a loop helper,
    // and not already a loop-inv entry impl — those are handled by
    // `loop_inv_entry`). We additionally require F to NOT already carry an `hpre`
    // for this slot via the loop_inv cascade.
    // A function is a genuine loop-inv entry impl (handled by `loop_inv_entry`,
    // NOT here) iff it calls one of ITS OWN loop helpers (`<self>.while_N`).
    // `loop_inv_entry_impls` is name-keyed, so a same-named cross-module wrapper
    // (e.g. `Validator.pool_token_exchange_rate_at_epoch`) is wrongly flagged
    // there; key off the helper-call shape instead.
    let calls_own_loop_helper = |f: &crate::data::functions::Function| -> bool {
        f.body.calls().any(|c| {
            let n = &program.functions.get(&c).name;
            n.starts_with(&format!("{}.while_", f.name.trim_end_matches(".aborts")))
                || n.starts_with(&format!("{}.after_", f.name.trim_end_matches(".aborts")))
        })
    };
    let f_candidates: Vec<FunctionID> = program
        .functions
        .iter()
        .filter(|(id, f)| {
            !f.name.contains(".while_")
                && !f.name.contains(".after_")
                && !calls_own_loop_helper(f)
                && entry_call_to(&f.body, &g_ids).is_some()
                && f.body.calls().all(|c| c != *id) // not self-recursive
        })
        .map(|(id, _)| id)
        .collect();

    for f_id in f_candidates {
        let (g_id, _) = entry_call_to(&program.functions.get(&f_id).body, &g_ids).unwrap();

        let f_mod = program.functions.get(&f_id).module_id;
        let g_mod = program.functions.get(&g_id).module_id;
        let g_name = program.functions.get(&g_id).name.clone();
        let g_base = g_name
            .strip_suffix(".aborts")
            .unwrap_or(&g_name)
            .to_string();

        // The args G is applied to in F's call — these reference F's params, so
        // they are a valid type for an `hpre` param on F. Prefer the call whose
        // args are all F's own parameters (the callee's `requires` is the same
        // predicate at every site, so any param-only call types the single
        // `hpre`).
        let f_params: HashSet<String> = program
            .functions
            .get(&f_id)
            .signature
            .parameters
            .iter()
            .map(|p| p.name.to_string())
            .collect();
        let Some(g_args) = best_entry_args(
            &program.functions.get(&f_id).body,
            &g_ids,
            program,
            &f_params,
        ) else {
            continue;
        };
        let rendered_args: Option<Vec<String>> = g_args
            .iter()
            .map(|a| render_arg(a, program))
            .collect::<Option<Vec<String>>>();
        let Some(rendered_args) = rendered_args else {
            continue;
        };
        // Require all hpre-type args to be F's own params; otherwise the type
        // would reference an out-of-scope let-temp. Leave the sorry fallback.
        let all_params = rendered_args.iter().all(|s| {
            let head = s.trim_start_matches('(').split(['.', ' ']).next().unwrap();
            f_params.contains(head)
        });
        if !all_params {
            continue;
        }

        let hook = requires_hook(program, g_mod, f_mod, &g_base);
        let hpre_type = format!("{} {}", hook, rendered_args.join(" "));

        // Thread `hpre` onto F and rewrite F's call to G to forward it.
        program
            .fn_proof_params
            .entry(f_id)
            .or_default()
            .push(("hpre".to_string(), hpre_type));
        program.callee_requires_impls.insert(f_id);

        // Rewrite EVERY entry call to G (both the value and `.aborts` variants of
        // G share the same `requires`, so a single `hpre` discharges all of them).
        let g_value_id = g_id;
        let g_aborts_id = program
            .functions
            .iter()
            .find(|(_, c)| c.module_id == g_mod && c.name == format!("{}.aborts", g_base))
            .map(|(id, _)| id);
        let body = std::mem::take(&mut program.functions.get_mut(f_id).body);
        let rewritten = body.map(&mut |n| match n {
            IRNode::Call {
                function,
                type_args,
                args,
            } if (function == g_value_id || Some(function) == g_aborts_id)
                && matches!(args.last(), Some(IRNode::Abort { .. })) =>
            {
                let mut args = args;
                let last = args.len() - 1;
                args[last] = IRNode::Var("hpre".into());
                IRNode::Call {
                    function,
                    type_args,
                    args,
                }
            }
            other => other,
        });
        program.functions.get_mut(f_id).body = rewritten;

        // F now expects one extra (proof) arg beyond its value params.
        let value_arity = program.functions.get(&f_id).signature.parameters.len();

        // F's own spec hook (for forwarding onto F's `_spec` companions). F's
        // base name drops a `.aborts` suffix; the hook lives in F's own module.
        let f_name = program.functions.get(&f_id).name.clone();
        let f_base = f_name
            .strip_suffix(".aborts")
            .unwrap_or(&f_name)
            .to_string();
        let f_hook = format!("{}_spec.requires", f_base);
        let f_spec_name = format!("{}_spec", f_base);
        let f_spec_mod = program.functions.iter().find_map(|(_, c)| {
            let is_companion =
                c.name == f_spec_name || c.name.starts_with(&format!("{}.", f_spec_name));
            if is_companion
                && program
                    .modules
                    .get(&c.module_id)
                    .name
                    .trim_end_matches("_specs")
                    == program.modules.get(&f_mod).name
            {
                Some(c.module_id)
            } else {
                None
            }
        });

        // Forward onto every value-arity caller of F.
        let caller_ids: Vec<FunctionID> = program
            .functions
            .iter()
            .filter(|(id, c)| *id != f_id && c.body.calls().any(|x| x == f_id))
            .map(|(id, _)| id)
            .collect();

        for caller_id in caller_ids {
            let caller = program.functions.get(&caller_id);
            let caller_params: HashSet<String> = caller
                .signature
                .parameters
                .iter()
                .map(|p| p.name.to_string())
                .collect();
            let is_threadable_companion =
                Some(caller.module_id) == f_spec_mod && caller.name.contains("_spec");
            let simple_args = call_var_args(&caller.body, f_id)
                .filter(|a| a.iter().all(|n| caller_params.contains(n)));

            let forward = if is_threadable_companion {
                if let Some(args) = simple_args {
                    let entry = program.fn_proof_params.entry(caller_id).or_default();
                    if !entry.iter().any(|(n, _)| n == "hpre") {
                        entry.push(("hpre".to_string(), format!("{} {}", f_hook, args.join(" "))));
                    }
                    IRNode::Var("hpre".into())
                } else {
                    IRNode::Abort { code: None }
                }
            } else {
                IRNode::Abort { code: None }
            };

            let body = std::mem::take(&mut program.functions.get_mut(caller_id).body);
            let rewritten = body.map(&mut |n| match n {
                IRNode::Call {
                    function,
                    type_args,
                    args,
                } if function == f_id && args.len() == value_arity => {
                    let mut args = args;
                    args.push(forward.clone());
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
