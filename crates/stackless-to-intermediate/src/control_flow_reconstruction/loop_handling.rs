// Copyright (c) Asymptotic
// SPDX-License-Identifier: Apache-2.0

//! Loop handling: translates While structures into separate Lean functions.
//!
//! Each while loop becomes two functions per emit pass:
//! - `while_func` (loop iteration body)
//! - `after_func` (continuation after loop exit)
//!
//! In Body mode these compute the return value; in Aborts mode they compute Bool.
//! Since each mode has its own EmitContext with independent scope, the parameter
//! lists are computed independently and correctly for each side.

use super::{no_abort, EmitContext, EmitMode, WhileLoopInfo};
use intermediate_theorem_format::IRNode;
use intermediate_theorem_format::{Function, FunctionSignature, Parameter, Type};

/// Emit an IRNode for a While structure.
pub fn emit_while(
    ctx: &mut EmitContext,
    body: &IRNode,
    loop_body: &super::ir_translation::Structure,
    continuation: Option<&super::ir_translation::Structure>,
) -> IRNode {
    // Extend scope with bindings from code preceding the loop
    ctx.extend_scope(body);

    // Save scope before emitting continuation/loop body
    let scope_at_loop = ctx.save_scope();

    if std::env::var("PROBE_CONV").is_ok() && ctx.func_name.starts_with("string_bytes_lt") {
        eprintln!(
            "PROBE_CONV func_name={} mode={:?} continuation={:#?}",
            ctx.func_name, ctx.mode, continuation
        );
    }
    // Emit continuation FIRST so we can determine after_func's full parameter list.
    let conv = continuation
        .map(|c| super::early_return::emit(ctx, c))
        .unwrap_or_else(|| match ctx.mode {
            EmitMode::Body => IRNode::unit(),
            EmitMode::Aborts => no_abort(),
        });
    if std::env::var("PROBE_CONV").is_ok() && ctx.func_name.starts_with("string_bytes_lt") {
        eprintln!("PROBE_CONV conv={:#?}", conv);
    }

    // No outer-guard wrapping: the continuation is emitted directly.
    // Termination proofs can derive the outer guard from calling context.

    // Restore scope so continuation bindings don't leak
    ctx.restore_scope(scope_at_loop.clone());

    // `while_params` = the variables in scope at the loop's entry point that
    // are actually read inside `loop_body` or in the continuation `conv`.
    //
    // The naive choice is "every variable in scope at loop entry" (the
    // scope-preserving rule), with dead-param elimination as a later pass.
    // That works for `while_func` itself but the dead-param pass currently
    // skips every `.aborts` companion (its parameters must stay in sync with
    // the impl's so callee-aborts composition can copy args). For test bodies
    // generated from `assert!` macros inside `cases!` × `range_do!` nests
    // (stdlib's `test_dos`), the naive rule produces helpers with 180+
    // parameters and the resulting `.aborts` companions blow past Lean's
    // `whnf` heartbeat budget.
    //
    // Computing the minimal set up front, before the helper is materialised,
    // avoids that bloat for both the impl and the `.aborts`. Both are emitted
    // from this same `emit_while` call with the same `while_params`, so they
    // stay parameter-synchronised by construction.
    //
    // We include the continuation's free vars so that vars used only in the
    // continuation (post-loop) are still threaded — `after_params` extends
    // `while_params` with loop-body escape vars, and the after_func receives
    // the union via Break call sites.
    //
    // Critically: we collect free vars from the continuation's *structure*
    // tree (mode-independent), not from the emitted `conv` IRNode. The Body
    // and Aborts modes are emitted independently from the same `structure`,
    // and `early_return::emit` produces mode-specific IR. Using the
    // already-emitted `conv` would yield different filters per mode and
    // break the impl-vs-`.aborts` parameter symmetry that the
    // callee-aborts composition pass relies on.
    let used_vars: std::collections::BTreeSet<_> = {
        let mut s = collect_structure_free_vars(loop_body);
        if let Some(cont) = continuation {
            s.extend(collect_structure_free_vars(cont));
        }

        // Cross-level Continue/Break leaves don't show up in
        // `collect_structure_free_vars` — the variable references they
        // introduce are synthesised at *emission* time by
        // `emit_loop_call`, which fetches the targeted enclosing
        // loop's `while_params` (Continue) or `after_params` (Break)
        // and passes them as call args. Walking the structure for free
        // vars sees only the leaf body / cond / scrutinee IR; the call
        // site's `Var` references are not yet there.
        //
        // The result is that any cross-level termination produces a
        // call whose arguments reference names that, after the
        // used-vars filter, are no longer in this loop's `while_params`.
        // The argument site emits an unbound `Var(name)` and Lake
        // rejects with `Undefined variable: <name>`.
        //
        // Walk the structure tree for every Continue/Break leaf,
        // figure out which enclosing loop frame it actually targets at
        // emit time, and union that frame's params (while_params for
        // Continue, after_params for Break) into the used set so they
        // survive the filter. The walker tracks a stack-length offset
        // relative to this `emit_while`'s pre-push state, which is
        // independent for `loop_body` (caller pushed, offset starts at
        // 1) and for `continuation` (caller not on stack, offset starts
        // at 0).
        let mut term_levels: Vec<(usize, bool)> = Vec::new();
        collect_term_resolutions(loop_body, 1, &mut term_levels);
        if let Some(cont) = continuation {
            collect_term_resolutions(cont, 0, &mut term_levels);
        }
        for (enc_level, is_break) in term_levels {
            if let Some(info) = ctx.enclosing_while(enc_level) {
                let params = if is_break {
                    &info.after_params
                } else {
                    &info.while_params
                };
                for v in params {
                    s.insert(v.clone());
                }
            }
        }
        s
    };
    let while_params: Vec<_> = ctx
        .scope()
        .iter()
        .filter(|v| v.as_ref() != "_")
        .filter(|v| used_vars.contains(*v))
        .cloned()
        .collect();

    // Reserve function IDs for while_func and after_func
    let while_func_id = ctx.program.functions.reserve_id();
    let after_func_id = ctx.program.functions.reserve_id();

    let while_name = ctx.next_while_name();
    let after_name = format!("{}.after", while_name);

    // In aborts mode, append ".aborts" to names
    let (while_display_name, after_display_name) = match ctx.mode {
        EmitMode::Body => (while_name.clone(), after_name.clone()),
        EmitMode::Aborts => (
            format!("{}.aborts", while_name),
            format!("{}.aborts", after_name),
        ),
    };

    // A loop whose target function carries a `#[spec_only(loop_inv(...))]` gets
    // a loop-invariant hypothesis parameter threaded onto its `while_func` so
    // termination can be discharged with the invariant in scope (see
    // `Program::loop_inv_hyps`). The proof argument at the recursive Continue
    // calls is the same hypothesis (the invariant is preserved across the loop);
    // the entry call from the enclosing function supplies it (initially a `sorry`
    // placeholder — the requires-derived proof is wired separately).
    let hyp_param: Option<intermediate_theorem_format::data::types::TempId> =
        if ctx.program.loop_invariants.contains_key(&ctx.func_name) {
            ctx.program.loop_inv_hyps.insert(
                while_func_id,
                intermediate_theorem_format::LoopInvHyp {
                    hyp_param: "hinv".to_string(),
                    hook_name: format!("{}.loop_hyp", while_name),
                },
            );
            Some("hinv".into())
        } else {
            None
        };

    let type_args: Vec<Type> = ctx
        .type_params
        .iter()
        .enumerate()
        .map(|(i, _)| Type::TypeParameter(i as u16))
        .collect();

    // `.after`'s parameters start with `while_params` (every name in scope at
    // loop entry — the same scope-preserving rule that drives `while_params`).
    // We then extend with extras: variables the continuation references that
    // were bound *inside the loop body* (e.g. `let effects = ...; if cond
    // { return effects }` produces a continuation that reads `effects` even
    // though `effects` is not in scope at loop entry).
    //
    // At Break call sites the extras are still in scope (they were defined
    // earlier in the loop body's shared prefix), so passing them as args is
    // safe; the after_func receives them as parameters and the continuation
    // body can resolve them.
    //
    // We restrict extras to vars actually bound inside `loop_body` — vars in
    // conv that aren't bound anywhere in the loop body can't be passed via
    // Break (they wouldn't be in scope at the Break site), so adding them as
    // params would just propagate the same unbound reference into a wider
    // surface.
    let mut after_params = while_params.clone();
    {
        // Tighter than `collect_structure_bindings`: a var is only safe
        // to thread through `after_params` if it is bound on EVERY path
        // from loop entry to a Break that targets THIS loop. Bindings
        // that live in only some branches (e.g. a let inside the THEN
        // arm of a cond-check whose ELSE arm is the Break leaf) are NOT
        // in scope at the Break call site, so passing them as args
        // produces undefined-var IR. See `collect_break_safe_bindings`.
        let break_safe_bindings = collect_break_safe_bindings(loop_body);
        let mut already_added: std::collections::BTreeSet<_> =
            while_params.iter().cloned().collect();
        for v in conv.free_vars() {
            if v.as_ref() == "_" {
                continue;
            }
            if already_added.contains(&v) {
                continue;
            }
            if !break_safe_bindings.contains(&v) {
                continue;
            }
            if !ctx.variables.contains_key(&v) {
                continue;
            }
            after_params.push(v.clone());
            already_added.insert(v);
        }
    }

    // Push while context so Continue/Break can emit real Calls.
    // after_params now includes the extra variables the continuation needs.
    ctx.push_while(WhileLoopInfo {
        while_func_id,
        after_func_id,
        while_params: while_params.clone(),
        after_params: after_params.clone(),
        type_args: type_args.clone(),
        hyp_param: hyp_param.clone(),
    });

    // Emit loop body — Continue/Break will use ctx.current_while()
    let loop_ir = super::early_return::emit(ctx, loop_body);

    // Pop the while context
    ctx.pop_while();

    // Restore scope so loop body bindings don't leak
    ctx.restore_scope(scope_at_loop);

    // Build parameter lists
    let while_parameters: Vec<Parameter> = while_params
        .iter()
        .map(|name| make_param(ctx, name))
        .collect();

    let after_parameters: Vec<Parameter> = after_params
        .iter()
        .map(|name| make_param(ctx, name))
        .collect();

    let return_type = match ctx.mode {
        EmitMode::Body => ctx.return_type.clone(),
        EmitMode::Aborts => Type::Bool,
    };

    // Create while_func
    ctx.program.functions.insert(
        while_func_id,
        Function {
            module_id: ctx.module_id,
            name: while_display_name,
            signature: FunctionSignature {
                type_params: ctx.type_params.clone(),
                parameters: while_parameters,
                proof_params: Vec::new(),
                return_type: return_type.clone(),
            },
            body: loop_ir,

            theorem: None,
            is_native: false,
            mutual_group_id: None,
            test_expectation: None,
            is_uninterpreted: false,
        },
    );

    // Create after_func.
    let is_unit = matches!(&conv, IRNode::Tuple(v) if v.is_empty());
    let after_body = if is_unit
        && !matches!(&return_type, Type::Tuple(v) if v.is_empty())
        && !matches!(&return_type, Type::Bool)
    {
        IRNode::Inhabited
    } else {
        conv
    };
    ctx.program.functions.insert(
        after_func_id,
        Function {
            module_id: ctx.module_id,
            name: after_display_name,
            signature: FunctionSignature {
                type_params: ctx.type_params.clone(),
                parameters: after_parameters,
                proof_params: Vec::new(),
                return_type,
            },
            body: after_body,

            theorem: None,
            is_native: false,
            mutual_group_id: None,
            test_expectation: None,
            is_uninterpreted: false,
        },
    );

    // Call site: call while_func with current scope variables
    let mut args: Vec<IRNode> = while_params
        .iter()
        .map(|v| IRNode::Var(v.clone()))
        .collect();
    // For loop_inv loops, the entry call must also supply the loop-invariant
    // hypothesis. The faithful proof derives it from the enclosing function's
    // `requires`; until that threading lands it is a `sorry` placeholder
    // (`IRNode::Abort` renders `sorry`, a proof of any proposition).
    if hyp_param.is_some() {
        args.push(IRNode::Abort { code: None });
    }
    let call = IRNode::Call {
        function: while_func_id,
        type_args,
        args,
    };

    IRNode::assign(body.clone(), call)
}

fn make_param(ctx: &EmitContext, name: &str) -> Parameter {
    let param_type = ctx
        .variables
        .get(name)
        .cloned()
        .unwrap_or(Type::Tuple(vec![]));
    Parameter {
        name: name.to_string(),
        param_type,
        ssa_value: name.into(),
    }
}

/// Emit an IRNode for a Continue / Break leaf at the given level.
/// Both share the same shape — look up the targeted loop's
/// `WhileLoopInfo` via `enclosing_while(level)`, then emit a `Call` to
/// either the loop's iteration function (Continue) or its continuation
/// function (Break). The two leaves only differ in which params and
/// which function id they pull from the info.
fn emit_loop_call(
    ctx: &EmitContext,
    level: usize,
    body: &IRNode,
    params_of: impl Fn(&WhileLoopInfo) -> &Vec<intermediate_theorem_format::data::types::TempId>,
    func_id_of: impl Fn(&WhileLoopInfo) -> intermediate_theorem_format::FunctionID,
) -> IRNode {
    match ctx.enclosing_while(level) {
        Some(info) => {
            let mut args: Vec<IRNode> = params_of(info)
                .iter()
                .map(|v| IRNode::Var(v.clone()))
                .collect();
            // A Continue re-enters `while_func`, which (for loop_inv loops) takes
            // the invariant hypothesis as its final parameter. The invariant is
            // preserved across iterations, so the recursive call threads the same
            // hypothesis variable unchanged. Only `while_func` carries it; Break
            // (→ after_func) does not, so this is gated on the call targeting
            // `while_func_id`.
            if let Some(hp) = &info.hyp_param {
                if func_id_of(info) == info.while_func_id {
                    args.push(IRNode::Var(hp.clone()));
                }
            }
            let call = IRNode::Call {
                function: func_id_of(info),
                type_args: info.type_args.clone(),
                args,
            };
            IRNode::assign(body.clone(), call)
        }
        None => match ctx.mode {
            EmitMode::Body => body.clone(),
            EmitMode::Aborts => IRNode::assign(body.clone(), no_abort()),
        },
    }
}

/// Emit an IRNode for a Continue (loop back-edge) leaf at the given
/// level (0 = innermost). Cross-level continues call the targeted
/// loop's while_func directly, bypassing intermediate after_funcs —
/// the source-level semantics of "exit inner loops and re-enter the
/// outer."
pub fn emit_continue(ctx: &EmitContext, level: usize, body: &IRNode) -> IRNode {
    emit_loop_call(
        ctx,
        level,
        body,
        |info| &info.while_params,
        |info| info.while_func_id,
    )
}

/// Emit an IRNode for a Break (loop exit) leaf at the given level
/// (0 = innermost). Cross-level breaks call the targeted loop's
/// after_func directly, bypassing intermediate after_funcs — the
/// semantic of "exit through multiple loops at once" preserved in the
/// lowering.
pub fn emit_break(ctx: &EmitContext, level: usize, body: &IRNode) -> IRNode {
    emit_loop_call(
        ctx,
        level,
        body,
        |info| &info.after_params,
        |info| info.after_func_id,
    )
}

/// Collect every let-binding name introduced anywhere inside a `Structure`
/// tree (leaf bodies, nested If/Switch/While arms, and continuations). Used
/// by `emit_while` to identify which continuation-free-vars are actually
/// reachable as Break-call args. `IRNode::bindings()` covers the per-leaf
/// IR; this just walks the structure shape and unions the per-leaf sets.
///
/// Replaces the now-deleted `Structure::bindings()` inherent method
/// (removed in #449's "drop dead Structure methods" cleanup) — same walk,
/// kept local to the one caller that still needs it.
fn collect_structure_bindings(
    s: &super::ir_translation::Structure,
) -> std::collections::BTreeSet<intermediate_theorem_format::data::types::TempId> {
    let mut out = std::collections::BTreeSet::new();
    collect_structure_bindings_inner(s, &mut out);
    out
}

fn collect_structure_bindings_inner(
    s: &super::ir_translation::Structure,
    out: &mut std::collections::BTreeSet<intermediate_theorem_format::data::types::TempId>,
) {
    use super::ir_translation::Structure;
    match s {
        Structure::Leaf { body, .. } => out.extend(body.bindings()),
        Structure::If {
            body,
            then_branch,
            else_branch,
            continuation,
            ..
        } => {
            out.extend(body.bindings());
            collect_structure_bindings_inner(then_branch, out);
            collect_structure_bindings_inner(else_branch, out);
            if let Some(cont) = continuation {
                collect_structure_bindings_inner(cont, out);
            }
        }
        Structure::While {
            body,
            loop_body,
            continuation,
        } => {
            out.extend(body.bindings());
            collect_structure_bindings_inner(loop_body, out);
            if let Some(cont) = continuation {
                collect_structure_bindings_inner(cont, out);
            }
        }
        Structure::Switch {
            body,
            cases,
            continuation,
            ..
        } => {
            out.extend(body.bindings());
            for case in cases {
                collect_structure_bindings_inner(case, out);
            }
            if let Some(cont) = continuation {
                collect_structure_bindings_inner(cont, out);
            }
        }
    }
}

/// Compute the set of variables read (free) anywhere in a `Structure`.
///
/// Walks the structure tree and unions `body.free_vars()` across every
/// node's per-step `body` IR plus their children. Used by `emit_while`
/// to compute the minimal set of in-scope variables that the
/// `while_func` / `after_func` helpers actually need to thread through.
///
/// The result is a coarse over-approximation of the helpers' true
/// liveness: it includes any `Var(name)` reference, even when the same
/// name is shadowed by a sibling-arm's later `let`. The intersection
/// with `ctx.scope()` at the call site handles this — vars bound
/// inside the loop are filtered out, leaving only those that could
/// only have been referencing the outer scope.
fn collect_structure_free_vars(
    s: &super::ir_translation::Structure,
) -> std::collections::BTreeSet<intermediate_theorem_format::data::types::TempId> {
    let mut out = std::collections::BTreeSet::new();
    collect_structure_free_vars_inner(s, &mut out);
    out
}

fn collect_structure_free_vars_inner(
    s: &super::ir_translation::Structure,
    out: &mut std::collections::BTreeSet<intermediate_theorem_format::data::types::TempId>,
) {
    use super::ir_translation::Structure;
    match s {
        Structure::Leaf { body, .. } => out.extend(body.free_vars()),
        Structure::If {
            body,
            cond,
            then_branch,
            else_branch,
            continuation,
        } => {
            out.extend(body.free_vars());
            out.extend(cond.free_vars());
            collect_structure_free_vars_inner(then_branch, out);
            collect_structure_free_vars_inner(else_branch, out);
            if let Some(cont) = continuation {
                collect_structure_free_vars_inner(cont, out);
            }
        }
        Structure::While {
            body,
            loop_body,
            continuation,
        } => {
            out.extend(body.free_vars());
            collect_structure_free_vars_inner(loop_body, out);
            if let Some(cont) = continuation {
                collect_structure_free_vars_inner(cont, out);
            }
        }
        Structure::Switch {
            body,
            scrutinee,
            cases,
            continuation,
        } => {
            out.extend(body.free_vars());
            out.extend(scrutinee.free_vars());
            for case in cases {
                collect_structure_free_vars_inner(case, out);
            }
            if let Some(cont) = continuation {
                collect_structure_free_vars_inner(cont, out);
            }
        }
    }
}

/// Walk a structure subtree and record every Continue/Break leaf
/// whose target, at emission time, is a frame *outside* this
/// `emit_while`'s pre-push enclosing stack. Each entry is
/// `(enclosing_level, is_break)` where `enclosing_level` indexes the
/// pre-push `ctx.while_stack` from the innermost (level 0).
///
/// `stack_len_offset` is the difference between the emit-time
/// `while_stack.len()` at this point in the subtree and the caller
/// `emit_while`'s pre-push `while_stack.len()`. It starts at:
///   - 1 when walking THIS loop's `loop_body` (caller has pushed self
///     before emit_loop), so emission-time stack length = pre + 1
///   - 0 when walking THIS loop's `continuation` (caller has not
///     pushed self; the after-func runs after this loop exits, so
///     emission-time stack length = pre)
///
/// Each `Structure::While` we descend INTO via `loop_body` adds 1 to
/// the offset (the nested while pushes its frame at emit). Descending
/// into a `Structure::While` via `continuation` keeps the offset (the
/// nested while's frame has been popped by then). `Structure::If` and
/// `Structure::Switch` don't change the offset.
///
/// A leaf's resolved index in the emission stack is
/// `pre_len + stack_len_offset - 1 - level`. If that index is `>=
/// pre_len` the target is THIS loop or one of our inner nested loops
/// (its params are managed by its own `emit_while`); we skip those.
/// Otherwise the target is an enclosing loop, at level
/// `level - stack_len_offset` from us.
fn collect_term_resolutions(
    s: &super::ir_translation::Structure,
    stack_len_offset: i32,
    out: &mut Vec<(usize, bool)>,
) {
    use super::ir_translation::Structure;
    use super::skeleton_recovery::Termination;
    match s {
        Structure::Leaf { termination, .. } => match termination {
            Some(Termination::Continue { level }) | Some(Termination::Break { level }) => {
                let lvl = *level as i32;
                let resolved_offset = stack_len_offset - 1 - lvl;
                if resolved_offset < 0 {
                    let enc_level = (-resolved_offset - 1) as usize;
                    let is_break = matches!(termination, Some(Termination::Break { .. }));
                    out.push((enc_level, is_break));
                }
            }
            _ => {}
        },
        Structure::If {
            then_branch,
            else_branch,
            continuation,
            ..
        } => {
            collect_term_resolutions(then_branch, stack_len_offset, out);
            collect_term_resolutions(else_branch, stack_len_offset, out);
            if let Some(c) = continuation {
                collect_term_resolutions(c, stack_len_offset, out);
            }
        }
        Structure::While {
            loop_body,
            continuation,
            ..
        } => {
            collect_term_resolutions(loop_body, stack_len_offset + 1, out);
            if let Some(c) = continuation {
                collect_term_resolutions(c, stack_len_offset, out);
            }
        }
        Structure::Switch {
            cases,
            continuation,
            ..
        } => {
            for case in cases {
                collect_term_resolutions(case, stack_len_offset, out);
            }
            if let Some(c) = continuation {
                collect_term_resolutions(c, stack_len_offset, out);
            }
        }
    }
}

/// Compute the set of bindings that are GUARANTEED in scope at every
/// `Break` leaf targeting THIS loop. Walks `loop_body` accumulating an
/// in-set of bindings along each path; at every Break leaf whose
/// `level` equals our nesting depth (so it targets us), records the
/// path-local in-set; finally intersects all snapshots.
///
/// Tighter than `collect_structure_bindings`, which unions bindings
/// across every leaf — including branch-local ones that aren't visible
/// from sibling Break leaves. The intersection rules out vars bound
/// only in arms that don't reach a Break.
///
/// Returns the empty set if no Break leaf targets this loop (e.g. an
/// infinite loop, or every exit goes through Return/Abort) — which is
/// safe because `after_func` is then never invoked, and adding zero
/// extras keeps `conv.free_vars()` honest about what's actually
/// reachable.
fn collect_break_safe_bindings(
    loop_body: &super::ir_translation::Structure,
) -> std::collections::BTreeSet<intermediate_theorem_format::data::types::TempId> {
    let mut snapshots: Vec<
        std::collections::BTreeSet<intermediate_theorem_format::data::types::TempId>,
    > = Vec::new();
    let in_set = std::collections::BTreeSet::new();
    walk_break_paths(loop_body, 0, &in_set, &mut snapshots);
    if snapshots.is_empty() {
        return std::collections::BTreeSet::new();
    }
    let mut iter = snapshots.into_iter();
    let mut acc = iter.next().unwrap();
    for s in iter {
        acc = acc.intersection(&s).cloned().collect();
    }
    acc
}

/// Recursive walker for `collect_break_safe_bindings`. `depth` is the
/// number of nested While layers between us (the loop computing
/// `after_params`) and the current node; a `Break { level }` matches
/// us iff `level == depth`. Cross-level Breaks at deeper levels are
/// ignored — they're not call sites for our after_func.
fn walk_break_paths(
    s: &super::ir_translation::Structure,
    depth: usize,
    in_set: &std::collections::BTreeSet<intermediate_theorem_format::data::types::TempId>,
    snapshots: &mut Vec<
        std::collections::BTreeSet<intermediate_theorem_format::data::types::TempId>,
    >,
) {
    use super::ir_translation::Structure;
    use super::skeleton_recovery::Termination;
    match s {
        Structure::Leaf { body, termination } => {
            let mut local = in_set.clone();
            local.extend(body.bindings());
            if let Some(Termination::Break { level }) = termination {
                if *level == depth {
                    snapshots.push(local);
                }
            }
        }
        Structure::If {
            body,
            then_branch,
            else_branch,
            continuation,
            ..
        } => {
            let mut local = in_set.clone();
            local.extend(body.bindings());
            walk_break_paths(then_branch, depth, &local, snapshots);
            walk_break_paths(else_branch, depth, &local, snapshots);
            if let Some(cont) = continuation {
                // Branch-local bindings don't flow into the continuation
                // (the continuation runs after one of the branches falls
                // through, but each branch's bindings are scoped to it).
                // Use the post-body in-set without branch additions.
                walk_break_paths(cont, depth, &local, snapshots);
            }
        }
        Structure::While {
            body,
            loop_body,
            continuation,
        } => {
            let mut local = in_set.clone();
            local.extend(body.bindings());
            // Descend into the nested loop with depth+1 — Breaks inside
            // it that target US carry `level == depth + (their depth)`,
            // and we recover that by passing depth+1 here.
            walk_break_paths(loop_body, depth + 1, &local, snapshots);
            if let Some(cont) = continuation {
                // Continuation runs after the nested loop exits. From
                // our perspective we're still at `depth`. Bindings from
                // the nested loop_body don't escape (after_func extras
                // are the nested loop's concern, handled in its own
                // emit_while), so the in-set we pass is just `local`.
                walk_break_paths(cont, depth, &local, snapshots);
            }
        }
        Structure::Switch {
            body,
            cases,
            continuation,
            ..
        } => {
            let mut local = in_set.clone();
            local.extend(body.bindings());
            for case in cases {
                walk_break_paths(case, depth, &local, snapshots);
            }
            if let Some(cont) = continuation {
                walk_break_paths(cont, depth, &local, snapshots);
            }
        }
    }
}
