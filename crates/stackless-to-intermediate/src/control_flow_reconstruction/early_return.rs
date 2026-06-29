// Copyright (c) Asymptotic
// SPDX-License-Identifier: Apache-2.0

//! Early Return Handling
//!
//! Walks the Structure tree and emits a single IRNode, handling early returns
//! by restructuring so every path is a complete, straight-line computation.
//!
//! Called once for the body side (EmitMode::Body) and once for the aborts side
//! (EmitMode::Aborts). Each pass has its own EmitContext with independent scope
//! and while loop state.

use super::ir_translation::Structure;
use super::loop_handling;
use super::phi_detection;
use super::skeleton_recovery::Termination;
use super::{does_abort, no_abort, EmitContext, EmitMode};
use intermediate_theorem_format::data::types::TempId;
use intermediate_theorem_format::IRNode;
use std::collections::BTreeSet;

/// Emit a single IRNode from a Structure tree.
pub fn emit(ctx: &mut EmitContext, structure: &Structure) -> IRNode {
    match structure {
        Structure::Leaf { body, termination } => emit_leaf(ctx, body, termination.as_ref()),

        Structure::If {
            body,
            cond,
            then_branch,
            else_branch,
            continuation,
        } => emit_if(
            ctx,
            body,
            cond,
            then_branch,
            else_branch,
            continuation.as_deref(),
        ),

        Structure::While {
            body,
            loop_body,
            continuation,
        } => loop_handling::emit_while(ctx, body, loop_body, continuation.as_deref()),

        Structure::Switch {
            body,
            scrutinee,
            cases,
            continuation,
        } => emit_switch(ctx, body, scrutinee, cases, continuation.as_deref()),
    }
}

fn emit_leaf(ctx: &mut EmitContext, body: &IRNode, termination: Option<&Termination>) -> IRNode {
    ctx.extend_scope(body);
    match termination {
        Some(Termination::Return) => match ctx.mode {
            EmitMode::Body => body.clone(),
            EmitMode::Aborts => IRNode::assign(body.clone(), no_abort()),
        },
        Some(Termination::Abort { code }) => match ctx.mode {
            EmitMode::Body => IRNode::assign(
                body.clone(),
                IRNode::Abort {
                    code: code.clone().map(Box::new),
                },
            ),
            EmitMode::Aborts => IRNode::assign(body.clone(), does_abort()),
        },
        Some(Termination::Continue { level }) => loop_handling::emit_continue(ctx, *level, body),
        Some(Termination::Break { level }) => loop_handling::emit_break(ctx, *level, body),
        None => match ctx.mode {
            EmitMode::Body => body.clone(),
            EmitMode::Aborts => IRNode::assign(body.clone(), no_abort()),
        },
    }
}

/// Build `assign(body, If(cond, then_ir, else_ir))` — the standard
/// "wrap branches in an If, prepend body" closer used by every
/// non-phi-merge path through `emit_if`.
fn finish_if(body: &IRNode, cond: &IRNode, then_ir: IRNode, else_ir: IRNode) -> IRNode {
    let if_node = IRNode::If {
        cond: Box::new(cond.clone()),
        then_branch: Box::new(then_ir),
        else_branch: Box::new(else_ir),
    };
    IRNode::assign(body.clone(), if_node)
}

/// Emit the optional continuation, falling back to a mode-appropriate
/// no-op tail when there is no continuation block. In `Body` mode the
/// fallback is `unit()`; in `Aborts` mode it is `no_abort()`. Used by
/// every emit path that needs to splice a continuation onto a branch.
fn default_continuation(ctx: &mut EmitContext, continuation: Option<&Structure>) -> IRNode {
    continuation
        .map(|c| emit(ctx, c))
        .unwrap_or_else(|| match ctx.mode {
            EmitMode::Body => IRNode::unit(),
            EmitMode::Aborts => no_abort(),
        })
}

/// Body-mode prune: if exactly one of the branches always aborts and we
/// aren't preserving abort branches (the Test face does), drop the
/// aborting branch entirely and emit `assign(body, assign(other_branch,
/// continuation))`. The aborts pass already captures the abort
/// condition, so the body pass doesn't need to re-emit it.
///
/// Returns `Some(ir)` when the prune fired; `None` otherwise — the
/// caller must fall through to the normal If shape.
fn try_abort_prune_if(
    ctx: &mut EmitContext,
    body: &IRNode,
    then_branch: &Structure,
    else_branch: &Structure,
    continuation: Option<&Structure>,
    scope_after_body: &BTreeSet<TempId>,
) -> Option<IRNode> {
    if !matches!(ctx.mode, EmitMode::Body) || ctx.preserve_aborts {
        return None;
    }
    let then_aborts = then_branch.always_aborts();
    let else_aborts = else_branch.always_aborts();
    let surviving = match (then_aborts, else_aborts) {
        (true, false) => else_branch,
        (false, true) => then_branch,
        // (false, false): nothing to prune. (true, true): function is
        // abort-only; let the normal path emit a placeholder.
        _ => return None,
    };
    let surviving_ir = emit(ctx, surviving);
    ctx.restore_scope(scope_after_body.clone());
    let conv = continuation
        .map(|c| emit(ctx, c))
        .unwrap_or_else(IRNode::unit);
    Some(IRNode::assign(
        body.clone(),
        IRNode::assign(surviving_ir, conv),
    ))
}

fn emit_if(
    ctx: &mut EmitContext,
    body: &IRNode,
    cond: &IRNode,
    then_branch: &Structure,
    else_branch: &Structure,
    continuation: Option<&Structure>,
) -> IRNode {
    ctx.extend_scope(body);
    // Save scope after body bindings but before branches — branches must
    // not leak their bindings into each other, into the continuation,
    // or into the caller's scope.
    let scope_after_body = ctx.save_scope();

    if let Some(pruned) = try_abort_prune_if(
        ctx,
        body,
        then_branch,
        else_branch,
        continuation,
        &scope_after_body,
    ) {
        return pruned;
    }

    let then_returns = then_branch.always_returns();
    let else_returns = else_branch.always_returns();

    // Case 4: neither branch fully returns. With a continuation we phi-
    // merge the branches' definitions (different IR shape); without one
    // we just emit a bare If.
    if !then_returns && !else_returns {
        ctx.restore_scope(scope_after_body.clone());
        let then_ir = emit(ctx, then_branch);
        ctx.restore_scope(scope_after_body.clone());
        let else_ir = emit(ctx, else_branch);
        return match continuation {
            Some(cont) => {
                // Compute phi variables from the emitted branches, add
                // them to scope, then emit the continuation so it can
                // see them (e.g., in while-loop parameter lists).
                let phi_vars =
                    phi_detection::compute_if_phi_vars(cond, &then_ir, &else_ir, &scope_after_body);
                ctx.restore_scope(scope_after_body.clone());
                for v in &phi_vars {
                    ctx.extend_scope_var(v.clone());
                }
                let conv = emit(ctx, cont);
                let result = phi_detection::detect_if_phis(
                    cond.clone(),
                    then_ir,
                    else_ir,
                    conv,
                    &scope_after_body,
                );
                IRNode::assign(body.clone(), result)
            }
            None => finish_if(body, cond, then_ir, else_ir),
        };
    }

    // Cases 1, 2, 3: at least one branch always returns. Emit both
    // branches; if exactly one falls through, splice the continuation
    // (or its mode-appropriate fallback) onto that branch's tail.
    ctx.restore_scope(scope_after_body.clone());
    let mut then_ir = emit(ctx, then_branch);
    ctx.restore_scope(scope_after_body.clone());
    let mut else_ir = emit(ctx, else_branch);

    if !then_returns || !else_returns {
        ctx.restore_scope(scope_after_body);
        let conv = default_continuation(ctx, continuation);
        if !then_returns {
            then_ir = IRNode::assign(then_ir, conv.clone());
        }
        if !else_returns {
            else_ir = IRNode::assign(else_ir, conv);
        }
    }

    finish_if(body, cond, then_ir, else_ir)
}

fn emit_switch(
    ctx: &mut EmitContext,
    body: &IRNode,
    scrutinee: &IRNode,
    cases: &[Structure],
    continuation: Option<&Structure>,
) -> IRNode {
    ctx.extend_scope(body);

    // Save scope after body bindings — cases must not leak into each other.
    let scope_after_body = ctx.save_scope();

    let conv = default_continuation(ctx, continuation);

    let match_cases: Vec<(
        usize,
        Vec<intermediate_theorem_format::data::types::TempId>,
        IRNode,
    )> = cases
        .iter()
        .enumerate()
        .map(|(i, case)| {
            ctx.restore_scope(scope_after_body.clone());
            (i, vec![], emit(ctx, case))
        })
        .collect();

    // Restore scope so case bindings don't leak to the caller.
    ctx.restore_scope(scope_after_body.clone());

    if continuation.is_some() {
        let result = phi_detection::detect_match_phis(
            scrutinee.clone(),
            match_cases,
            conv,
            &scope_after_body,
        );
        IRNode::assign(body.clone(), result)
    } else {
        let match_node = IRNode::Match {
            scrutinee: Box::new(scrutinee.clone()),
            cases: match_cases,
        };
        IRNode::assign(body.clone(), match_node)
    }
}
