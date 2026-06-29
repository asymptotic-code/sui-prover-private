// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Temp inlining pass
//!
//! Inlines generated temporaries (variables starting with $) using a simple
//! sequential forward substitution approach:
//!
//! 1. Process statements in order
//! 2. When we see `let $t = value`, substitute any known temps in `value`,
//!    store the result in our map, and remove the let
//! 3. When we see a variable reference to a known temp, replace it with the stored value
//!
//! This approach is safe because:
//! - We only substitute temps we've already seen (no forward references)
//! - Each temp's value is fully expanded when stored (no fixpoint needed)
//! - No recursion on definitions (just map lookup + tree substitution)

use crate::data::types::TempId;
use crate::{IRNode, VariableRegistry};
use std::collections::BTreeMap;

/// Inline all temps in the given IR.
pub fn inline_temps(ir: IRNode, _registry: &VariableRegistry) -> IRNode {
    inline_in_node(ir, &BTreeMap::new(), false)
}

/// Inline temps for an `.aborts` body. Same as `inline_temps`, but ALSO inlines
/// multi-use single-`Var`-pattern temps (the normal pass keeps those as `let`s to
/// avoid rendered-text duplication). An `.aborts` body is a `Bool` expression that is
/// only ever *proved*, never *computed*, so duplicating a sub-expression costs nothing
/// at runtime — whereas a `let`-binding of a heavy `BoundedNat` sub-expression blocks
/// the kernel-cheap `conv`-localized proof technique (a rewrite lemma can't match a
/// subterm bound under a `let`, and zeta-reducing the `let` re-materialises the heavy
/// term and triggers `(kernel) deep recursion`). Writeback/mutable constructs are still
/// kept as `let`s (inlining them would orphan their TempId references).
/// See CLAUDE.md "Kernel deep-recursion on heavy `BoundedNat` obligations".
pub fn inline_temps_aborts(ir: IRNode) -> IRNode {
    inline_in_node(ir, &BTreeMap::new(), true)
}

/// Inline all temps in the given IR (version without registry for pre-phi-detection use).
pub fn inline_temps_simple(ir: IRNode) -> IRNode {
    inline_in_node(ir, &BTreeMap::new(), false)
}

/// Copy propagation pass: only propagates variable-to-variable assignments.
/// This is safer for pre-phi-detection use as it doesn't change the semantic structure,
/// just eliminates SSA copy chains like `let $t2 = $t1; use($t2)` -> `use($t1)`.
pub fn propagate_copies(ir: IRNode) -> IRNode {
    propagate_copies_inner(ir, &BTreeMap::new())
}

fn propagate_copies_inner(ir: IRNode, copies: &BTreeMap<TempId, TempId>) -> IRNode {
    match ir {
        IRNode::Var(name) => {
            // If this var is a copy of another, replace with the original
            if let Some(original) = copies.get(&name) {
                IRNode::Var(original.clone())
            } else {
                IRNode::Var(name)
            }
        }
        IRNode::Let {
            pattern,
            value,
            body,
        } => {
            // First substitute copies in the value
            let value = propagate_copies_inner(*value, copies);

            // Check if this is a simple copy: let $temp = $other_var
            if is_single_temp(&pattern) {
                if let IRNode::Var(src) = &value {
                    let original = copies.get(src).cloned().unwrap_or_else(|| src.clone());
                    // Don't propagate if the source variable is rebound in the body —
                    // replacing uses of $temp with the source after a rebinding would
                    // change semantics (snapshot vs live value).
                    if !is_rebound_in(original.as_ref(), &body) {
                        let mut new_copies = copies.clone();
                        new_copies.insert(pattern[0].clone(), original);
                        return propagate_copies_inner(*body, &new_copies);
                    }
                }
            }

            // Not a copy - keep the let but propagate in body
            let body = propagate_copies_inner(*body, copies);
            IRNode::Let {
                pattern,
                value: Box::new(value),
                body: Box::new(body),
            }
        }
        IRNode::If {
            cond,
            then_branch,
            else_branch,
        } => {
            let cond = propagate_copies_inner(*cond, copies);
            // Process branches with current copy map (copies don't flow across branches)
            let then_branch = propagate_copies_inner(*then_branch, copies);
            let else_branch = propagate_copies_inner(*else_branch, copies);
            IRNode::If {
                cond: Box::new(cond),
                then_branch: Box::new(then_branch),
                else_branch: Box::new(else_branch),
            }
        }
        IRNode::Match { scrutinee, cases } => {
            let scrutinee = propagate_copies_inner(*scrutinee, copies);
            let cases = cases
                .into_iter()
                .map(|(idx, bindings, body)| (idx, bindings, propagate_copies_inner(body, copies)))
                .collect();
            IRNode::Match {
                scrutinee: Box::new(scrutinee),
                cases,
            }
        }
        // For other nodes, recursively apply to children
        other => other.map(&mut |node| {
            if let IRNode::Var(name) = &node {
                if let Some(original) = copies.get(name) {
                    return IRNode::Var(original.clone());
                }
            }
            if let IRNode::WriteBack {
                ref child,
                ref parent,
                ref edge,
            } = node
            {
                let new_child = copies.get(child).cloned().unwrap_or_else(|| child.clone());
                let new_parent = copies
                    .get(parent)
                    .cloned()
                    .unwrap_or_else(|| parent.clone());
                if new_child != *child || new_parent != *parent {
                    return IRNode::WriteBack {
                        child: new_child,
                        parent: new_parent,
                        edge: edge.clone(),
                    };
                }
            }
            node
        }),
    }
}

/// Substitute known temps in an IR node (non-recursive on definitions)
fn substitute_temps(ir: IRNode, temps: &BTreeMap<TempId, IRNode>) -> IRNode {
    ir.map(&mut |node| {
        if let IRNode::Var(name) = &node {
            return temps.get(name).cloned().unwrap_or(node);
        }
        if let IRNode::WriteBack {
            ref child,
            ref parent,
            ref edge,
        } = node
        {
            let new_child = if let Some(IRNode::Var(c)) = temps.get(child) {
                c.clone()
            } else {
                child.clone()
            };
            let new_parent = if let Some(IRNode::Var(p)) = temps.get(parent) {
                p.clone()
            } else {
                parent.clone()
            };
            if new_child != *child || new_parent != *parent {
                return IRNode::WriteBack {
                    child: new_child,
                    parent: new_parent,
                    edge: edge.clone(),
                };
            }
        }
        node
    })
}

/// Process a node, inlining temps. `temps` contains temps defined in outer scopes.
fn inline_in_node(ir: IRNode, outer_temps: &BTreeMap<TempId, IRNode>, aborts: bool) -> IRNode {
    match ir {
        IRNode::Let {
            pattern,
            value,
            body,
        } => {
            // Substitute temps in the value
            let value = substitute_temps(*value, outer_temps);

            // If this is a single temp pattern, try to inline it
            if is_single_temp(&pattern) {
                let temp_name = &pattern[0];

                // Count effective uses: how many times this temp's value will
                // appear in the rendered output.
                let use_count = count_effective_uses(&body, temp_name.as_ref());

                // WriteBack/MutableCompose store child/parent as TempId strings.
                // Inlining a non-Var value into them is impossible — `substitute_temps`
                // only rewrites the string when the inlined value is itself a `Var`,
                // so a Field/Call/etc. value would orphan the WriteBack reference.
                let used_in_writeback_or_compose = !matches!(value, IRNode::Var(_))
                    && is_used_in_writeback_or_compose(&body, temp_name.as_ref());

                // In `.aborts` mode we relax the multi-use keep-rule: a `Bool`
                // abort-expression is only proved, never computed, so duplicating a
                // sub-expression is free, while a `let` of a heavy `BoundedNat` term
                // blocks the kernel-cheap `conv`-localized proof. Writeback/mutable and
                // rebinding guards still apply (soundness, not text-size).
                let multi_use_block = if aborts {
                    false
                } else {
                    use_count > 1 && !value.is_atomic()
                };

                if (use_count == 0
                    && !value.is_atomic()
                    && !matches!(value, IRNode::Tuple(_) | IRNode::Const(_)))
                    || multi_use_block
                    || value_vars_rebound_in_body(&value, &body)
                    || used_in_writeback_or_compose
                    || matches!(
                        value,
                        IRNode::WriteRef { .. }
                            | IRNode::WriteBack { .. }
                            | IRNode::MutableBorrow { .. }
                            | IRNode::MutableCompose { .. }
                    )
                {
                    // Keep as a let binding — don't inline.
                    // The rebinding check prevents unsound inlining when the value
                    // references a variable that gets rebound later in the body
                    // (e.g. mutable threading rebinds `table := __mut_ret_0`).
                    let body = inline_in_node(*body, outer_temps, aborts);
                    IRNode::Let {
                        pattern,
                        value: Box::new(value),
                        body: Box::new(body),
                    }
                } else {
                    // Single use or atomic — inline
                    let mut new_temps = outer_temps.clone();
                    new_temps.insert(pattern[0].clone(), value);
                    inline_in_node(*body, &new_temps, aborts)
                }
            } else {
                // Non-temp let - substitute temps in value and keep
                let body = inline_in_node(*body, outer_temps, aborts);
                IRNode::Let {
                    pattern,
                    value: Box::new(value),
                    body: Box::new(body),
                }
            }
        }
        IRNode::If {
            cond,
            then_branch,
            else_branch,
        } => {
            // Substitute temps in condition
            let cond = substitute_temps(*cond, outer_temps);
            // Process branches with outer temps (branches may define new temps locally)
            let then_branch = inline_in_node(*then_branch, outer_temps, aborts);
            let else_branch = inline_in_node(*else_branch, outer_temps, aborts);
            IRNode::If {
                cond: Box::new(cond),
                then_branch: Box::new(then_branch),
                else_branch: Box::new(else_branch),
            }
        }
        // For BinOp, recurse into operands (they may contain nested structures)
        IRNode::BinOp { op, lhs, rhs } => {
            let lhs = inline_in_node(*lhs, outer_temps, aborts);
            let rhs = inline_in_node(*rhs, outer_temps, aborts);
            IRNode::BinOp {
                op,
                lhs: Box::new(lhs),
                rhs: Box::new(rhs),
            }
        }
        // For UnOp, recurse into operand
        IRNode::UnOp { op, operand } => {
            let operand = inline_in_node(*operand, outer_temps, aborts);
            IRNode::UnOp {
                op,
                operand: Box::new(operand),
            }
        }
        // For Call, recurse into args
        IRNode::Call {
            function,
            type_args,
            args,
        } => {
            let args = args
                .into_iter()
                .map(|a| inline_in_node(a, outer_temps, aborts))
                .collect();
            IRNode::Call {
                function,
                type_args,
                args,
            }
        }
        // For other nodes, just substitute temps in all children
        other => substitute_temps(other, outer_temps),
    }
}

/// Count how many times a variable will effectively appear in the rendered output.
///
/// This goes beyond a simple Var count: when a variable is inside an Unpack with
/// N fields, the renderer emits the value N times (once per field accessor).
/// Similarly, MutableBorrow contains the base in both val_expr and reconstruct_expr.
/// We account for these renderer-level duplications to avoid inlining expressions
/// that would explode line length.
fn count_effective_uses(ir: &IRNode, name: &str) -> usize {
    count_effective_uses_inner(ir, name, 1)
}

fn count_effective_uses_inner(ir: &IRNode, name: &str, multiplier: usize) -> usize {
    match ir {
        IRNode::Var(v) if v.as_ref() == name => multiplier,
        IRNode::Var(_) | IRNode::Const(_) => 0,
        IRNode::Tuple(elems) if elems.is_empty() => 0,
        IRNode::Unpack {
            value, struct_id, ..
        } => {
            // The renderer emits the value once per field, so we need
            // to know the field count. But we don't have the Program here.
            // Instead, use a simple heuristic: Unpack always duplicates,
            // so treat any non-trivial value inside Unpack as multi-use.
            // We pass multiplier * 2 (conservative minimum for >1 field).
            let _ = struct_id;
            count_effective_uses_inner(value, name, multiplier * 2)
        }
        // WriteBack stores child/parent as TempId strings, not IRNode children,
        // so iter_children() doesn't see them. Count them explicitly.
        IRNode::WriteBack { child, parent, .. } => {
            let mut count = 0;
            if child.as_ref() == name {
                count += multiplier;
            }
            if parent.as_ref() == name {
                count += multiplier;
            }
            count
        }
        _ => {
            // Sum across all children
            ir.iter_children()
                .map(|child| count_effective_uses_inner(child, name, multiplier))
                .sum()
        }
    }
}

/// Check whether `name` appears as `child` or `parent` in any `WriteBack` /
/// `MutableCompose` node inside `body`. Both store temp identifiers as strings,
/// so substituting a non-`Var` value into them is impossible.
fn is_used_in_writeback_or_compose(body: &IRNode, name: &str) -> bool {
    body.iter().any(|n| match n {
        IRNode::WriteBack { child, parent, .. } => {
            child.as_ref() == name || parent.as_ref() == name
        }
        IRNode::MutableCompose { inner, outer } => inner.as_ref() == name || outer.as_ref() == name,
        _ => false,
    })
}

/// Check if pattern is a single temp variable that should be inlined
fn is_single_temp(pattern: &[TempId]) -> bool {
    if pattern.len() != 1 {
        return false;
    }

    let name = &pattern[0];

    // Only inline $ prefixed temps (true compiler temps)
    // We CANNOT inline "tmp" because it may be defined in conditional branches
    // and used after the conditional, which our scope-local inlining can't handle.
    VariableRegistry::is_temp(name.as_ref())
}

/// Check if any variable referenced in `value` is rebound (appears as a Let pattern)
/// anywhere in `body`. Inlining `let $t = x` into later uses of `$t` is unsound
/// when `x` gets rebound between the definition and the use — the inlined `x` would
/// refer to the new value instead of the snapshot at definition time.
fn value_vars_rebound_in_body(value: &IRNode, body: &IRNode) -> bool {
    let mut vars = Vec::new();
    collect_vars(value, &mut vars);
    if vars.is_empty() {
        return false;
    }
    for var in &vars {
        if is_rebound_in(var.as_ref(), body) {
            return true;
        }
    }
    false
}

fn collect_vars(node: &IRNode, out: &mut Vec<TempId>) {
    match node {
        IRNode::Var(name) => out.push(name.clone()),
        other => {
            for child in other.iter_children() {
                collect_vars(child, out);
            }
        }
    }
}

fn is_rebound_in(name: &str, node: &IRNode) -> bool {
    match node {
        IRNode::Let {
            pattern,
            value,
            body,
        } => {
            if pattern.iter().any(|p| p.as_ref() == name) {
                return true;
            }
            is_rebound_in(name, value) || is_rebound_in(name, body)
        }
        IRNode::If {
            cond,
            then_branch,
            else_branch,
        } => {
            is_rebound_in(name, cond)
                || is_rebound_in(name, then_branch)
                || is_rebound_in(name, else_branch)
        }
        IRNode::Match { scrutinee, cases } => {
            is_rebound_in(name, scrutinee)
                || cases.iter().any(|(_, _, body)| is_rebound_in(name, body))
        }
        _ => false,
    }
}
