// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Dead code removal pass
//!
//! Removes Let statements where the bound variables are never used.
//! Preserves side-effecting expressions (function calls, etc.) even if unused.

use crate::data::types::TempId;
use crate::IRNode;
use std::collections::BTreeSet;
use std::rc::Rc;

pub fn remove_dead_code(ir: IRNode) -> IRNode {
    let used: BTreeSet<TempId> = ir.used_vars().cloned().collect();
    let ir = remove_dead_lets(ir, &used);
    // Also simplify tuple patterns by replacing unused vars with "_"
    simplify_tuple_patterns(ir, &used)
}

/// Remove dead let bindings from the IR tree
fn remove_dead_lets(ir: IRNode, used: &BTreeSet<TempId>) -> IRNode {
    ir.map(&mut |node| {
        if is_dead_let(&node, used) {
            if let IRNode::Let { body, .. } = node {
                return *body;
            }
        }
        node
    })
}

/// Simplify tuple patterns by replacing unused variables with "_"
/// This transforms `let (a, b, c) := ...` to `let (_, _, c) := ...` if only c is used
pub fn simplify_tuple_patterns(ir: IRNode, used: &BTreeSet<TempId>) -> IRNode {
    ir.map(&mut |node| match node {
        IRNode::Let {
            pattern,
            value,
            body,
        } if pattern.len() > 1 => {
            // For multi-element patterns, replace unused vars with "_"
            let simplified_pattern: Vec<_> = pattern
                .into_iter()
                .map(|v| if used.contains(&v) { v } else { Rc::from("_") })
                .collect();
            IRNode::Let {
                pattern: simplified_pattern,
                value,
                body,
            }
        }
        other => other,
    })
}

fn is_dead_let(ir: &IRNode, used: &BTreeSet<TempId>) -> bool {
    let IRNode::Let { pattern, value, .. } = ir else {
        return false;
    };
    // Only remove Let bindings where:
    // 1. None of the pattern variables are used
    // 2. The value has no side effects (no function calls that could abort or mutate)
    // For now, conservatively: only remove pure expressions
    pattern.iter().all(|n| !used.contains(n)) && is_pure(value)
}

/// Check if an expression is pure (no side effects)
fn is_pure(ir: &IRNode) -> bool {
    match ir {
        IRNode::Var(_) | IRNode::Const(_) => true,
        IRNode::BinOp { lhs, rhs, .. } => is_pure(lhs) && is_pure(rhs),
        IRNode::UnOp { operand, .. } => is_pure(operand),
        IRNode::Tuple(elems) => elems.iter().all(is_pure),
        IRNode::Field { base, .. } => is_pure(base),
        // Function calls are never pure — they may abort, mutate, or have other side effects
        IRNode::Call { .. } => false,
        // Everything else potentially has side effects
        _ => false,
    }
}
