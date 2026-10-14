// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Deep nesting flattening pass for TheoremIR
//!
//! This pass addresses Lean's maximum recursion depth limits by flattening
//! deeply nested conditional expressions. The primary pattern is:
//!
//! ```
//! let tmp__t_30 := (if cond1 then result1 else false)
//! let t_t518 := tmp__t_30
//! if t_t518 then
//!   true
//! else
//!   let tmp__t_27 := (if cond2 then result2 else false)
//!   ...  // deeply nested
//! ```
//!
//! This pattern arises from Move's short-circuit boolean evaluation being
//! translated literally into nested if-expressions.
//!
//! The transformation flattens this into:
//! ```
//! cond1 && result1 || (!cond1 && (cond2 && result2 || ...))
//! ```
//!
//! Or more practically, we use a helper function approach to reduce nesting.

use crate::{BinOp, Const, IRNode};
use std::rc::Rc;

/// Maximum depth of if-nesting before we apply flattening
const MAX_IF_DEPTH: usize = 15;

/// Flatten deeply nested conditionals to avoid Lean's recursion depth limits.
pub fn flatten_deep_nesting(node: IRNode) -> IRNode {
    let depth = measure_if_depth(&node);
    if depth > MAX_IF_DEPTH {
        flatten_deep_ifs(node)
    } else {
        node
    }
}

/// Measure the maximum depth of nested if-expressions
fn measure_if_depth(node: &IRNode) -> usize {
    measure_if_depth_inner(node, 0)
}

fn measure_if_depth_inner(node: &IRNode, current_depth: usize) -> usize {
    match node {
        IRNode::If {
            then_branch,
            else_branch,
            ..
        } => {
            let then_depth = measure_if_depth_inner(then_branch, current_depth + 1);
            let else_depth = measure_if_depth_inner(else_branch, current_depth + 1);
            then_depth.max(else_depth)
        }
        IRNode::Let { value, body, .. } => {
            let value_depth = measure_if_depth_inner(value, current_depth);
            let body_depth = measure_if_depth_inner(body, current_depth);
            value_depth.max(body_depth)
        }
        _ => current_depth,
    }
}

/// Flatten deeply nested if-then-true-else chains into AND expressions.
///
/// Pattern detected:
/// ```
/// if cond then true else REST
/// ```
/// Where REST is another if-then-true-else chain.
///
/// Transformed to:
/// ```
/// !cond && REST_transformed
/// ```
/// or using De Morgan's laws to keep it readable.
fn flatten_deep_ifs(node: IRNode) -> IRNode {
    // First, try to extract a chain of conditions that lead to `true`
    let mut conditions = Vec::new();
    let final_else = collect_if_true_else_chain(&node, &mut conditions);

    if conditions.len() > 3 {
        // We have a significant chain - flatten it
        // The semantics are: if any condition is true, return true
        // Otherwise return the final else value
        build_or_chain(conditions, final_else)
    } else {
        // Not enough to flatten, just recurse normally
        node.map(&mut |n| {
            if let IRNode::If {
                cond,
                then_branch,
                else_branch,
            } = &n
            {
                let new_then = flatten_deep_ifs((**then_branch).clone());
                let new_else = flatten_deep_ifs((**else_branch).clone());
                IRNode::If {
                    cond: cond.clone(),
                    then_branch: Box::new(new_then),
                    else_branch: Box::new(new_else),
                }
            } else {
                n
            }
        })
    }
}

/// Collect conditions from a chain of `if cond then true else ...` patterns.
/// Also handles wrapped versions with Let bindings.
///
/// Returns the final else branch (what happens when all conditions are false).
fn collect_if_true_else_chain(node: &IRNode, conditions: &mut Vec<IRNode>) -> IRNode {
    match node {
        // Direct pattern: if cond then true else rest
        IRNode::If {
            cond,
            then_branch,
            else_branch,
        } => {
            if is_true_const(then_branch) {
                conditions.push((**cond).clone());
                collect_if_true_else_chain(else_branch, conditions)
            } else if is_true_const(else_branch) {
                // Pattern: if cond then rest else true
                // This means: !cond => true, so we add !cond as a condition
                conditions.push(IRNode::UnOp {
                    op: crate::UnOp::Not,
                    operand: cond.clone(),
                });
                collect_if_true_else_chain(then_branch, conditions)
            } else {
                // Not a pattern we can flatten at this level
                node.clone()
            }
        }
        // Pattern with Let wrapping: let tmp := (if ...) in let x := tmp in if x then true else ...
        IRNode::Let {
            pattern,
            value,
            body,
        } => {
            // Check if value is an if-expression that we should look through
            if let IRNode::If { .. } = value.as_ref() {
                // Try to find where this pattern variable is used as a condition
                if pattern.len() == 1 {
                    let var_name = &pattern[0];
                    if let Some(unwrapped) = unwrap_let_if_pattern(body, var_name, value) {
                        return collect_if_true_else_chain(&unwrapped, conditions);
                    }
                }
            }
            // Try to collect from the body
            let new_body = collect_if_true_else_chain(body, conditions);
            if conditions.is_empty() {
                node.clone()
            } else {
                IRNode::Let {
                    pattern: pattern.clone(),
                    value: value.clone(),
                    body: Box::new(new_body),
                }
            }
        }
        _ => node.clone(),
    }
}

/// Check if a node is the constant `true`
fn is_true_const(node: &IRNode) -> bool {
    match node {
        IRNode::Const(Const::Bool(true)) => true,
        IRNode::Let { body, .. } => is_true_const(body),
        _ => false,
    }
}

/// Try to unwrap a pattern like:
/// ```
/// let x := tmp_var
/// let _ := ()
/// if x then true else REST
/// ```
/// Returns the restructured if-expression using the original value.
fn unwrap_let_if_pattern(
    body: &IRNode,
    var_name: &Rc<str>,
    original_value: &IRNode,
) -> Option<IRNode> {
    match body {
        IRNode::Let {
            pattern,
            value,
            body: inner_body,
        } => {
            // Check if this is `let x := var_name`
            if pattern.len() == 1 {
                if let IRNode::Var(v) = value.as_ref() {
                    if v.as_ref() == var_name.as_ref() {
                        // Found `let x := var_name`, now look for `if x then true else ...`
                        return unwrap_let_if_pattern(inner_body, &pattern[0], original_value);
                    }
                }
            }
            // Check for `let _ := ()` (unit sequencing)
            if pattern.is_empty() || (pattern.len() == 1 && pattern[0].as_ref() == "_") {
                if matches!(value.as_ref(), IRNode::Tuple(v) if v.is_empty()) {
                    return unwrap_let_if_pattern(inner_body, var_name, original_value);
                }
            }
            None
        }
        IRNode::If {
            cond,
            then_branch,
            else_branch,
        } => {
            // Check if cond is the variable we're tracking
            if let IRNode::Var(v) = cond.as_ref() {
                if v.as_ref() == var_name.as_ref() {
                    // Found `if var_name then ... else ...`
                    // Replace with `if original_value then ... else ...`
                    return Some(IRNode::If {
                        cond: Box::new(original_value.clone()),
                        then_branch: then_branch.clone(),
                        else_branch: else_branch.clone(),
                    });
                }
            }
            None
        }
        _ => None,
    }
}

/// Build an OR chain from conditions: cond1 || cond2 || ... || final_else
fn build_or_chain(conditions: Vec<IRNode>, final_else: IRNode) -> IRNode {
    if conditions.is_empty() {
        return final_else;
    }

    // Build: cond1 || (cond2 || (cond3 || ... || final_else))
    // But we want to limit nesting, so we'll chunk them
    const CHUNK_SIZE: usize = 4;

    if conditions.len() <= CHUNK_SIZE {
        // Small enough to just chain directly
        let mut result = final_else;
        for cond in conditions.into_iter().rev() {
            result = IRNode::BinOp {
                op: BinOp::Or,
                lhs: Box::new(cond),
                rhs: Box::new(result),
            };
        }
        result
    } else {
        // Split into chunks and combine
        let chunks: Vec<Vec<IRNode>> = conditions.chunks(CHUNK_SIZE).map(|c| c.to_vec()).collect();

        // Build each chunk as an OR, then combine the chunks
        let chunk_ors: Vec<IRNode> = chunks
            .into_iter()
            .map(|chunk| {
                let mut result = IRNode::Const(Const::Bool(false));
                for cond in chunk.into_iter().rev() {
                    result = IRNode::BinOp {
                        op: BinOp::Or,
                        lhs: Box::new(cond),
                        rhs: Box::new(result),
                    };
                }
                result
            })
            .collect();

        // Combine all chunk ORs with the final else
        let mut result = final_else;
        for chunk_or in chunk_ors.into_iter().rev() {
            result = IRNode::BinOp {
                op: BinOp::Or,
                lhs: Box::new(chunk_or),
                rhs: Box::new(result),
            };
        }
        result
    }
}
