// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Early return elimination pass for TheoremIR
//!
//! Transforms early returns in sequential blocks into nested if/else chains.
//! Inside while loops, the same restructuring is applied but Return nodes are
//! preserved — the renderer handles those by emitting Option-based early return
//! patterns directly in Lean.
//!
//! Before:
//! ```text
//! Block([
//!   If { cond1, then: Return(EQ), else: Tuple([]) },
//!   If { cond2, then: Return(LT), else: Tuple([]) },
//!   final_expr
//! ])
//! ```
//!
//! After:
//! ```text
//! If { cond1, then: EQ,
//!   else: If { cond2, then: LT,
//!     else: final_expr } }
//! ```

use crate::IRNode;

/// Eliminate early returns by restructuring blocks with terminating if-branches
/// into nested if/else chains. This runs bottom-up so inner blocks are processed first.
///
/// Inside while bodies, Returns are preserved (not stripped) so the renderer can
/// detect them and emit Option-based early return patterns.
pub fn eliminate_early_returns(node: IRNode) -> IRNode {
    let node = restructure_recursive(node, false);
    let node = hoist_returns_from_while_lets(node);
    strip_tail_returns(node)
}

/// Recursively apply early return elimination (block restructuring only).
///
/// `preserve_returns`: when true (inside while bodies), don't strip Returns
/// from terminating branches during restructuring. The renderer needs them.
fn restructure_recursive(node: IRNode, preserve_returns: bool) -> IRNode {
    match node {
        IRNode::While {
            cond,
            body,
            vars,
            invariants,
        } => {
            // Restructure blocks inside while bodies but preserve Return nodes
            IRNode::While {
                cond: Box::new(restructure_recursive(*cond, preserve_returns)),
                body: Box::new(restructure_recursive(*body, true)),
                vars,
                invariants,
            }
        }
        IRNode::Block { children } => {
            // Trim dead code after Return/Abort in blocks
            let mut trimmed = Vec::new();
            for c in children {
                let terminates = c.terminates();
                trimmed.push(restructure_recursive(c, preserve_returns));
                if terminates {
                    break;
                }
            }
            restructure_block(IRNode::Block { children: trimmed }, preserve_returns)
        }
        IRNode::If {
            cond,
            then_branch,
            else_branch,
        } => {
            let node = IRNode::If {
                cond: Box::new(restructure_recursive(*cond, preserve_returns)),
                then_branch: Box::new(restructure_recursive(*then_branch, preserve_returns)),
                else_branch: Box::new(restructure_recursive(*else_branch, preserve_returns)),
            };
            restructure_block(node, preserve_returns)
        }
        IRNode::Let { pattern, value } => {
            let node = IRNode::Let {
                pattern,
                value: Box::new(restructure_recursive(*value, preserve_returns)),
            };
            restructure_block(node, preserve_returns)
        }
        IRNode::Match {
            scrutinee,
            enum_id,
            cases,
        } => {
            let cases = cases
                .into_iter()
                .map(|(idx, bindings, body)| {
                    (idx, bindings, restructure_recursive(body, preserve_returns))
                })
                .collect();
            restructure_block(
                IRNode::Match {
                    scrutinee: Box::new(restructure_recursive(*scrutinee, preserve_returns)),
                    enum_id,
                    cases,
                },
                preserve_returns,
            )
        }
        other => other,
    }
}

/// For a given node, if it's a Block, scan for If children with at least one
/// terminating branch and restructure into nested if/else chains.
///
/// When `preserve_returns` is true (inside while bodies), don't call
/// strip_tail_returns on the terminating branch.
fn restructure_block(node: IRNode, preserve_returns: bool) -> IRNode {
    let children = match node {
        IRNode::Block { children } if children.len() >= 2 => children,
        other => return other,
    };

    let early_return_idx = children.iter().position(|child| match child {
        IRNode::If {
            then_branch,
            else_branch,
            ..
        } => then_branch.terminates() || else_branch.terminates(),
        // Also check Let { value: If { ..terminates.. } }
        IRNode::Let { value, .. } => {
            if let IRNode::If {
                then_branch,
                else_branch,
                ..
            } = value.as_ref()
            {
                then_branch.terminates() || else_branch.terminates()
            } else {
                false
            }
        }
        _ => false,
    });

    let idx = match early_return_idx {
        Some(i) => i,
        None => return IRNode::Block { children },
    };

    let mut prefix: Vec<IRNode> = children[..idx].to_vec();
    let child_node = children[idx].clone();
    let rest: Vec<IRNode> = children[idx + 1..].to_vec();

    // Extract the If and optional Let pattern from the child
    let (cond, then_branch, else_branch, let_pattern) = match child_node {
        IRNode::If {
            cond,
            then_branch,
            else_branch,
        } => (cond, *then_branch, *else_branch, None),
        IRNode::Let { pattern, value } => match *value {
            IRNode::If {
                cond,
                then_branch,
                else_branch,
            } => (cond, *then_branch, *else_branch, Some(pattern)),
            _ => unreachable!(),
        },
        _ => unreachable!(),
    };

    let then_term = then_branch.terminates();
    let else_term = else_branch.terminates();

    // Helper: wrap a non-terminating branch in Let if the If was inside a Let
    let wrap_in_let = |branch: IRNode, rest: Vec<IRNode>| -> IRNode {
        let branch_with_let = if let Some(ref pat) = let_pattern {
            // Wrap: let pattern := branch; rest...
            let let_node = IRNode::Let {
                pattern: pat.clone(),
                value: Box::new(branch),
            };
            if rest.is_empty() {
                IRNode::Block {
                    children: vec![let_node],
                }
            } else {
                let mut children = vec![let_node];
                children.extend(rest);
                IRNode::Block { children }
            }
        } else if rest.is_empty() {
            branch
        } else {
            let rest_node = make_single_node(rest);
            merge_with_rest(branch, rest_node)
        };
        restructure_block(branch_with_let, preserve_returns)
    };

    // Conditionally strip tail returns from terminating branches.
    // Inside while bodies (preserve_returns=true), keep Returns intact for the renderer.
    let maybe_strip = |node: IRNode| -> IRNode {
        if preserve_returns {
            node
        } else {
            strip_tail_returns(node)
        }
    };

    let new_if = if then_term && else_term {
        // Both branches terminate — drop any dead code after, but keep Returns/Aborts
        // intact so parent blocks can still detect termination during bottom-up processing.
        // The top-level strip_tail_returns in eliminate_early_returns handles final cleanup.
        IRNode::If {
            cond,
            then_branch: Box::new(then_branch),
            else_branch: Box::new(else_branch),
        }
    } else if then_term {
        // Only then terminates — nest rest into else
        let new_else = wrap_in_let(else_branch, rest);
        IRNode::If {
            cond,
            then_branch: Box::new(maybe_strip(then_branch)),
            else_branch: Box::new(new_else),
        }
    } else {
        // Only else terminates — nest rest into then
        let new_then = wrap_in_let(then_branch, rest);
        IRNode::If {
            cond,
            then_branch: Box::new(new_then),
            else_branch: Box::new(maybe_strip(else_branch)),
        }
    };

    if prefix.is_empty() {
        new_if
    } else {
        prefix.push(new_if);
        IRNode::Block { children: prefix }
    }
}

fn make_single_node(nodes: Vec<IRNode>) -> IRNode {
    if nodes.len() == 1 {
        nodes.into_iter().next().unwrap()
    } else if nodes.is_empty() {
        IRNode::Tuple(vec![])
    } else {
        IRNode::Block { children: nodes }
    }
}

fn merge_with_rest(branch: IRNode, rest: IRNode) -> IRNode {
    match &branch {
        IRNode::Tuple(elems) if elems.is_empty() => rest,
        IRNode::Block { children } if children.is_empty() => rest,
        IRNode::Block { children } => {
            let mut merged = children.clone();
            match rest {
                IRNode::Block {
                    children: rest_children,
                } => merged.extend(rest_children),
                other => merged.push(other),
            }
            IRNode::Block { children: merged }
        }
        _ => {
            let mut merged = vec![branch];
            match rest {
                IRNode::Block {
                    children: rest_children,
                } => merged.extend(rest_children),
                other => merged.push(other),
            }
            IRNode::Block { children: merged }
        }
    }
}

/// Hoist Returns out of Let values inside While bodies.
///
/// When a While body contains `Let { pattern, value: If { ... Return ... } }`,
/// the Return is inside the Let's value expression. This causes type mismatches
/// in the renderer because the Return produces a different-shaped tuple than
/// the Let pattern expects.
///
/// This pass transforms:
/// ```text
/// Let { [a, b], value: If { cond, then: Tuple([a,b]),
///                            else: If { cond2, then: Return(x), else: Tuple([a,b]) } } }
/// rest...
/// ```
/// into:
/// ```text
/// If { cond,
///   then: Block { Let { [a,b] := Tuple([a,b]) }, rest... },
///   else: If { cond2,
///     then: Return(x),
///     else: Block { Let { [a,b] := Tuple([a,b]) }, rest... } } }
/// ```
fn hoist_returns_from_while_lets(node: IRNode) -> IRNode {
    match node {
        IRNode::While {
            cond,
            body,
            vars,
            invariants,
        } => {
            let body = hoist_returns_in_block(*body);
            let body = hoist_returns_from_while_lets(body);
            IRNode::While {
                cond: Box::new(hoist_returns_from_while_lets(*cond)),
                body: Box::new(body),
                vars,
                invariants,
            }
        }
        IRNode::Block { children } => IRNode::Block {
            children: children
                .into_iter()
                .map(hoist_returns_from_while_lets)
                .collect(),
        },
        IRNode::If {
            cond,
            then_branch,
            else_branch,
        } => IRNode::If {
            cond: Box::new(hoist_returns_from_while_lets(*cond)),
            then_branch: Box::new(hoist_returns_from_while_lets(*then_branch)),
            else_branch: Box::new(hoist_returns_from_while_lets(*else_branch)),
        },
        IRNode::Let { pattern, value } => IRNode::Let {
            pattern,
            value: Box::new(hoist_returns_from_while_lets(*value)),
        },
        IRNode::Match {
            scrutinee,
            enum_id,
            cases,
        } => IRNode::Match {
            scrutinee: Box::new(hoist_returns_from_while_lets(*scrutinee)),
            enum_id,
            cases: cases
                .into_iter()
                .map(|(idx, bindings, body)| (idx, bindings, hoist_returns_from_while_lets(body)))
                .collect(),
        },
        other => other,
    }
}

/// Check if an If tree contains any Return nodes in its branches
fn if_contains_return(node: &IRNode) -> bool {
    node.iter().any(|n| matches!(n, IRNode::Return(_)))
}

/// Process a block inside a While body, hoisting Returns out of Let values.
fn hoist_returns_in_block(node: IRNode) -> IRNode {
    let children = match node {
        IRNode::Block { children } => children,
        other => return other,
    };

    // Find a Let whose value contains a Return (value is If or Block ending in If)
    let hoist_idx = children.iter().position(|child| {
        if let IRNode::Let { value, .. } = child {
            if if_contains_return(value) {
                // The value must ultimately contain an If with a Return
                return extract_trailing_if(value).is_some();
            }
        }
        false
    });

    let idx = match hoist_idx {
        Some(i) => i,
        None => return IRNode::Block { children },
    };

    let prefix: Vec<IRNode> = children[..idx].to_vec();
    let let_node = children[idx].clone();
    let rest: Vec<IRNode> = children[idx + 1..].to_vec();

    let (pattern, value) = match let_node {
        IRNode::Let { pattern, value } => (pattern, *value),
        _ => unreachable!(),
    };

    // Extract prefix lets and trailing If from the value
    let (value_prefix, if_value) = match extract_trailing_if(&value) {
        Some(_) => split_block_trailing_if(value),
        None => (vec![], value),
    };

    // Hoist: transform If branches so Returns are at statement level
    // The value_prefix (lets before the If) become part of the rest for each branch
    let mut branch_rest = value_prefix;
    // The branch_rest is tricky — these are Lets that need to run BEFORE the pattern binding.
    // Actually they're Lets inside the value that set up variables used in the If.
    // They need to be prepended to the block before the hoisted If.
    let hoisted = hoist_if_returns(if_value, &pattern, &rest);

    // Combine: prefix + value_prefix + hoisted
    let mut new_children = prefix;
    new_children.append(&mut branch_rest);
    new_children.push(hoisted);

    if new_children.len() == 1 {
        new_children.into_iter().next().unwrap()
    } else {
        IRNode::Block {
            children: new_children,
        }
    }
}

/// Extract the trailing If from a node (which may be an If directly or a Block ending with an If).
fn extract_trailing_if(node: &IRNode) -> Option<&IRNode> {
    match node {
        IRNode::If { .. } if if_contains_return(node) => Some(node),
        IRNode::Block { children } => children.last().and_then(|last| extract_trailing_if(last)),
        _ => None,
    }
}

/// Split a Block or If into (prefix lets, trailing If).
/// If the node is directly an If, returns (empty, If).
/// If the node is a Block ending with an If, returns (prefix children, If).
fn split_block_trailing_if(node: IRNode) -> (Vec<IRNode>, IRNode) {
    match node {
        IRNode::If { .. } => (vec![], node),
        IRNode::Block { mut children } => {
            if children.is_empty() {
                return (vec![], IRNode::Block { children });
            }
            let last = children.pop().unwrap();
            let (mut inner_prefix, if_node) = split_block_trailing_if(last);
            let mut prefix = children;
            prefix.append(&mut inner_prefix);
            (prefix, if_node)
        }
        other => (vec![], other),
    }
}

/// Transform an If tree that's the value of a Let, hoisting Returns to statement level.
///
/// For each branch:
/// - If it's a Return: keep it as-is (now at statement level, not inside Let)
/// - If it's a normal value: wrap in `Let { pattern := value }; rest...`
/// - If it's an If with mixed Return/normal branches: recurse
fn hoist_if_returns(if_node: IRNode, pattern: &[String], rest: &[IRNode]) -> IRNode {
    match if_node {
        IRNode::If {
            cond,
            then_branch,
            else_branch,
        } => {
            let then_hoisted = hoist_if_returns(*then_branch, pattern, rest);
            let else_hoisted = hoist_if_returns(*else_branch, pattern, rest);
            IRNode::If {
                cond,
                then_branch: Box::new(then_hoisted),
                else_branch: Box::new(else_hoisted),
            }
        }
        IRNode::Return(_) => if_node,
        // Block or other node that terminates (ends with Return/Abort): keep as-is
        ref node if node.terminates() => if_node,
        // Normal value: wrap in Let { pattern := value }; rest...
        // Then recursively hoist in case the value itself is a Block containing Returns
        normal_value => {
            let let_node = IRNode::Let {
                pattern: pattern.to_vec(),
                value: Box::new(normal_value),
            };
            let block = if rest.is_empty() {
                IRNode::Block {
                    children: vec![let_node],
                }
            } else {
                let mut children = vec![let_node];
                children.extend(rest.iter().cloned());
                IRNode::Block { children }
            };
            // Recursively hoist in case the Let value contains nested Returns
            hoist_returns_in_block(block)
        }
    }
}

fn strip_tail_returns(node: IRNode) -> IRNode {
    match node {
        IRNode::Return(values) => {
            if values.len() == 1 {
                values.into_iter().next().unwrap()
            } else {
                IRNode::Tuple(values)
            }
        }
        IRNode::Block { mut children } => {
            if let Some(last) = children.last_mut() {
                let taken = std::mem::replace(last, IRNode::Tuple(vec![]));
                *last = strip_tail_returns(taken);
            }
            IRNode::Block { children }
        }
        IRNode::If {
            cond,
            then_branch,
            else_branch,
        } => IRNode::If {
            cond,
            then_branch: Box::new(strip_tail_returns(*then_branch)),
            else_branch: Box::new(strip_tail_returns(*else_branch)),
        },
        other => other,
    }
}
