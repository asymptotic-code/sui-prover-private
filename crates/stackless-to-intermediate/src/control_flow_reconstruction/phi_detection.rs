// Copyright (c) Asymptotic
// SPDX-License-Identifier: Apache-2.0

//! Phi Detection — rewrites if/match nodes to return all defined variables.
//!
//! For `if cond then A else B` with continuation C:
//!   - Collect variables defined in BOTH A and B (intersection), OR
//!     defined in one branch but already in the outer scope (reassignment)
//!   - Transform to: `let (v1, v2, ...) := if cond then (...) else (...) in C`
//!   - The branch that doesn't define a reassigned variable implicitly
//!     keeps the outer value (append_phi_return emits Var(v) for it).

use intermediate_theorem_format::data::types::TempId;
use intermediate_theorem_format::IRNode;
use std::collections::BTreeSet;

/// Compute which variables are phi variables for an if expression.
///
/// A variable is a phi variable if:
/// 1. It's defined in BOTH branches (standard phi), OR
/// 2. It's defined in ONE branch and already exists in the outer scope
///    (it's a reassignment — the other branch implicitly keeps the old value)
///
/// Variables referenced by the condition are excluded (they can't be reassigned).
pub fn compute_if_phi_vars(
    cond: &IRNode,
    then_branch: &IRNode,
    else_branch: &IRNode,
    outer_scope: &BTreeSet<TempId>,
) -> Vec<TempId> {
    let then_defs = then_branch.bindings();
    let else_defs = else_branch.bindings();

    // Variables defined in both branches (standard phi)
    let both: BTreeSet<_> = then_defs.intersection(&else_defs).cloned().collect();

    // Variables defined in only one branch but already in outer scope (reassignment)
    let then_only: BTreeSet<_> = then_defs.difference(&else_defs).cloned().collect();
    let else_only: BTreeSet<_> = else_defs.difference(&then_defs).cloned().collect();
    let reassigned: BTreeSet<_> = then_only
        .union(&else_only)
        .filter(|v| outer_scope.contains(*v))
        .cloned()
        .collect();

    let all_defs: BTreeSet<_> = both.union(&reassigned).cloned().collect();

    let cond_free = cond.free_vars();

    all_defs
        .into_iter()
        .filter(|v| !cond_free.contains(v))
        .collect()
}

/// Detect and lift phi variables for an if expression with continuation.
///
/// 1. Collects variables defined in BOTH branches, or in one branch
///    when the variable is already in the outer scope (reassignment)
/// 2. Transforms both branches to return those variables as a tuple
/// 3. Wraps in a let binding so the continuation can use them
pub fn detect_if_phis(
    cond: IRNode,
    then_branch: IRNode,
    else_branch: IRNode,
    continuation: IRNode,
    outer_scope: &BTreeSet<TempId>,
) -> IRNode {
    let phi_vars = compute_if_phi_vars(&cond, &then_branch, &else_branch, outer_scope);

    if phi_vars.is_empty() {
        // No variables defined in branches, no phi lifting needed
        return IRNode::Let {
            pattern: vec![],
            value: Box::new(IRNode::If {
                cond: Box::new(cond),
                then_branch: Box::new(then_branch),
                else_branch: Box::new(else_branch),
            }),
            body: Box::new(continuation),
        };
    }

    // Transform branches to return the phi variables
    let then_transformed = append_phi_return(then_branch, &phi_vars);
    let else_transformed = append_phi_return(else_branch, &phi_vars);

    // Build: let (phi_vars...) := if cond then ... else ... in continuation
    IRNode::Let {
        pattern: phi_vars,
        value: Box::new(IRNode::If {
            cond: Box::new(cond),
            then_branch: Box::new(then_transformed),
            else_branch: Box::new(else_transformed),
        }),
        body: Box::new(continuation),
    }
}

/// Detect and lift phi variables for a match expression with continuation.
///
/// Same logic as detect_if_phis but generalized for N cases:
/// phi variables are those defined in ALL cases (intersection across all arms),
/// OR defined in at least one case when already in the outer scope (reassignment).
pub fn detect_match_phis(
    scrutinee: IRNode,
    cases: Vec<(usize, Vec<TempId>, IRNode)>,
    continuation: IRNode,
    outer_scope: &BTreeSet<TempId>,
) -> IRNode {
    if cases.is_empty() {
        return IRNode::assign(
            IRNode::Match {
                scrutinee: Box::new(scrutinee),
                cases,
            },
            continuation,
        );
    }

    // Collect bindings from each case
    let case_defs: Vec<BTreeSet<_>> = cases.iter().map(|(_, _, body)| body.bindings()).collect();

    // Variables defined in ALL cases (standard phi)
    let mut all_cases: BTreeSet<_> = case_defs[0].clone();
    for defs in case_defs.iter().skip(1) {
        all_cases = all_cases.intersection(defs).cloned().collect();
    }

    // Variables defined in at least one case but already in outer scope (reassignment)
    let mut any_case: BTreeSet<_> = BTreeSet::new();
    for defs in &case_defs {
        any_case = any_case.union(defs).cloned().collect();
    }
    let reassigned: BTreeSet<_> = any_case
        .difference(&all_cases)
        .filter(|v| outer_scope.contains(*v))
        .cloned()
        .collect();

    let all_defs: BTreeSet<_> = all_cases.union(&reassigned).cloned().collect();

    let scrutinee_free = scrutinee.free_vars();

    let phi_vars: Vec<TempId> = all_defs
        .into_iter()
        .filter(|v| !scrutinee_free.contains(v))
        .collect();

    if phi_vars.is_empty() {
        return IRNode::Let {
            pattern: vec![],
            value: Box::new(IRNode::Match {
                scrutinee: Box::new(scrutinee),
                cases,
            }),
            body: Box::new(continuation),
        };
    }

    let transformed_cases: Vec<_> = cases
        .into_iter()
        .map(|(idx, bindings, body)| (idx, bindings, append_phi_return(body, &phi_vars)))
        .collect();

    IRNode::Let {
        pattern: phi_vars,
        value: Box::new(IRNode::Match {
            scrutinee: Box::new(scrutinee),
            cases: transformed_cases,
        }),
        body: Box::new(continuation),
    }
}

// ============================================================================
// Helper functions
// ============================================================================

/// Transform a branch to return phi variables as a tuple at the end.
/// Recurses through Let chains and into If/Match branches to ensure
/// phi variables are returned from every code path.
fn append_phi_return(ir: IRNode, phi_vars: &[TempId]) -> IRNode {
    match ir {
        IRNode::Let {
            pattern,
            value,
            body,
        } => IRNode::Let {
            pattern,
            value,
            body: Box::new(append_phi_return(*body, phi_vars)),
        },
        IRNode::If {
            cond,
            then_branch,
            else_branch,
        } => {
            // Recurse into both branches of the If
            IRNode::If {
                cond,
                then_branch: Box::new(append_phi_return(*then_branch, phi_vars)),
                else_branch: Box::new(append_phi_return(*else_branch, phi_vars)),
            }
        }
        IRNode::Match { scrutinee, cases } => {
            // Recurse into all match arms
            IRNode::Match {
                scrutinee,
                cases: cases
                    .into_iter()
                    .map(|(idx, bindings, body)| (idx, bindings, append_phi_return(body, phi_vars)))
                    .collect(),
            }
        }
        terminal => {
            // At the terminal, discard it and return the phi tuple
            let phi_tuple = if phi_vars.len() == 1 {
                IRNode::Var(phi_vars[0].clone())
            } else {
                IRNode::Tuple(phi_vars.iter().map(|v| IRNode::Var(v.clone())).collect())
            };

            // Wrap: let _ := terminal in phi_tuple
            IRNode::Let {
                pattern: vec![],
                value: Box::new(terminal),
                body: Box::new(phi_tuple),
            }
        }
    }
}
