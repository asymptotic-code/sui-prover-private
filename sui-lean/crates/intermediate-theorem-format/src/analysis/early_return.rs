use crate::IRNode;

/// Fold early-return and strip abort-only branches.
///
/// 1. Early returns: When Move has `if (cond) { return X; }; Y`, structure
///    discovery produces a Let chain with If in the middle. This pass folds
///    the remaining siblings into the else branch.
///
/// 2. Abort stripping: When Move has `if (cond) { abort E }; Y`, the abort is
///    extracted into the separate `.aborts` function, leaving behind an empty
///    then-branch: `If(cond, (), Y)`. Since the abort path never executes at
///    runtime, strip the If entirely and keep only the non-abort branch.
pub fn fold_early_returns(node: IRNode) -> IRNode {
    let node = fold_early_returns_inner(node);
    strip_abort_branches(node)
}

/// Strip unreachable code after ifs where both branches are tail calls.
/// This handles patterns like:
///   let _ := (if cond then tail_call_A else tail_call_B)
///   unreachable_code  -- This should be removed
pub fn strip_unreachable_after_tail_calls(node: IRNode) -> IRNode {
    match node {
        IRNode::Let {
            pattern,
            value,
            body,
        } => {
            let value = Box::new(strip_unreachable_after_tail_calls(*value));
            let body = Box::new(strip_unreachable_after_tail_calls(*body));

            // If value is an If where both branches are tail calls,
            // the body is unreachable - replace it with the If itself.
            // Only do this when pattern is empty to preserve phi bindings.
            if pattern.is_empty() {
                if let IRNode::If {
                    ref cond,
                    ref then_branch,
                    ref else_branch,
                } = *value
                {
                    if is_tail_call(then_branch) && is_tail_call(else_branch) {
                        // Body is unreachable, just return the If
                        return IRNode::If {
                            cond: cond.clone(),
                            then_branch: then_branch.clone(),
                            else_branch: else_branch.clone(),
                        };
                    }
                }
            }

            IRNode::Let {
                pattern,
                value,
                body,
            }
        }
        IRNode::If {
            cond,
            then_branch,
            else_branch,
        } => IRNode::If {
            cond: Box::new(strip_unreachable_after_tail_calls(*cond)),
            then_branch: Box::new(strip_unreachable_after_tail_calls(*then_branch)),
            else_branch: Box::new(strip_unreachable_after_tail_calls(*else_branch)),
        },
        IRNode::Match { scrutinee, cases } => IRNode::Match {
            scrutinee,
            cases: cases
                .into_iter()
                .map(|(idx, bindings, body)| {
                    (idx, bindings, strip_unreachable_after_tail_calls(body))
                })
                .collect(),
        },
        other => other,
    }
}

/// Check if a node ends with a "fall-through" pattern at the tail of its
/// Let chain. This identifies "guard" branches that perform side effects and
/// fall through, vs. "early return" branches that produce a value.
///
/// Matches:
/// - `()` (unit)
/// - `UpdateField` (mutable write-back statement that was unwrapped from its Let)
fn tail_is_unit(node: &IRNode) -> bool {
    match node {
        IRNode::Tuple(elems) => elems.is_empty(),
        IRNode::Let { body, .. } => tail_is_unit(body),
        // UpdateField at tail position is a write-back statement (e.g., from mutable
        // threading). It's a side effect that falls through to the continuation.
        IRNode::UpdateField { .. } => true,
        _ => false,
    }
}

/// Append a continuation to the tail of a branch.
/// Replaces the terminal unit `()` with `let _ := (); continuation`,
/// or if the branch ends with Let bindings, appends to the deepest body.
fn append_continuation(branch: &IRNode, continuation: &IRNode) -> IRNode {
    match branch {
        IRNode::Let {
            pattern,
            value,
            body,
        } => IRNode::Let {
            pattern: pattern.clone(),
            value: value.clone(),
            body: Box::new(append_continuation(body, continuation)),
        },
        IRNode::Tuple(elems) if elems.is_empty() => {
            // Replace () with the continuation
            continuation.clone()
        }
        // For any other terminal (e.g., a non-unit value), wrap it as
        // `let _ := <terminal>; continuation`
        other => IRNode::Let {
            pattern: vec![],
            value: Box::new(other.clone()),
            body: Box::new(continuation.clone()),
        },
    }
}

/// Check if a node is a tail call (ends with a Call expression)
fn is_tail_call(node: &IRNode) -> bool {
    match node {
        IRNode::Call { .. } => true,
        IRNode::Let { body, .. } => is_tail_call(body),
        IRNode::If {
            then_branch,
            else_branch,
            ..
        } => is_tail_call(then_branch) && is_tail_call(else_branch),
        _ => false,
    }
}

/// Recursively fold early-return patterns (step 1).
/// Exported so it can be run independently before phi detection.
pub fn fold_early_returns_inner(node: IRNode) -> IRNode {
    match node {
        IRNode::Let {
            pattern,
            value,
            body,
        } => {
            let value = Box::new(fold_early_returns_inner(*value));
            let body = Box::new(fold_early_returns_inner(*body));

            // Check if value is an If with empty else branch and body continues
            // IMPORTANT: Only fold when pattern is empty. Non-empty patterns contain phi
            // variables that must be bound, so we must preserve the Let structure.
            if pattern.is_empty() {
                if let IRNode::If {
                    cond,
                    then_branch,
                    else_branch,
                } = value.as_ref()
                {
                    if is_unit(else_branch) && !is_unit(&body) {
                        if tail_is_unit(then_branch) {
                            // Guard pattern: the then-branch falls through (ends
                            // with unit), so it must also receive the continuation.
                            // let _ = if cond then X; () else (); Y
                            //    -> if cond then X; Y else Y
                            //
                            // `append_continuation` clones the continuation `body`
                            // into the then-branch (and the else keeps it), so a
                            // chain of N guard-ifs duplicates the continuation 2^N
                            // times under this bottom-up fold — an exponential
                            // blowup (observed: 86 GB on bluefin's `pool`). Only
                            // fold when the continuation is small enough that the
                            // duplication is bounded; otherwise leave the guard as
                            // `let _ := if cond then X else (); Y` (semantically
                            // identical, no duplication). The cond is preserved
                            // either way — see the strip-guard handling below.
                            const MAX_GUARD_FOLD_NODES: usize = 64;
                            if body.iter().count() <= MAX_GUARD_FOLD_NODES {
                                return IRNode::If {
                                    cond: cond.clone(),
                                    then_branch: Box::new(append_continuation(then_branch, &body)),
                                    else_branch: body,
                                };
                            }
                            return IRNode::Let {
                                pattern,
                                value: Box::new(IRNode::If {
                                    cond: cond.clone(),
                                    then_branch: then_branch.clone(),
                                    else_branch: else_branch.clone(),
                                }),
                                body,
                            };
                        }
                        // Early return: the then-branch is a complete path (call,
                        // return, etc.) that does not fall through to the continuation.
                        // let _ = if cond then X else (); Y
                        //    -> if cond then X else Y
                        return IRNode::If {
                            cond: cond.clone(),
                            then_branch: then_branch.clone(),
                            else_branch: body,
                        };
                    }
                }
            }

            IRNode::Let {
                pattern,
                value,
                body,
            }
        }
        IRNode::If {
            cond,
            then_branch,
            else_branch,
        } => IRNode::If {
            cond: Box::new(fold_early_returns_inner(*cond)),
            then_branch: Box::new(fold_early_returns_inner(*then_branch)),
            else_branch: Box::new(fold_early_returns_inner(*else_branch)),
        },
        IRNode::Match { scrutinee, cases } => IRNode::Match {
            scrutinee,
            cases: cases
                .into_iter()
                .map(|(idx, bindings, body)| (idx, bindings, fold_early_returns_inner(body)))
                .collect(),
        },
        other => other,
    }
}

/// Recursively strip If nodes where one branch is unit/empty (step 2).
pub fn strip_abort_branches(node: IRNode) -> IRNode {
    match node {
        IRNode::If {
            cond,
            then_branch,
            else_branch,
        } => strip_abort_if(*cond, *then_branch, *else_branch),
        IRNode::Let {
            pattern,
            value,
            body,
        } => IRNode::Let {
            pattern,
            value: Box::new(strip_abort_branches(*value)),
            body: Box::new(strip_abort_branches(*body)),
        },
        IRNode::Match { scrutinee, cases } => IRNode::Match {
            scrutinee,
            cases: cases
                .into_iter()
                .map(|(idx, bindings, body)| (idx, bindings, strip_abort_branches(body)))
                .collect(),
        },
        other => other,
    }
}

/// Strip an If node where one branch is unit/empty.
fn strip_abort_if(cond: IRNode, then_branch: IRNode, else_branch: IRNode) -> IRNode {
    let then_branch = strip_abort_branches(then_branch);
    let else_branch = strip_abort_branches(else_branch);

    // Use is_unit which is conservative: only strips if no important bindings are lost
    let then_is_unit = is_unit(&then_branch);
    let else_is_unit = is_unit(&else_branch);

    // Don't strip `if cond then A else Abort/()` when the condition is a termination
    // guard inserted by the loop handler (Var or BinOp comparison). These give the
    // termination checker hypotheses like `l_1_0 > 0`.
    let is_termination_guard_cond = matches!(&cond, IRNode::Var(_))
        || matches!(&cond, IRNode::BinOp { op, .. }
            if matches!(op, crate::BinOp::Gt | crate::BinOp::Ge | crate::BinOp::Lt | crate::BinOp::Le));
    let is_abort_or_unit = |n: &IRNode| {
        matches!(n, IRNode::Abort { .. }) || matches!(n, IRNode::Tuple(v) if v.is_empty())
    };
    let is_guard = is_termination_guard_cond
        && ((then_is_unit && is_abort_or_unit(&then_branch))
            || (else_is_unit && is_abort_or_unit(&else_branch)));

    if !is_guard {
        if then_is_unit && !else_is_unit {
            return else_branch;
        }
        if else_is_unit && !then_is_unit {
            return then_branch;
        }
    }

    IRNode::If {
        cond: Box::new(strip_abort_branches(cond)),
        then_branch: Box::new(then_branch),
        else_branch: Box::new(else_branch),
    }
}

/// Check if an IR node is unit/empty or an abort path (represents a stripped abort branch).
/// IMPORTANT: A branch is NOT strippable if it contains any Let with non-empty pattern anywhere,
/// because stripping the if would cause those variables to escape scope.
fn is_unit(node: &IRNode) -> bool {
    match node {
        IRNode::Tuple(elems) => elems.is_empty(),
        IRNode::Abort { .. } => true,
        // A Let is unit only if:
        // 1. Its pattern is empty (sequencing only)
        // 2. Its value doesn't define any variables (check recursively)
        // 3. Its body is unit/abort
        IRNode::Let {
            pattern,
            value,
            body,
        } => pattern.is_empty() && !contains_bindings(value) && is_unit(body),
        _ => false,
    }
}

/// Check if a node is effectively unit for aborts purposes.
/// This is more permissive than is_unit - it returns true for branches
/// that end in unit, even if they have Let bindings with non-empty patterns.
/// This is used in aborts simplification where variable bindings don't matter.
fn is_effectively_unit_for_aborts(node: &IRNode) -> bool {
    match node {
        IRNode::Tuple(elems) => elems.is_empty(),
        IRNode::Abort { .. } => true,
        IRNode::Let { body, .. } => is_effectively_unit_for_aborts(body),
        _ => false,
    }
}

/// Wrap a unit-ending branch with `false` at the end for type consistency.
/// Transforms: let x := ...; let y := ...; ()
/// Into:       let x := ...; let y := ...; false
fn wrap_unit_branch_with_false(node: &IRNode) -> Box<IRNode> {
    match node {
        IRNode::Tuple(elems) if elems.is_empty() => {
            Box::new(IRNode::Const(crate::Const::Bool(false)))
        }
        IRNode::Abort { .. } => Box::new(IRNode::Const(crate::Const::Bool(false))),
        IRNode::Let {
            pattern,
            value,
            body,
        } => Box::new(IRNode::Let {
            pattern: pattern.clone(),
            value: value.clone(),
            body: wrap_unit_branch_with_false(body),
        }),
        other => Box::new(other.clone()),
    }
}

/// Check if a node contains any Let bindings with non-empty patterns.
/// This detects variable definitions anywhere in the subtree.
fn contains_bindings(node: &IRNode) -> bool {
    match node {
        IRNode::Let {
            pattern,
            value,
            body,
        } => !pattern.is_empty() || contains_bindings(value) || contains_bindings(body),
        IRNode::If {
            cond,
            then_branch,
            else_branch,
        } => {
            contains_bindings(cond)
                || contains_bindings(then_branch)
                || contains_bindings(else_branch)
        }
        IRNode::Tuple(elems) => elems.iter().any(contains_bindings),
        IRNode::BinOp { lhs, rhs, .. } => contains_bindings(lhs) || contains_bindings(rhs),
        IRNode::UnOp { operand, .. } => contains_bindings(operand),
        IRNode::Call { args, .. } => args.iter().any(contains_bindings),
        _ => false,
    }
}

/// Rewrite `Prover.asserts(p)` calls in aborts IR into conditional abort conditions.
///
/// Transforms:
///   let _ := Prover.asserts(p)
///   <rest>
/// Into:
///   if ¬p then True else <rest>
///
/// This makes the `.aborts` def return True when any assert condition fails,
/// giving `¬(func.aborts ...)` the meaning "all asserts hold".
pub fn rewrite_asserts_in_aborts(
    node: IRNode,
    assert_fn_ids: &std::collections::HashSet<crate::FunctionID>,
) -> IRNode {
    match node {
        IRNode::Let {
            pattern,
            value,
            body,
        } => {
            // Check if value is a Prover.asserts call with empty pattern (let _ := ...)
            if pattern.is_empty() {
                if let IRNode::Call {
                    ref function,
                    ref args,
                    ..
                } = *value
                {
                    if assert_fn_ids.contains(function) {
                        if let Some(condition) = args.first() {
                            // Transform: if ¬condition then True else <rest>
                            let rest = rewrite_asserts_in_aborts(*body, assert_fn_ids);
                            return IRNode::If {
                                cond: Box::new(IRNode::UnOp {
                                    op: crate::UnOp::Not,
                                    operand: Box::new(condition.clone()),
                                }),
                                then_branch: Box::new(IRNode::Const(crate::Const::Bool(true))),
                                else_branch: Box::new(rest),
                            };
                        }
                    }
                }
            }
            IRNode::Let {
                pattern,
                // Do NOT recurse into Let values — they compute results with
                // non-Prop types (e.g. BoundedNat).  Rewriting asserts inside
                // a value creates if-branches with mismatched types.
                value,
                body: Box::new(rewrite_asserts_in_aborts(*body, assert_fn_ids)),
            }
        }
        IRNode::If {
            cond,
            then_branch,
            else_branch,
        } => IRNode::If {
            cond,
            then_branch: Box::new(rewrite_asserts_in_aborts(*then_branch, assert_fn_ids)),
            else_branch: Box::new(rewrite_asserts_in_aborts(*else_branch, assert_fn_ids)),
        },
        IRNode::Match { scrutinee, cases } => IRNode::Match {
            scrutinee,
            cases: cases
                .into_iter()
                .map(|(idx, bindings, body)| {
                    (
                        idx,
                        bindings,
                        rewrite_asserts_in_aborts(body, assert_fn_ids),
                    )
                })
                .collect(),
        },
        other => other,
    }
}

/// Simplify aborts IR to ensure consistent Bool return type.
/// This handles cases where if-branches have mismatched types due to
/// one branch containing value computation (returning Unit) and
/// the other returning Bool.
pub fn simplify_aborts(node: IRNode) -> IRNode {
    match node {
        IRNode::Let {
            pattern,
            value,
            body,
        } => {
            // First, simplify the value
            let simplified_value = Box::new(simplify_aborts(*value));
            let body = Box::new(simplify_aborts(*body));

            // Check if this is a tuple pattern (from phi detection) but the value has been
            // simplified to return Bool OR has mismatched branch types.
            let is_tuple_pattern = pattern.len() > 1;

            // For tuple patterns, we need to check if the value is usable as a tuple.
            // If it's an If with mismatched branch types (one Bool, one not), it can't
            // satisfy a tuple pattern.
            let value_incompatible_with_tuple = if is_tuple_pattern {
                if let IRNode::If {
                    then_branch,
                    else_branch,
                    ..
                } = simplified_value.as_ref()
                {
                    let then_is_bool = ends_with_bool(then_branch);
                    let else_is_bool = ends_with_bool(else_branch);
                    // If either branch ends with Bool, but not both, we have a type mismatch.
                    // Also if both branches end with Bool, the If returns Bool not tuple.
                    then_is_bool || else_is_bool
                } else {
                    ends_with_bool(&simplified_value)
                }
            } else {
                false
            };

            let final_pattern = if is_tuple_pattern && value_incompatible_with_tuple {
                // Tuple pattern bound to incompatible value - discard the pattern
                vec![]
            } else {
                pattern
            };

            // Check if none of the pattern variables are used in the body
            let no_vars_used = !final_pattern
                .iter()
                .any(|var| var.as_ref() != "_" && body_references_var(&body, var));

            // If body is just `false` and no pattern vars are used, we can strip the binding
            // But keep if value has side effects (calls that might abort)
            if is_const_false(&body) && no_vars_used && !contains_abort_calls(&simplified_value) {
                return *body;
            }

            // If the value is Inhabited and none of the pattern variables are used in body,
            // we can skip this binding entirely (it's just a placeholder that's never referenced)
            if matches!(simplified_value.as_ref(), IRNode::Inhabited) && no_vars_used {
                return *body;
            }

            IRNode::Let {
                pattern: final_pattern,
                value: simplified_value,
                body,
            }
        }
        IRNode::If {
            cond,
            then_branch,
            else_branch,
        } => {
            let then_branch = Box::new(simplify_aborts(*then_branch));
            let else_branch = Box::new(simplify_aborts(*else_branch));
            let cond = Box::new(simplify_aborts(*cond));

            // Check if branches are effectively "no abort" (either false, unit, or unit-with-bindings without calls)
            let then_no_abort = is_const_false(&then_branch)
                || is_unit_no_abort(&then_branch)
                || (is_effectively_unit_for_aborts(&then_branch)
                    && !contains_abort_calls(&then_branch));
            let else_no_abort = is_const_false(&else_branch)
                || is_unit_no_abort(&else_branch)
                || (is_effectively_unit_for_aborts(&else_branch)
                    && !contains_abort_calls(&else_branch));

            // Check if branches end in unit (regardless of calls) - used for type coercion
            let then_ends_unit = is_effectively_unit_for_aborts(&then_branch);
            let else_ends_unit = is_effectively_unit_for_aborts(&else_branch);

            // Check if branches define variables that might be used outside the if.
            // If so, we can't simplify away the if without losing those definitions.
            let then_defines_vars = contains_bindings(&then_branch);
            let else_defines_vars = contains_bindings(&else_branch);

            // If both branches have no abort AND neither defines variables, the whole if has no abort
            if then_no_abort && else_no_abort && !then_defines_vars && !else_defines_vars {
                return IRNode::Const(crate::Const::Bool(false));
            }

            // If one branch has no abort and other is false, return false
            if (then_no_abort && is_const_false(&else_branch))
                || (is_const_false(&then_branch) && else_no_abort)
            {
                return IRNode::Const(crate::Const::Bool(false));
            }

            // For type consistency: convert branches to Bool if needed.
            // This handles unit-ending branches and tuple-ending branches.
            let then_is_bool = ends_with_bool(&then_branch);
            let else_is_bool = ends_with_bool(&else_branch);
            let then_ends_tuple = ends_with_tuple(&then_branch);
            let else_ends_tuple = ends_with_tuple(&else_branch);

            let then_result = if then_ends_unit && !is_const_false(&then_branch) {
                wrap_unit_branch_with_false(&then_branch)
            } else if then_ends_tuple && else_is_bool {
                // Tuple vs Bool mismatch - wrap tuple branch
                wrap_non_bool_with_false(&then_branch)
            } else {
                then_branch
            };
            let else_result = if else_ends_unit && !is_const_false(&else_branch) {
                wrap_unit_branch_with_false(&else_branch)
            } else if else_ends_tuple && then_is_bool {
                // Tuple vs Bool mismatch - wrap tuple branch
                wrap_non_bool_with_false(&else_branch)
            } else {
                else_branch
            };

            IRNode::If {
                cond,
                then_branch: then_result,
                else_branch: else_result,
            }
        }
        IRNode::Match { scrutinee, cases } => IRNode::Match {
            scrutinee,
            cases: cases
                .into_iter()
                .map(|(idx, bindings, body)| (idx, bindings, simplify_aborts(body)))
                .collect(),
        },
        other => other,
    }
}

/// Simplify aborts IR while preserving the terminal type.
/// This is used for If branches that are assigned to variables - we need to
/// preserve the computation so the variable gets the right type, but still
/// simplify any nested abort-related logic.
fn simplify_aborts_preserving_type(node: IRNode) -> IRNode {
    match node {
        IRNode::Let {
            pattern,
            value,
            body,
        } => IRNode::Let {
            pattern,
            value: Box::new(simplify_aborts_preserving_type(*value)),
            body: Box::new(simplify_aborts_preserving_type(*body)),
        },
        IRNode::If {
            cond,
            then_branch,
            else_branch,
        } => IRNode::If {
            cond: Box::new(simplify_aborts(*cond)),
            then_branch: Box::new(simplify_aborts_preserving_type(*then_branch)),
            else_branch: Box::new(simplify_aborts_preserving_type(*else_branch)),
        },
        IRNode::Call {
            function,
            type_args,
            args,
        } => {
            // Preserve calls - they may abort
            IRNode::Call {
                function,
                type_args,
                args: args.into_iter().map(simplify_aborts).collect(),
            }
        }
        other => other,
    }
}

/// Check if a node is the constant `false`
fn is_const_false(node: &IRNode) -> bool {
    matches!(node, IRNode::Const(crate::Const::Bool(false)))
}

/// Check if a node is the constant `true`
fn is_const_true(node: &IRNode) -> bool {
    matches!(node, IRNode::Const(crate::Const::Bool(true)))
}

/// Check if a node ends with a Bool constant (false or true), looking through lets
fn ends_with_bool(node: &IRNode) -> bool {
    match node {
        IRNode::Const(crate::Const::Bool(_)) => true,
        IRNode::Let { body, .. } => ends_with_bool(body),
        IRNode::If {
            then_branch,
            else_branch,
            ..
        } => ends_with_bool(then_branch) && ends_with_bool(else_branch),
        _ => false,
    }
}

/// Check if a node is unit AND doesn't contain any abort-related calls
fn is_unit_no_abort(node: &IRNode) -> bool {
    is_unit(node) && !contains_abort_calls(node)
}

/// Check if a node contains any function calls (potential abort points)
fn contains_abort_calls(node: &IRNode) -> bool {
    match node {
        IRNode::Call { .. } => true,
        IRNode::Let { value, body, .. } => {
            contains_abort_calls(value) || contains_abort_calls(body)
        }
        IRNode::If {
            cond,
            then_branch,
            else_branch,
        } => {
            contains_abort_calls(cond)
                || contains_abort_calls(then_branch)
                || contains_abort_calls(else_branch)
        }
        IRNode::Tuple(elems) => elems.iter().any(contains_abort_calls),
        IRNode::BinOp { lhs, rhs, .. } => contains_abort_calls(lhs) || contains_abort_calls(rhs),
        IRNode::UnOp { operand, .. } => contains_abort_calls(operand),
        _ => false,
    }
}

/// Check if a branch ends with a Var or non-empty Tuple (not Bool/Unit).
/// This indicates phi detection may have incorrectly extracted a non-Bool value.
fn ends_with_non_bool(node: &IRNode) -> bool {
    match node {
        IRNode::Var(_) => true,
        IRNode::Tuple(elems) => !elems.is_empty(),
        IRNode::Let { body, .. } => ends_with_non_bool(body),
        IRNode::If {
            then_branch,
            else_branch,
            ..
        } => ends_with_non_bool(then_branch) || ends_with_non_bool(else_branch),
        _ => false,
    }
}

/// Check if a branch ends with a non-empty Tuple.
fn ends_with_tuple(node: &IRNode) -> bool {
    match node {
        IRNode::Tuple(elems) => !elems.is_empty(),
        IRNode::Let { body, .. } => ends_with_tuple(body),
        IRNode::If {
            then_branch,
            else_branch,
            ..
        } => ends_with_tuple(then_branch) || ends_with_tuple(else_branch),
        _ => false,
    }
}

/// Wrap a non-Bool-ending branch with false for aborts context.
/// Preserves the computation but changes the terminal to false.
fn wrap_non_bool_with_false(node: &IRNode) -> Box<IRNode> {
    match node {
        IRNode::Var(_) => Box::new(IRNode::Const(crate::Const::Bool(false))),
        IRNode::Tuple(elems) if !elems.is_empty() => {
            Box::new(IRNode::Const(crate::Const::Bool(false)))
        }
        IRNode::Let {
            pattern,
            value,
            body,
        } => Box::new(IRNode::Let {
            pattern: pattern.clone(),
            value: value.clone(),
            body: wrap_non_bool_with_false(body),
        }),
        IRNode::If {
            cond,
            then_branch,
            else_branch,
        } => {
            let new_then = if ends_with_non_bool(then_branch) {
                wrap_non_bool_with_false(then_branch)
            } else {
                then_branch.clone()
            };
            let new_else = if ends_with_non_bool(else_branch) {
                wrap_non_bool_with_false(else_branch)
            } else {
                else_branch.clone()
            };
            Box::new(IRNode::If {
                cond: cond.clone(),
                then_branch: new_then,
                else_branch: new_else,
            })
        }
        other => Box::new(other.clone()),
    }
}

/// Check if a body references a specific variable.
fn body_references_var(node: &IRNode, var: &std::rc::Rc<str>) -> bool {
    match node {
        IRNode::Var(name) => name.as_ref() == var.as_ref(),
        IRNode::Let { value, body, .. } => {
            body_references_var(value, var) || body_references_var(body, var)
        }
        IRNode::If {
            cond,
            then_branch,
            else_branch,
        } => {
            body_references_var(cond, var)
                || body_references_var(then_branch, var)
                || body_references_var(else_branch, var)
        }
        IRNode::BinOp { lhs, rhs, .. } => {
            body_references_var(lhs, var) || body_references_var(rhs, var)
        }
        IRNode::UnOp { operand, .. } => body_references_var(operand, var),
        IRNode::Tuple(elems) => elems.iter().any(|e| body_references_var(e, var)),
        IRNode::Call { args, .. } => args.iter().any(|a| body_references_var(a, var)),
        _ => false,
    }
}

/// Replace all Inhabited nodes with false in aborts context.
/// Phi detection creates Inhabited placeholders for undefined variables,
/// but in aborts context we want these to be false (no abort).
pub fn replace_inhabited_with_false(node: IRNode) -> IRNode {
    match node {
        IRNode::Inhabited => IRNode::Const(crate::Const::Bool(false)),
        IRNode::Let {
            pattern,
            value,
            body,
        } => IRNode::Let {
            pattern,
            value: Box::new(replace_inhabited_with_false(*value)),
            body: Box::new(replace_inhabited_with_false(*body)),
        },
        IRNode::If {
            cond,
            then_branch,
            else_branch,
        } => IRNode::If {
            cond: Box::new(replace_inhabited_with_false(*cond)),
            then_branch: Box::new(replace_inhabited_with_false(*then_branch)),
            else_branch: Box::new(replace_inhabited_with_false(*else_branch)),
        },
        IRNode::Match { scrutinee, cases } => IRNode::Match {
            scrutinee: Box::new(replace_inhabited_with_false(*scrutinee)),
            cases: cases
                .into_iter()
                .map(|(idx, bindings, body)| (idx, bindings, replace_inhabited_with_false(body)))
                .collect(),
        },
        IRNode::BinOp { op, lhs, rhs } => IRNode::BinOp {
            op,
            lhs: Box::new(replace_inhabited_with_false(*lhs)),
            rhs: Box::new(replace_inhabited_with_false(*rhs)),
        },
        IRNode::UnOp { op, operand } => IRNode::UnOp {
            op,
            operand: Box::new(replace_inhabited_with_false(*operand)),
        },
        IRNode::Call {
            function,
            type_args,
            args,
        } => IRNode::Call {
            function,
            type_args,
            args: args.into_iter().map(replace_inhabited_with_false).collect(),
        },
        IRNode::Tuple(elems) => IRNode::Tuple(
            elems
                .into_iter()
                .map(replace_inhabited_with_false)
                .collect(),
        ),
        other => other,
    }
}

/// Replace Let values containing Inhabited with dummy false tuples.
/// This is smarter than replace_inhabited_with_false because it replaces
/// the ENTIRE value (e.g., a function call with Inhabited args) rather than
/// just the Inhabited nodes inside. This avoids type mismatches like
/// `full_mul(false, false)` where `false` has wrong type.
///
/// If a Let value contains Inhabited anywhere, the entire value is replaced
/// with a tuple of `false` values matching the pattern length.
pub fn replace_inhabited_let_values(node: IRNode) -> IRNode {
    match node {
        IRNode::Let {
            pattern,
            value,
            body,
        } => {
            let body = replace_inhabited_let_values(*body);

            // Check if value contains Inhabited
            if contains_inhabited(&value) {
                // Replace the entire value with a tuple of false values
                let false_tuple = if pattern.len() == 1 {
                    IRNode::Const(crate::Const::Bool(false))
                } else {
                    IRNode::Tuple(
                        (0..pattern.len())
                            .map(|_| IRNode::Const(crate::Const::Bool(false)))
                            .collect(),
                    )
                };
                IRNode::Let {
                    pattern,
                    value: Box::new(false_tuple),
                    body: Box::new(body),
                }
            } else {
                // Recurse into value normally
                let value = replace_inhabited_let_values(*value);
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
        } => IRNode::If {
            cond: Box::new(replace_inhabited_let_values(*cond)),
            then_branch: Box::new(replace_inhabited_let_values(*then_branch)),
            else_branch: Box::new(replace_inhabited_let_values(*else_branch)),
        },
        IRNode::Match { scrutinee, cases } => IRNode::Match {
            scrutinee: Box::new(replace_inhabited_let_values(*scrutinee)),
            cases: cases
                .into_iter()
                .map(|(idx, bindings, body)| (idx, bindings, replace_inhabited_let_values(body)))
                .collect(),
        },
        IRNode::MatchOption {
            scrutinee,
            binding,
            some_branch,
            none_branch,
        } => IRNode::MatchOption {
            scrutinee: Box::new(replace_inhabited_let_values(*scrutinee)),
            binding,
            some_branch: Box::new(replace_inhabited_let_values(*some_branch)),
            none_branch: Box::new(replace_inhabited_let_values(*none_branch)),
        },
        other => other,
    }
}

/// Check if an IRNode contains an Inhabited node anywhere
fn contains_inhabited(node: &IRNode) -> bool {
    match node {
        IRNode::Inhabited => true,
        IRNode::Let { value, body, .. } => contains_inhabited(value) || contains_inhabited(body),
        IRNode::If {
            cond,
            then_branch,
            else_branch,
        } => {
            contains_inhabited(cond)
                || contains_inhabited(then_branch)
                || contains_inhabited(else_branch)
        }
        IRNode::Match { scrutinee, cases } => {
            contains_inhabited(scrutinee)
                || cases.iter().any(|(_, _, body)| contains_inhabited(body))
        }
        IRNode::MatchOption {
            scrutinee,
            some_branch,
            none_branch,
            ..
        } => {
            contains_inhabited(scrutinee)
                || contains_inhabited(some_branch)
                || contains_inhabited(none_branch)
        }
        IRNode::BinOp { lhs, rhs, .. } => contains_inhabited(lhs) || contains_inhabited(rhs),
        IRNode::UnOp { operand, .. } => contains_inhabited(operand),
        IRNode::Call { args, .. } => args.iter().any(contains_inhabited),
        IRNode::Tuple(elems) => elems.iter().any(contains_inhabited),
        IRNode::Pack { fields, .. } => fields.iter().any(contains_inhabited),
        IRNode::Unpack { value, .. } => contains_inhabited(value),
        IRNode::Field { base, .. } => contains_inhabited(base),
        IRNode::UpdateField { base, value, .. } => {
            contains_inhabited(base) || contains_inhabited(value)
        }
        IRNode::MutableBorrow { val_expr, .. } => contains_inhabited(val_expr),
        IRNode::ReadRef(inner) => contains_inhabited(inner),
        IRNode::WriteRef { reference, value } => {
            contains_inhabited(reference) || contains_inhabited(value)
        }
        IRNode::ToProp(inner) | IRNode::ToBool(inner) => contains_inhabited(inner),
        _ => false,
    }
}

/// Fix undefined variable references in aborts context by replacing them with false.
/// This handles cases where phi-like variables are defined inside if branches
/// but referenced outside, which happens when phi detection is skipped for aborts.
///
/// Note: This function assumes that function parameters are already handled by
/// the caller passing a non-empty initial_scope. Variables in the initial scope
/// will not be replaced.
pub fn fix_undefined_vars_in_aborts(node: IRNode, initial_scope: &[String]) -> IRNode {
    use crate::data::types::TempId;
    use std::collections::BTreeSet;
    use std::rc::Rc;

    fn fix_inner(node: IRNode, scope: &BTreeSet<TempId>) -> IRNode {
        match node {
            IRNode::Var(name) => {
                if scope.contains(&name) {
                    IRNode::Var(name)
                } else {
                    // Undefined variable - replace with false
                    IRNode::Const(crate::Const::Bool(false))
                }
            }
            IRNode::Let {
                pattern,
                value,
                body,
            } => {
                let value = Box::new(fix_inner(*value, scope));
                let mut new_scope = scope.clone();
                new_scope.extend(pattern.iter().cloned());
                let body = Box::new(fix_inner(*body, &new_scope));
                IRNode::Let {
                    pattern,
                    value,
                    body,
                }
            }
            IRNode::If {
                cond,
                then_branch,
                else_branch,
            } => {
                let cond = Box::new(fix_inner(*cond, scope));
                let then_branch = Box::new(fix_inner(*then_branch, scope));
                let else_branch = Box::new(fix_inner(*else_branch, scope));
                IRNode::If {
                    cond,
                    then_branch,
                    else_branch,
                }
            }
            IRNode::Match { scrutinee, cases } => {
                let scrutinee = Box::new(fix_inner(*scrutinee, scope));
                let cases = cases
                    .into_iter()
                    .map(|(idx, bindings, body)| {
                        let mut case_scope = scope.clone();
                        case_scope.extend(bindings.iter().cloned());
                        (idx, bindings, fix_inner(body, &case_scope))
                    })
                    .collect();
                IRNode::Match { scrutinee, cases }
            }
            IRNode::BinOp { op, lhs, rhs } => IRNode::BinOp {
                op,
                lhs: Box::new(fix_inner(*lhs, scope)),
                rhs: Box::new(fix_inner(*rhs, scope)),
            },
            IRNode::UnOp { op, operand } => IRNode::UnOp {
                op,
                operand: Box::new(fix_inner(*operand, scope)),
            },
            IRNode::Call {
                function,
                type_args,
                args,
            } => IRNode::Call {
                function,
                type_args,
                args: args.into_iter().map(|a| fix_inner(a, scope)).collect(),
            },
            IRNode::Tuple(elems) => {
                IRNode::Tuple(elems.into_iter().map(|e| fix_inner(e, scope)).collect())
            }
            other => other,
        }
    }

    // Start with initial scope (function parameters) and fix undefined references
    let scope: BTreeSet<TempId> = initial_scope.iter().map(|s| Rc::from(s.as_str())).collect();
    fix_inner(node, &scope)
}

/// Inline calls to abort-only `<while>.after` loop-continuation helpers.
///
/// A `<f>.while_N.after` helper whose Move source falls through to `abort`
/// has a bare-`Abort` body. `mutable_threading`'s demotion (step 4b) then
/// strips the `Mutable` wrapper off its return type — because an abort body
/// exposes no mutref result — while its `<while>` sibling keeps the wrapper
/// (its found-branch has a real `Mutable.compose`). The sibling's exit call
/// `let r := <while>.after …; (r.1, …)` then feeds a plain value where a
/// `Mutable` is expected ("Application type mismatch"; cetus
/// `borrow_mut_rewarder`).
///
/// The call always aborts, so this pass replaces the enclosing `let` (whose
/// value is the call) — and the now-unreachable destructure that follows —
/// with an inline `Abort`. Lean unifies that with the found-branch's inferred
/// `Mutable` type, so no return-type annotation (and no unreliable state
/// placeholder) is needed. Only value-mode bodies are rewritten; `.aborts` /
/// `.ensures` / `.requires` / `.asserts` faces are skipped, where an abort
/// must feed the Prop/Option abort shape rather than collapse to `sorry`.
pub fn inline_abort_only_after_calls(program: &mut crate::Program) {
    use std::collections::BTreeMap;

    let targets: BTreeMap<crate::FunctionID, Option<IRNode>> = program
        .functions
        .iter()
        .filter(|(_, f)| !f.is_native && f.name.contains(".after"))
        .filter_map(|(fid, f)| abort_tail_code(&f.body).map(|code| (fid, code)))
        .collect();
    if targets.is_empty() {
        return;
    }

    let ids: Vec<crate::FunctionID> = program.functions.iter_ids().collect();
    for id in ids {
        let f = program.functions.get(&id);
        if f.is_native {
            continue;
        }
        let nm = &f.name;
        if nm.contains(".aborts")
            || nm.contains(".ensures")
            || nm.contains(".requires")
            || nm.contains(".asserts")
        {
            continue;
        }
        let body = std::mem::take(&mut program.functions.get_mut(id).body);
        program.functions.get_mut(id).body = inline_after_calls_inner(body, &targets);
    }
}

/// If `node` always aborts (its tail is an `Abort`), return that abort's code.
fn abort_tail_code(node: &IRNode) -> Option<Option<IRNode>> {
    match node {
        IRNode::Abort { code } => Some(code.as_deref().cloned()),
        IRNode::Let { body, .. } => abort_tail_code(body),
        _ => None,
    }
}

fn call_is_target(
    node: &IRNode,
    targets: &std::collections::BTreeMap<crate::FunctionID, Option<IRNode>>,
) -> Option<Option<IRNode>> {
    match node {
        IRNode::Call { function, .. } => targets.get(function).cloned(),
        _ => None,
    }
}

fn inline_after_calls_inner(
    node: IRNode,
    targets: &std::collections::BTreeMap<crate::FunctionID, Option<IRNode>>,
) -> IRNode {
    match node {
        IRNode::Let {
            pattern,
            value,
            body,
        } => {
            if let Some(code) = call_is_target(&value, targets) {
                return IRNode::Abort {
                    code: code.map(Box::new),
                };
            }
            IRNode::Let {
                pattern,
                value: Box::new(inline_after_calls_inner(*value, targets)),
                body: Box::new(inline_after_calls_inner(*body, targets)),
            }
        }
        IRNode::If {
            cond,
            then_branch,
            else_branch,
        } => {
            let fix = |n: IRNode| -> IRNode {
                if let Some(code) = call_is_target(&n, targets) {
                    IRNode::Abort {
                        code: code.map(Box::new),
                    }
                } else {
                    inline_after_calls_inner(n, targets)
                }
            };
            IRNode::If {
                cond,
                then_branch: Box::new(fix(*then_branch)),
                else_branch: Box::new(fix(*else_branch)),
            }
        }
        IRNode::Match { scrutinee, cases } => IRNode::Match {
            scrutinee,
            cases: cases
                .into_iter()
                .map(|(idx, bindings, body)| {
                    let body = if let Some(code) = call_is_target(&body, targets) {
                        IRNode::Abort {
                            code: code.map(Box::new),
                        }
                    } else {
                        inline_after_calls_inner(body, targets)
                    };
                    (idx, bindings, body)
                })
                .collect(),
        },
        other => other,
    }
}
