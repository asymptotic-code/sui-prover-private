// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Cleanup pass for TheoremIR
//!
//! Transformations:
//! 1. Remove identity assignments: `let x := x` -> removed
//! 2. Simplify boolean if expressions: `if cond then true else false` -> `cond`
//! 3. Convert nested boolean ifs to AND: `if A then B else false` -> `A && B`

use crate::data::ir::WriteBackEdge;
use crate::data::structure::StructID;
use crate::data::types::TempId;
use crate::data::variables::VariableRegistry;
use crate::{BinOp, Const, IRNode, Type};
use std::collections::BTreeMap;
use std::rc::Rc;

pub fn cleanup(node: IRNode, reg: &mut VariableRegistry, self_fn: Option<usize>) -> IRNode {
    let node = remove_identity_lets(node);
    let node = simplify_boolean_ifs(node);
    let node = convert_boolean_ifs_to_and_or(node, reg, self_fn);
    collapse_branch_bindings(node)
}

/// Normalize unit-valued if-branches to false for Bool-returning functions.
/// Only call this on functions with Bool return type (aborts, requires, ensures).
pub fn normalize_unit_branches(node: IRNode) -> IRNode {
    normalize_unit_in_bool_ifs(node)
}

/// Remove identity let bindings: `let x := x` -> removed
pub fn remove_identity_lets(node: IRNode) -> IRNode {
    node.map(&mut |n| {
        if is_identity_let(&n) {
            if let IRNode::Let { body, .. } = n {
                return *body;
            }
        }
        n
    })
}

fn is_identity_let(ir: &IRNode) -> bool {
    single_pattern_let(ir)
        .map(|(name, value)| matches!(value, IRNode::Var(v) if v.as_ref() == name.as_ref()))
        .unwrap_or(false)
}

fn single_pattern_let(ir: &IRNode) -> Option<(&Rc<str>, &IRNode)> {
    match ir {
        IRNode::Let { pattern, value, .. } if pattern.len() == 1 => {
            Some((&pattern[0], value.as_ref()))
        }
        _ => None,
    }
}

/// Get the effective value if it's a boolean constant.
/// Returns None if the node has side effects (like function calls) that must be preserved.
fn get_bool_const(node: &IRNode) -> Option<bool> {
    match node {
        IRNode::Const(Const::Bool(b)) => Some(*b),
        // For Let with empty pattern (sequencing), we can only simplify if the value is pure
        IRNode::Let {
            pattern,
            value,
            body,
        } => {
            if pattern.is_empty() && !is_pure_for_bool_const(value) {
                // Sequencing Let with side effects - can't simplify
                return None;
            }
            get_bool_const(body)
        }
        _ => None,
    }
}

/// Check if an expression is pure (no side effects) for the purpose of get_bool_const.
fn is_pure_for_bool_const(node: &IRNode) -> bool {
    match node {
        IRNode::Const(_) | IRNode::Var(_) => true,
        IRNode::Tuple(elems) => elems.iter().all(is_pure_for_bool_const),
        IRNode::BinOp { lhs, rhs, .. } => {
            is_pure_for_bool_const(lhs) && is_pure_for_bool_const(rhs)
        }
        IRNode::UnOp { operand, .. } => is_pure_for_bool_const(operand),
        IRNode::Let { value, body, .. } => {
            is_pure_for_bool_const(value) && is_pure_for_bool_const(body)
        }
        IRNode::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            is_pure_for_bool_const(cond)
                && is_pure_for_bool_const(then_branch)
                && is_pure_for_bool_const(else_branch)
        }
        // Function calls are never pure - they may abort, mutate, or have other effects
        IRNode::Call { .. } => false,
        // Everything else potentially has side effects
        _ => false,
    }
}

/// Check if a node produces Unit at the type level.
/// This is used for normalize_unit_branches which replaces unit-valued branches with `false`
/// in Bool-returning functions. We're intentionally aggressive here because:
/// 1. Computations in spec/aborts functions don't have side effects that matter
/// 2. The only thing that matters is whether the branch returns true, false, or unit
fn is_unit_valued(node: &IRNode) -> bool {
    match node {
        IRNode::Tuple(v) if v.is_empty() => true,
        IRNode::Let { body, .. } => {
            // For any Let, recursively check the body
            // We don't check purity here because in Bool-returning functions (aborts, etc.),
            // the computations don't have meaningful side effects - only the final Bool matters
            is_unit_valued(body)
        }
        _ => false,
    }
}

/// Replace unit-valued if-branches with `false` when the other branch is boolean.
/// This fixes aborts functions where one branch aborts (true) and the other
/// has body computations ending with () instead of false.
fn normalize_unit_in_bool_ifs(node: IRNode) -> IRNode {
    node.map(&mut |n| match n {
        IRNode::If {
            cond,
            then_branch,
            else_branch,
        } => {
            let then_is_unit = is_unit_valued(&then_branch);
            let else_is_unit = is_unit_valued(&else_branch);

            // Replace unit-valued branches with false.
            // In aborts functions, () means "no abort here" which is false.
            let then_branch = if then_is_unit {
                Box::new(IRNode::Const(Const::Bool(false)))
            } else {
                then_branch
            };
            let else_branch = if else_is_unit {
                Box::new(IRNode::Const(Const::Bool(false)))
            } else {
                else_branch
            };
            IRNode::If {
                cond,
                then_branch,
                else_branch,
            }
        }
        other => other,
    })
}

/// Simplify boolean if expressions recursively
/// - `if cond then true else false` -> `cond`
/// - `if cond then false else true` -> `!cond`
fn simplify_boolean_ifs(node: IRNode) -> IRNode {
    node.map(&mut |n| match n {
        IRNode::If {
            cond,
            then_branch,
            else_branch,
        } => {
            // Check if both branches are boolean constants (handles wrapped cases)
            let then_is_true = get_bool_const(&then_branch) == Some(true);
            let then_is_false = get_bool_const(&then_branch) == Some(false);
            let else_is_true = get_bool_const(&else_branch) == Some(true);
            let else_is_false = get_bool_const(&else_branch) == Some(false);

            if then_is_true && else_is_false {
                // if cond then true else false -> cond
                *cond
            } else if then_is_false && else_is_true {
                // if cond then false else true -> !cond
                IRNode::UnOp {
                    op: crate::UnOp::Not,
                    operand: cond,
                }
            } else {
                // Keep as is
                IRNode::If {
                    cond,
                    then_branch,
                    else_branch,
                }
            }
        }
        other => other,
    })
}

/// Convert nested boolean if patterns to AND/OR operations
/// Patterns:
/// - `if cond1 then cond2 else false` -> `cond1 && cond2` (short-circuit AND)
/// - `if cond1 then true else cond2` -> `cond1 || cond2` (short-circuit OR)
fn convert_boolean_ifs_to_and_or(
    node: IRNode,
    reg: &mut VariableRegistry,
    self_fn: Option<usize>,
) -> IRNode {
    match node {
        IRNode::Let {
            pattern,
            value,
            body,
        } => {
            let value = Box::new(convert_boolean_ifs_to_and_or(*value, reg, self_fn));
            let let_node = IRNode::Let {
                pattern: pattern.clone(),
                value,
                body: Box::new(IRNode::Tuple(vec![])),
            };
            reg.add_node(&let_node);
            let IRNode::Let { pattern, value, .. } = let_node else {
                unreachable!()
            };
            IRNode::Let {
                pattern,
                value,
                body: Box::new(convert_boolean_ifs_to_and_or(*body, reg, self_fn)),
            }
        }
        IRNode::If {
            cond,
            then_branch,
            else_branch,
        } => {
            let cond = Box::new(convert_boolean_ifs_to_and_or(*cond, reg, self_fn));
            let then_branch = Box::new(convert_boolean_ifs_to_and_or(*then_branch, reg, self_fn));
            let else_branch = Box::new(convert_boolean_ifs_to_and_or(*else_branch, reg, self_fn));

            if let (Some(then_val), Some(else_val)) =
                (get_bool_const(&then_branch), get_bool_const(&else_branch))
            {
                if then_val == else_val {
                    return IRNode::Const(Const::Bool(then_val));
                }
            }

            let then_is_true = get_bool_const(&then_branch) == Some(true);
            let then_is_false = get_bool_const(&then_branch) == Some(false);
            let else_is_true = get_bool_const(&else_branch) == Some(true);
            let else_is_false = get_bool_const(&else_branch) == Some(false);

            // Do NOT collapse `if c then b else false` (or the dual Or form) into
            // `c && b` when the kept branch is a *self-recursive* tail call. While-loop
            // bodies are emitted as `if guard then (... recurse) else false`; collapsing
            // to `guard && (... recurse)` moves the recursive call into a Bool `&&`,
            // where Lean's well-founded recursion no longer threads the `guard = true`
            // hypothesis into the decreasing-measure proof. Keeping the `if` preserves
            // guard-threading so the termination measure can discharge. We restrict the
            // guard to calls that target the function being optimized (`self_fn`), so
            // ordinary boolean predicates like `is_u64 x = (0 ≤ x) && (x ≤ max)` — whose
            // tail is a call to a *different* helper (`Integer.lte`) — still collapse.
            if else_is_false && !then_is_false && !branch_is_self_recursive(&then_branch, self_fn) {
                if is_boolean_type(&then_branch, reg) {
                    return IRNode::BinOp {
                        op: BinOp::And,
                        lhs: cond,
                        rhs: then_branch,
                    };
                }
            }

            if then_is_true && !else_is_true && !branch_is_self_recursive(&else_branch, self_fn) {
                if is_boolean_type(&else_branch, reg) {
                    return IRNode::BinOp {
                        op: BinOp::Or,
                        lhs: cond,
                        rhs: else_branch,
                    };
                }
            }

            IRNode::If {
                cond,
                then_branch,
                else_branch,
            }
        }
        other => other.map(&mut |n| n),
    }
}

/// Whether a branch contains a *self-recursive* call anywhere (a `Call`
/// targeting `self_fn`, the function being optimized). While-loop bodies emit
/// their recursive iteration inside the guarded branch — either as a tail call
/// (`if k == key then true else recurse`) or as a discarded sequencing step in
/// an `.aborts` body (`let _ := recurse; false`). In both cases we must keep the
/// enclosing `if` (rather than collapse to `&&`/`||`) so Lean's well-founded
/// recursion threads the loop guard into the decreasing-measure proof. Calls to
/// *other* helpers (e.g. `Integer.lte` in `is_u64 = (0 ≤ x) && (x ≤ max)`) never
/// match `self_fn`, so genuine boolean predicates still collapse normally.
fn branch_is_self_recursive(node: &IRNode, self_fn: Option<usize>) -> bool {
    let Some(self_fn) = self_fn else {
        return false;
    };
    node.calls().any(|f| f == self_fn)
}

/// Check if an IR node has a boolean type.
/// For If nodes, checks BOTH branches (get_type only checks then-branch,
/// which gives false positives when the else-branch has a different type
/// e.g. in folded early returns: `if a>b then true else if b>a then false else ...`).
fn is_boolean_type(node: &IRNode, reg: &VariableRegistry) -> bool {
    match node {
        IRNode::If {
            then_branch,
            else_branch,
            ..
        } => is_boolean_type(then_branch, reg) && is_boolean_type(else_branch, reg),
        IRNode::Let { body, .. } => is_boolean_type(body, reg),
        _ => matches!(node.get_type(reg), Type::Bool),
    }
}

/// Collapse common patterns where a variable is bound and immediately used.
///
/// Pattern: Let { x = v, body: Var("x") } -> v
///
/// These patterns arise from Move code that assigns to a variable in branches
/// but our temp inlining can't track that the variable is defined in all branches.
fn collapse_branch_bindings(node: IRNode) -> IRNode {
    // Run to fixpoint since transformations can expose new patterns
    let mut result = node;
    loop {
        let prev = result.clone();
        result = collapse_once(result);
        if result == prev {
            break;
        }
    }
    result
}

fn collapse_once(node: IRNode) -> IRNode {
    node.map(&mut |n| {
        // Pattern: Let { pattern: [x], value: v, body: Var(x) } -> v
        // Exclude WriteBack: it renders as `Mutable.apply child` and needs the
        // Let binding (`let parent := Mutable.apply child`) to capture the result.
        // Without the Let, WriteBack becomes a bare expression that Lean can't use.
        if let IRNode::Let {
            pattern,
            value,
            body,
        } = &n
        {
            if pattern.len() == 1 && !matches!(value.as_ref(), IRNode::WriteBack { .. }) {
                if let IRNode::Var(var_name) = body.as_ref() {
                    if pattern[0].as_ref() == var_name.as_ref() {
                        return (**value).clone();
                    }
                }
            }
        }

        // Pattern: Let { pattern: [] or ["_"], value: v, body: () } -> v
        // This handles: `let _ := result; ()` -> `result`
        // Exclude WriteRef and WriteBack: they render as expressions
        // (Mutable.set/Mutable.apply) that Lean interprets as function application
        // when followed by `()`.
        if let IRNode::Let {
            pattern,
            value,
            body,
        } = &n
        {
            let is_wildcard_pattern =
                pattern.is_empty() || (pattern.len() == 1 && pattern[0].as_ref() == "_");
            if is_wildcard_pattern
                && !matches!(
                    value.as_ref(),
                    IRNode::WriteRef { .. } | IRNode::WriteBack { .. }
                )
            {
                if let IRNode::Tuple(elems) = body.as_ref() {
                    if elems.is_empty() {
                        return (**value).clone();
                    }
                }
            }
        }

        // Pattern: Let { pattern: [x], value: If { ... }, body: Var(x) } where branches produce x
        if let IRNode::Let {
            pattern,
            value,
            body,
        } = &n
        {
            if pattern.len() == 1 {
                if let IRNode::Var(var_name) = body.as_ref() {
                    if pattern[0].as_ref() == var_name.as_ref() {
                        if let IRNode::If {
                            cond,
                            then_branch,
                            else_branch,
                        } = value.as_ref()
                        {
                            if let (Some(then_val), Some(else_val)) = (
                                extract_single_let_value(then_branch, var_name),
                                extract_single_let_value(else_branch, var_name),
                            ) {
                                return IRNode::If {
                                    cond: cond.clone(),
                                    then_branch: Box::new(then_val),
                                    else_branch: Box::new(else_val),
                                };
                            }
                        }
                    }
                }
            }
        }
        n
    })
}

/// Extract the value from a Let binding to the given variable name.
fn extract_single_let_value(node: &IRNode, var_name: &Rc<str>) -> Option<IRNode> {
    match node {
        IRNode::Let {
            pattern,
            value,
            body,
        } => {
            if pattern.len() == 1 && pattern[0].as_ref() == var_name.as_ref() {
                // Check if body is empty tuple - means this Let is the final binding
                if matches!(body.as_ref(), IRNode::Tuple(v) if v.is_empty()) {
                    return Some((**value).clone());
                }
            }
            // Recurse into the body
            extract_single_let_value(body, var_name)
        }
        _ => None,
    }
}

/// Fix nested if-else chains where some branches return unit and the deepest
/// else returns a value.
///
/// Pattern:
/// ```
/// if A then (effect; ()) else (if B then (effect; ()) else value)
/// ```
/// Transforms to:
/// ```
/// if A then (effect; value) else (if B then (effect; value) else value)
/// ```
///
/// This fixes type mismatches from CFG reconstruction where sequential
/// if-statements in Move are incorrectly merged into nested if-else expressions.
pub fn flatten_sequential_ifs(node: IRNode, reg: &mut VariableRegistry) -> IRNode {
    let mut result = node;
    loop {
        let prev = result.clone();
        result = fix_nested_if_types(result, reg);
        if result == prev {
            break;
        }
    }
    result
}

fn fix_nested_if_types(node: IRNode, reg: &mut VariableRegistry) -> IRNode {
    let result = node.map(&mut |n| {
        if let IRNode::If {
            cond,
            then_branch,
            else_branch,
        } = &n
        {
            let then_ends_unit = ends_with_unit(then_branch, reg);
            let else_ends_unit = ends_with_unit(else_branch, reg);

            if !then_ends_unit || else_ends_unit {
                return n;
            }

            let unit_then = make_return_unit(then_branch);

            let seq_if = IRNode::If {
                cond: cond.clone(),
                then_branch: Box::new(unit_then),
                else_branch: Box::new(IRNode::Tuple(vec![])),
            };

            return IRNode::Let {
                pattern: vec![],
                value: Box::new(seq_if),
                body: else_branch.clone(),
            };
        }
        n
    });
    result
}

/// Make an expression return () explicitly at the end.
/// For WriteRef and unit-returning Calls, wrap them in a Let that returns ().
fn make_return_unit(node: &IRNode) -> IRNode {
    match node {
        IRNode::Tuple(v) if v.is_empty() => node.clone(),
        IRNode::WriteRef { .. } | IRNode::Call { .. } => {
            // These return unit, wrap them to make it explicit
            IRNode::Let {
                pattern: vec![],
                value: Box::new(node.clone()),
                body: Box::new(IRNode::Tuple(vec![])),
            }
        }
        IRNode::Let {
            pattern,
            value,
            body,
        } => IRNode::Let {
            pattern: pattern.clone(),
            value: value.clone(),
            body: Box::new(make_return_unit(body)),
        },
        IRNode::If {
            cond,
            then_branch,
            else_branch,
        } => IRNode::If {
            cond: cond.clone(),
            then_branch: Box::new(make_return_unit(then_branch)),
            else_branch: Box::new(make_return_unit(else_branch)),
        },
        _ => node.clone(),
    }
}

/// Check if an IR node ends with unit (empty tuple).
fn ends_with_unit(node: &IRNode, reg: &VariableRegistry) -> bool {
    ends_with_unit_inner(node, reg, 0)
}

fn ends_with_unit_inner(node: &IRNode, reg: &VariableRegistry, depth: usize) -> bool {
    if depth > 100 {
        return false;
    }
    match node {
        IRNode::Tuple(v) if v.is_empty() => true,
        IRNode::WriteRef { .. } => true,
        IRNode::Call { function, .. } => {
            if let Some(f) = reg.program().functions.try_get(function) {
                matches!(&f.signature.return_type, Type::Tuple(v) if v.is_empty())
            } else {
                false
            }
        }
        IRNode::Let { body, .. } => ends_with_unit_inner(body, reg, depth + 1),
        IRNode::If {
            then_branch,
            else_branch,
            ..
        } => {
            ends_with_unit_inner(then_branch, reg, depth + 1)
                && ends_with_unit_inner(else_branch, reg, depth + 1)
        }
        _ => false,
    }
}

/// Fix if-then-else branches with mixed Bool/Prop types in Prop-returning functions.
///
/// In .aborts/.requires/.ensures functions, intermediate computations (==, !=)
/// return Bool while recursive calls and comparisons (<, ∧) return Prop.
/// When both appear in branches of the same if-then-else, Lean can't unify types.
///
/// This pass walks the entire body, finds if-then-else nodes where one branch
/// is Bool and the other is Prop, and wraps the Bool branch(es) with ToProp
/// (rendered as `(expr = true)`).
///
/// Also wraps Bool-typed tail expressions of the function with ToProp.
pub fn lift_bool_tails_to_prop(node: IRNode, reg: &mut VariableRegistry) -> IRNode {
    lift_tail(node, reg)
}

pub fn fix_mixed_if_branches(node: IRNode, reg: &mut VariableRegistry) -> IRNode {
    match node {
        IRNode::Let {
            pattern,
            value,
            body,
        } => {
            let value = Box::new(fix_mixed_if_branches(*value, reg));
            let let_node = IRNode::Let {
                pattern: pattern.clone(),
                value,
                body: Box::new(IRNode::Tuple(vec![])),
            };
            reg.add_node(&let_node);
            let IRNode::Let { pattern, value, .. } = let_node else {
                unreachable!()
            };
            IRNode::Let {
                pattern,
                value,
                body: Box::new(fix_mixed_if_branches(*body, reg)),
            }
        }
        IRNode::If {
            cond,
            then_branch,
            else_branch,
        } => {
            let cond = Box::new(fix_mixed_if_branches(*cond, reg));
            let then_branch = Box::new(fix_mixed_if_branches(*then_branch, reg));
            let else_branch = Box::new(fix_mixed_if_branches(*else_branch, reg));

            let then_ty = then_branch.get_type(reg);
            let else_ty = else_branch.get_type(reg);

            let then_is_bool = matches!(then_ty, Type::Bool);
            let else_is_bool = matches!(else_ty, Type::Bool);
            let then_is_prop = matches!(then_ty, Type::Prop);
            let else_is_prop = matches!(else_ty, Type::Prop);

            if (then_is_bool && else_is_prop) || (then_is_prop && else_is_bool) {
                let new_then = if then_is_bool {
                    Box::new(wrap_branch_in_to_prop(*then_branch))
                } else {
                    then_branch
                };
                let new_else = if else_is_bool {
                    Box::new(wrap_branch_in_to_prop(*else_branch))
                } else {
                    else_branch
                };
                return IRNode::If {
                    cond,
                    then_branch: new_then,
                    else_branch: new_else,
                };
            }

            IRNode::If {
                cond,
                then_branch,
                else_branch,
            }
        }
        other => other.map(&mut |n| n),
    }
}

fn wrap_branch_in_to_prop(node: IRNode) -> IRNode {
    match node {
        IRNode::Let {
            pattern,
            value,
            body,
        } => IRNode::Let {
            pattern,
            value,
            body: Box::new(wrap_branch_in_to_prop(*body)),
        },
        IRNode::If {
            cond,
            then_branch,
            else_branch,
        } => IRNode::If {
            cond,
            then_branch: Box::new(wrap_branch_in_to_prop(*then_branch)),
            else_branch: Box::new(wrap_branch_in_to_prop(*else_branch)),
        },
        other => IRNode::ToProp(Box::new(other)),
    }
}

fn lift_tail(node: IRNode, reg: &mut VariableRegistry) -> IRNode {
    match node {
        IRNode::Let {
            pattern,
            value,
            body,
        } => {
            let has_prop = contains_prop(&value, reg);
            let value = if has_prop {
                Box::new(bool_chain_to_prop(*value, reg))
            } else {
                value
            };
            let let_node = IRNode::Let {
                pattern: pattern.clone(),
                value,
                body: Box::new(IRNode::Tuple(vec![])),
            };
            reg.add_node(&let_node);
            let IRNode::Let { pattern, value, .. } = let_node else {
                unreachable!()
            };
            IRNode::Let {
                pattern,
                value,
                body: Box::new(lift_tail(*body, reg)),
            }
        }
        IRNode::If {
            cond,
            then_branch,
            else_branch,
        } => {
            let new_then = lift_tail(*then_branch, reg);
            let new_else = lift_tail(*else_branch, reg);
            IRNode::If {
                cond,
                then_branch: Box::new(new_then),
                else_branch: Box::new(new_else),
            }
        }
        other => match other.get_type(reg) {
            Type::Bool => IRNode::ToProp(Box::new(other)),
            _ => other,
        },
    }
}

fn contains_prop(node: &IRNode, reg: &VariableRegistry) -> bool {
    match node {
        IRNode::BinOp { op, lhs, rhs } => {
            if matches!(op, BinOp::And | BinOp::Or) {
                contains_prop(lhs, reg) || contains_prop(rhs, reg)
            } else {
                false
            }
        }
        IRNode::Let { value, body, .. } => contains_prop(value, reg) || contains_prop(body, reg),
        IRNode::If {
            then_branch,
            else_branch,
            ..
        } => contains_prop(then_branch, reg) || contains_prop(else_branch, reg),
        IRNode::Call { function, .. } => {
            matches!(reg.function_return_type(*function), Type::Prop)
        }
        IRNode::ToProp(_) => true,
        IRNode::Var(name) => reg.contains(name) && matches!(reg.get_type(name), Type::Prop),
        _ => false,
    }
}

fn bool_chain_to_prop(node: IRNode, reg: &mut VariableRegistry) -> IRNode {
    match node {
        IRNode::BinOp {
            op: crate::BinOp::And,
            lhs,
            rhs,
        } => {
            let lhs_prop = to_prop_expr(*lhs, reg);
            let rhs_prop = to_prop_expr(*rhs, reg);
            IRNode::BinOp {
                op: crate::BinOp::And,
                lhs: Box::new(lhs_prop),
                rhs: Box::new(rhs_prop),
            }
        }
        IRNode::Let {
            pattern,
            value,
            body,
        } => {
            let value = if contains_prop(&value, reg) {
                Box::new(bool_chain_to_prop(*value, reg))
            } else {
                value
            };
            let let_node = IRNode::Let {
                pattern: pattern.clone(),
                value,
                body: Box::new(IRNode::Tuple(vec![])),
            };
            reg.add_node(&let_node);
            let IRNode::Let { pattern, value, .. } = let_node else {
                unreachable!()
            };
            IRNode::Let {
                pattern,
                value,
                body: Box::new(bool_chain_to_prop(*body, reg)),
            }
        }
        other => to_prop_expr(other, reg),
    }
}

fn to_prop_expr(node: IRNode, reg: &VariableRegistry) -> IRNode {
    match node.get_type(reg) {
        Type::Prop => node,
        Type::Bool => IRNode::ToProp(Box::new(node)),
        _ => {
            if let IRNode::BinOp {
                op: crate::BinOp::And,
                ..
            } = &node
            {
                bool_chain_to_prop(node, &mut reg.clone())
            } else if let IRNode::Let { .. } = &node {
                bool_chain_to_prop(node, &mut reg.clone())
            } else {
                IRNode::ToProp(Box::new(node))
            }
        }
    }
}

// ============================================================================
// Peephole: coalesce shadow update + self-noop UpdateField
// ============================================================================
//
// `mutable_threading` (and the upstream stackless bytecode → IR translator)
// occasionally emit a sequence shaped like:
//
//   let X := Y                                    -- alias of Y
//   ...
//   let snap := Y.f                               -- snapshot of Y.f
//   let X := { X with f := EXPR }                 -- shadow update on the alias
//   let Y := { Y with f := snap }                 -- self-noop on Y
//
// where `X != Y`, both UpdateField nodes target the same struct field, and
// `snap` was bound earlier as `let snap := Y.f` (with no intervening
// rebinding of `Y` or `snap`).
//
// Semantically this is wrong: the update intended for `Y.f` lands on the
// dead alias `X` while `Y.f` is set back to its old value. The Move source
// `Y.f = EXPR` should produce a single update on `Y`, but the bytecode-level
// borrow chain produces a split that downstream passes do not recombine.
//
// This peephole detects that exact split and rewrites the self-noop to a
// real update on `Y` carrying `EXPR` (with `X -> Y` substitution, since `X`
// was just a copy of `Y`):
//
//   let Y := { Y with f := EXPR[X->Y] }
//
// The dead shadow update `let X := { X with f := EXPR }` is left in place
// and removed by `dead_code_removal` if `X` is unused downstream.

pub fn coalesce_shadow_self_noop_updates(node: IRNode) -> IRNode {
    let env = CoalesceEnv::default();
    coalesce_walk(node, &env)
}

#[derive(Clone, Default)]
struct CoalesceEnv {
    snapshots: BTreeMap<TempId, (StructID, usize, TempId)>,
    aliases: BTreeMap<TempId, TempId>,
}

/// Whether an update is on a plain struct value or wrapped in WriteRef
/// (mutable reference, e.g. `Mutable.set t (UpdateField ...)`).
#[derive(Clone, Copy, PartialEq, Eq)]
enum UpdateKind {
    Plain,
    WriteRef,
}

/// Recognise both plain and WriteRef-wrapped self-update shapes:
///
///   Plain:    `UpdateField { base: Var(X), struct_id, field_index, value }`
///   WriteRef: `WriteRef { reference: Var(X),
///       value: UpdateField { base: ReadRef(Var(X)), struct_id,
///                            field_index, value } }`
///
/// Returns `(base_var, struct_id, field_index, &value, kind)` when the
/// node matches; `None` otherwise.
fn extract_self_update(node: &IRNode) -> Option<(&TempId, StructID, usize, &IRNode, UpdateKind)> {
    match node {
        IRNode::UpdateField {
            base,
            struct_id,
            field_index,
            value,
        } => {
            if let IRNode::Var(b) = base.as_ref() {
                Some((
                    b,
                    *struct_id,
                    *field_index,
                    value.as_ref(),
                    UpdateKind::Plain,
                ))
            } else {
                None
            }
        }
        IRNode::WriteRef {
            reference,
            value: write_val,
        } => {
            let ref_var = if let IRNode::Var(b) = reference.as_ref() {
                b
            } else {
                return None;
            };
            if let IRNode::UpdateField {
                base,
                struct_id,
                field_index,
                value,
            } = write_val.as_ref()
            {
                // The IR carries `base: Var(X)` directly; the renderer
                // adds `(Mutable.val ...)` based on type. Accept both
                // forms for robustness.
                let base_var = match base.as_ref() {
                    IRNode::Var(b) => Some(b),
                    IRNode::ReadRef(inner) => {
                        if let IRNode::Var(b) = inner.as_ref() {
                            Some(b)
                        } else {
                            None
                        }
                    }
                    _ => None,
                };
                if let Some(b) = base_var {
                    if b == ref_var {
                        return Some((
                            ref_var,
                            *struct_id,
                            *field_index,
                            value.as_ref(),
                            UpdateKind::WriteRef,
                        ));
                    }
                }
            }
            None
        }
        _ => None,
    }
}

/// Recognise a snapshot binding shape: `let snap := X.f` either via a
/// plain `Field { base: Var(X), .. }` or a Mutable-wrapped
/// `Field { base: ReadRef(Var(X)), .. }`. Returns `(struct_id,
/// field_index, base_var)` on match, `None` otherwise.
fn extract_field_snapshot(node: &IRNode) -> Option<(StructID, usize, &TempId)> {
    if let IRNode::Field {
        base,
        struct_id,
        field_index,
    } = node
    {
        let base_var = match base.as_ref() {
            IRNode::Var(b) => Some(b),
            IRNode::ReadRef(inner) => {
                if let IRNode::Var(b) = inner.as_ref() {
                    Some(b)
                } else {
                    None
                }
            }
            _ => None,
        };
        return base_var.map(|b| (*struct_id, *field_index, b));
    }
    None
}

/// Reconstruct a self-update with `value` swapped for the given inner
/// expression, preserving the original `UpdateKind`.
fn rebuild_self_update(
    base_var: &TempId,
    struct_id: StructID,
    field_index: usize,
    new_value: IRNode,
    kind: UpdateKind,
) -> IRNode {
    match kind {
        UpdateKind::Plain => IRNode::UpdateField {
            base: Box::new(IRNode::Var(base_var.clone())),
            struct_id,
            field_index,
            value: Box::new(new_value),
        },
        UpdateKind::WriteRef => IRNode::WriteRef {
            reference: Box::new(IRNode::Var(base_var.clone())),
            value: Box::new(IRNode::UpdateField {
                base: Box::new(IRNode::ReadRef(Box::new(IRNode::Var(base_var.clone())))),
                struct_id,
                field_index,
                value: Box::new(new_value),
            }),
        },
    }
}

fn coalesce_walk(node: IRNode, env: &CoalesceEnv) -> IRNode {
    match node {
        IRNode::Let { .. } => {
            let (bindings, tail) = unroll_let_chain(node);
            // Apply the peephole as we process each binding so that
            // recursion into binding values uses the accumulated in-chain
            // env (alias / snapshot bindings established earlier in the
            // same chain are visible to inner Let / If bodies inside a
            // later binding's value).
            let (bindings, exit_env, latest_shadow_at_tail) =
                apply_coalesce_peephole(bindings, env.clone());
            let tail = coalesce_walk(tail, &exit_env);
            // Tail-position self-noop: a function-body / branch tail of
            // shape `{ Y with f := snap }` where `snap = Y.f` reverts a
            // preceding shadow self-update. Rewrite the tail to `Var(Y)`
            // so the shadow update's new value is what gets returned.
            let tail = coalesce_tail_self_noop(tail, &exit_env, &latest_shadow_at_tail, &bindings);
            rebuild_let_chain(bindings, tail)
        }
        IRNode::If {
            cond,
            then_branch,
            else_branch,
        } => IRNode::If {
            cond: Box::new(coalesce_walk(*cond, env)),
            then_branch: Box::new(coalesce_walk(*then_branch, env)),
            else_branch: Box::new(coalesce_walk(*else_branch, env)),
        },
        IRNode::Match { scrutinee, cases } => IRNode::Match {
            scrutinee: Box::new(coalesce_walk(*scrutinee, env)),
            cases: cases
                .into_iter()
                .map(|(idx, params, body)| (idx, params, coalesce_walk(body, env)))
                .collect(),
        },
        IRNode::MatchOption {
            scrutinee,
            binding,
            some_branch,
            none_branch,
        } => IRNode::MatchOption {
            scrutinee: Box::new(coalesce_walk(*scrutinee, env)),
            binding,
            some_branch: Box::new(coalesce_walk(*some_branch, env)),
            none_branch: Box::new(coalesce_walk(*none_branch, env)),
        },
        // Atoms and other compound nodes that do not introduce a new chain
        // context: recurse uniformly via `map`, redirecting nested chain
        // / branching nodes back into `coalesce_walk` with the outer env.
        other => {
            let env = env.clone();
            other.map(&mut |n| match n {
                IRNode::Let { .. }
                | IRNode::If { .. }
                | IRNode::Match { .. }
                | IRNode::MatchOption { .. } => coalesce_walk(n, &env),
                x => x,
            })
        }
    }
}

/// Unroll a Let chain into a list of (pattern, value) bindings and a tail.
fn unroll_let_chain(node: IRNode) -> (Vec<(Vec<TempId>, IRNode)>, IRNode) {
    let mut bindings = Vec::new();
    let mut current = node;
    while let IRNode::Let {
        pattern,
        value,
        body,
    } = current
    {
        bindings.push((pattern, *value));
        current = *body;
    }
    (bindings, current)
}

/// Rebuild a Let chain from a list of bindings and a tail.
fn rebuild_let_chain(bindings: Vec<(Vec<TempId>, IRNode)>, tail: IRNode) -> IRNode {
    let mut current = tail;
    for (pattern, value) in bindings.into_iter().rev() {
        current = IRNode::Let {
            pattern,
            value: Box::new(value),
            body: Box::new(current),
        };
    }
    current
}

/// Apply the peephole over a flat list of bindings. Returns the rewritten
/// chain, the env extended with bindings that escape into the tail (alias
/// / snapshot map after all invalidations), and the per-chain
/// latest_shadow map at the point where the tail starts (used by the
/// tail-position self-noop rewrite).
fn apply_coalesce_peephole(
    bindings: Vec<(Vec<TempId>, IRNode)>,
    env: CoalesceEnv,
) -> (
    Vec<(Vec<TempId>, IRNode)>,
    CoalesceEnv,
    BTreeMap<(TempId, StructID, usize), usize>,
) {
    // Snapshots / aliases inherit from `env` so peephole detection works
    // when the alias / snapshot binding lives in an enclosing chain.
    let mut snapshots = env.snapshots;
    let mut aliases = env.aliases;
    // Most recent shadow update on `(base_var, struct_id, field_idx)`:
    // index into `out` of the most recent
    // `let X := UpdateField{base=X, field=f, value=EXPR}` for that key.
    // Stays per-chain — outer-chain shadow updates that were not coalesced
    // there have already settled into the IR by the time we reach this
    // chain, and shadowing across If / Match boundaries cannot be safely
    // coalesced anyway.
    let mut latest_shadow: BTreeMap<(TempId, StructID, usize), usize> = BTreeMap::new();

    let mut out: Vec<(Vec<TempId>, IRNode)> = Vec::with_capacity(bindings.len());

    for (pattern, value) in bindings {
        // Recurse into the binding value FIRST with the accumulated env
        // (so far in the chain). This ensures inner Let / If bodies
        // inside the value see alias / snapshot bindings established
        // earlier in the same chain.
        let value = coalesce_walk(
            value,
            &CoalesceEnv {
                snapshots: snapshots.clone(),
                aliases: aliases.clone(),
            },
        );

        // Step 1: try to detect self-noop pattern.
        if pattern.len() == 1 {
            let y_var = pattern[0].clone();
            if let Some((base_var, struct_id, field_index, upd_val, kind)) =
                extract_self_update(&value)
            {
                if base_var == &y_var {
                    if let IRNode::Var(snap_var) = upd_val {
                        if let Some((snap_sid, snap_fid, snap_base)) = snapshots.get(snap_var) {
                            if *snap_sid == struct_id
                                && *snap_fid == field_index
                                && snap_base == &y_var
                            {
                                if let Some(shadow_idx) = find_shadow_for_y(
                                    &out,
                                    &latest_shadow,
                                    &aliases,
                                    &y_var,
                                    struct_id,
                                    field_index,
                                ) {
                                    let (shadow_pat, shadow_val) = &out[shadow_idx];
                                    let x_var = shadow_pat[0].clone();
                                    let expr = if let Some((_, _, _, e, _)) =
                                        extract_self_update(shadow_val)
                                    {
                                        e.clone()
                                    } else {
                                        unreachable!()
                                    };
                                    let mut subs: BTreeMap<String, String> = BTreeMap::new();
                                    subs.insert(x_var.to_string(), y_var.to_string());
                                    let new_expr = expr.substitute_vars(&subs);
                                    let new_value = rebuild_self_update(
                                        &y_var,
                                        struct_id,
                                        field_index,
                                        new_expr,
                                        kind,
                                    );
                                    // The fix produces a shadow self-update
                                    // on y_var, so apply the same partial
                                    // invalidation we use for shadow
                                    // self-updates: drop only snapshots
                                    // whose base is y_var (their cached
                                    // values are stale relative to the
                                    // new field value) and shadow entries
                                    // keyed on y_var (about to be
                                    // overwritten). Leave aliases alone —
                                    // any `aliases[X] = y_var` is still
                                    // semantically valid since X was
                                    // bound from y_var earlier and the
                                    // shadow update preserves that
                                    // origin relationship.
                                    invalidate_snapshots_for_base(&mut snapshots, &y_var);
                                    let stale: Vec<(TempId, StructID, usize)> = latest_shadow
                                        .keys()
                                        .filter(|(b, _, _)| b == &y_var)
                                        .cloned()
                                        .collect();
                                    for k in stale {
                                        latest_shadow.remove(&k);
                                    }
                                    // Track the new shadow update.
                                    latest_shadow
                                        .insert((y_var.clone(), struct_id, field_index), out.len());
                                    out.push((pattern, new_value));
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
        }

        // A `Direct` WriteBack `let _ := WriteBack { child, parent }`
        // rebinds `parent` to the mutated (post-WriteBack) value — the
        // renderer emits it as `let parent := Mutable.apply child`. It
        // carries an empty pattern, so `invalidate_for_rebind` (driven by
        // `pattern`) never fires for it. Invalidate any snapshot / alias /
        // shadow keyed on `parent` here, otherwise a later
        // `{ parent_owner with f := Var(parent) }` self-update is wrongly
        // matched against the now-stale `parent := owner.f` snapshot and
        // coalesced into the earlier op's temp, silently dropping the
        // mutation.
        if pattern.is_empty() {
            if let IRNode::WriteBack {
                parent,
                edge: crate::data::ir::WriteBackEdge::Direct,
                ..
            } = &value
            {
                let parent = parent.clone();
                invalidate_for_rebind(&mut snapshots, &mut aliases, &mut latest_shadow, &parent);
            }
        }

        // Step 2: invalidations triggered by this binding.
        //
        // A shadow self-update `let X := { X with f := EXPR }` rebinds X
        // but keeps the alias relationship (X is still based on whatever
        // it aliased originally; only field f changed). For all other
        // rebindings, do a full invalidation. We still need to drop any
        // snapshots whose base_var is the rebound var (their cached
        // field values are now stale).
        // Determine whether this binding is a shadow self-update —
        // either a plain `UpdateField { base: Var(X), ... }` or a
        // WriteRef-wrapped `WriteRef { ref: Var(X),
        //     value: UpdateField { base: ReadRef(Var(X)), ... } }`.
        let is_shadow_self_update = pattern.len() == 1
            && extract_self_update(&value)
                .map(|(b, _, _, _, _)| b == &pattern[0])
                .unwrap_or(false);
        for v in &pattern {
            if is_shadow_self_update {
                // A shadow self-update `let X := { X with f := EXPR }`
                // does NOT invalidate snapshots, aliases, or shadow
                // entries — X still refers to the same logical struct
                // (with one field updated), and snapshots whose base
                // is X retain their (old) values which are exactly
                // what the self-noop / revert pattern uses to detect
                // a buggy revert. The new shadow update is recorded
                // in step 3 via `latest_shadow.insert`, which will
                // overwrite any stale entry on the same key.
            } else {
                invalidate_for_rebind(&mut snapshots, &mut aliases, &mut latest_shadow, v);
            }
        }

        // Step 3: track this binding as alias / snapshot / shadow.
        if pattern.len() == 1 {
            let bound = pattern[0].clone();
            // Alias: `let X := Y`
            if let IRNode::Var(base) = &value {
                aliases.insert(bound.clone(), (*base).clone());
            }
            // Snapshot: `let snap := X.f` (plain or via ReadRef)
            if let Some((sid, fid, base_var)) = extract_field_snapshot(&value) {
                snapshots.insert(bound.clone(), (sid, fid, base_var.clone()));
            }
            // Shadow self-update (plain or WriteRef-wrapped)
            if let Some((base_var, sid, fid, _, _)) = extract_self_update(&value) {
                if base_var == &bound {
                    latest_shadow.insert((base_var.clone(), sid, fid), out.len());
                }
            }
        }

        out.push((pattern, value));
    }

    (out, CoalesceEnv { snapshots, aliases }, latest_shadow)
}

/// Rewrite a tail-position self-noop into a plain Var so the preceding
/// shadow self-update's new value is what gets returned. Pattern:
///
///   ... let Y := { Y with f := EXPR } ; { Y with f := Var(snap) }
///
/// where `snap = Y.f` was bound before the shadow update. The tail
/// reverts the shadow's update; rewriting it to `Var(Y)` returns Y with
/// the new field value.
fn coalesce_tail_self_noop(
    tail: IRNode,
    env: &CoalesceEnv,
    latest_shadow: &BTreeMap<(TempId, StructID, usize), usize>,
    bindings: &[(Vec<TempId>, IRNode)],
) -> IRNode {
    if let Some((y_var, struct_id, field_index, upd_val, _kind)) = extract_self_update(&tail) {
        if let IRNode::Var(snap_var) = upd_val {
            if let Some((snap_sid, snap_fid, snap_base)) = env.snapshots.get(snap_var) {
                if *snap_sid == struct_id && *snap_fid == field_index && snap_base == y_var {
                    if find_shadow_for_y(
                        bindings,
                        latest_shadow,
                        &env.aliases,
                        y_var,
                        struct_id,
                        field_index,
                    )
                    .is_some()
                    {
                        return IRNode::Var(y_var.clone());
                    }
                }
            }
        }
    }
    tail
}

/// Drop snapshots whose base_var is `var`. Used when `var` is rebound via
/// a shadow self-update — its alias relationship survives, but any cached
/// field values from before the update are stale.
fn invalidate_snapshots_for_base(
    snapshots: &mut BTreeMap<TempId, (StructID, usize, TempId)>,
    var: &TempId,
) {
    let stale_keys: Vec<TempId> = snapshots
        .iter()
        .filter_map(
            |(k, (_, _, base))| {
                if base == var {
                    Some(k.clone())
                } else {
                    None
                }
            },
        )
        .collect();
    for k in stale_keys {
        snapshots.remove(&k);
    }
}

/// Invalidate trackers when `var` is rebound: drop any alias / snapshot
/// keyed on `var`, any snapshot whose base_var is `var`, and any shadow
/// indexed by `var` as the base.
fn invalidate_for_rebind(
    snapshots: &mut BTreeMap<TempId, (StructID, usize, TempId)>,
    aliases: &mut BTreeMap<TempId, TempId>,
    latest_shadow: &mut BTreeMap<(TempId, StructID, usize), usize>,
    var: &TempId,
) {
    snapshots.remove(var);
    aliases.remove(var);
    let stale_snap_keys: Vec<TempId> = snapshots
        .iter()
        .filter_map(
            |(k, (_, _, base))| {
                if base == var {
                    Some(k.clone())
                } else {
                    None
                }
            },
        )
        .collect();
    for k in stale_snap_keys {
        snapshots.remove(&k);
    }
    let stale_alias_keys: Vec<TempId> = aliases
        .iter()
        .filter_map(|(k, base)| if base == var { Some(k.clone()) } else { None })
        .collect();
    for k in stale_alias_keys {
        aliases.remove(&k);
    }
    let stale_shadow_keys: Vec<(TempId, StructID, usize)> = latest_shadow
        .keys()
        .filter(|(b, _, _)| b == var)
        .cloned()
        .collect();
    for k in stale_shadow_keys {
        latest_shadow.remove(&k);
    }
}

/// Find the most recent shadow update on some `X` (where `X` is a tracked
/// alias of `y_var`) for the given struct / field combination.
fn find_shadow_for_y(
    out: &[(Vec<TempId>, IRNode)],
    latest_shadow: &BTreeMap<(TempId, StructID, usize), usize>,
    aliases: &BTreeMap<TempId, TempId>,
    y_var: &TempId,
    struct_id: StructID,
    field_index: usize,
) -> Option<usize> {
    let mut best: Option<usize> = None;
    for ((shadow_base, sid, fid), idx) in latest_shadow.iter() {
        if *sid != struct_id || *fid != field_index {
            continue;
        }
        // Two valid cases:
        // (a) `shadow_base == y_var`: the shadow is a previous self-update
        //     on Y itself, and the self-noop after it reverts that update.
        //     Substituting Y -> Y is a no-op, so the shadow's EXPR is
        //     used directly.
        // (b) `shadow_base != y_var` and `aliases[shadow_base] == y_var`:
        //     the shadow is on an alias X of Y (introduced by `let X :=
        //     Y`); the self-noop on Y was meant to update Y but lost the
        //     shadow's EXPR. Substitute X -> Y in the EXPR.
        let case_self = shadow_base == y_var;
        let case_alias = aliases
            .get(shadow_base)
            .map(|a| a == y_var)
            .unwrap_or(false);
        if !case_self && !case_alias {
            continue;
        }
        if let Some((pat, val)) = out.get(*idx) {
            let ok = pat.len() == 1
                && pat[0] == *shadow_base
                && extract_self_update(val)
                    .map(|(b, s, f, _, _)| b == shadow_base && s == struct_id && f == field_index)
                    .unwrap_or(false);
            if ok && best.map(|b| *idx > b).unwrap_or(true) {
                best = Some(*idx);
            }
        }
    }
    best
}

// ============================================================================
// Post-threading phi lift
// ============================================================================
//
// `mutable_threading` rewrites WriteBack ops into `let X := <new value>`
// shadow self-updates inside `If` / `Match` branches. When the
// surrounding control-flow node was wrapped by upstream phi detection
// in `let _ := <If> ; <body>` (because at translation time no variable
// was rebound in the branches yet), the post-threading rebinding of
// `X` is now lexically scoped to the branch and never escapes.
//
// Concretely, Move's `index.do!(|idx| { set.f = ... })` translates to:
//
//   let _ := (if has_index then
//     let set := { set with f := ... }
//     ()
//   else ())
//   <body referencing set>
//
// The `set` referenced in `<body>` is the parameter, not the
// shadow-updated copy from the branch. The mutation is silently lost.
//
// This pass detects empty-pattern Let bindings whose value is an If
// / Match and whose body references variables that are rebound in any
// branch. It lifts those variables to a real phi pattern:
//
//   let (v1, v2, ...) := (if has_index then
//     let set := { set with f := ... }
//     (set, ...)
//   else
//     (set, ...))
//   <body>

pub fn lift_post_threading_phis(node: IRNode) -> IRNode {
    // Fixpoint: phi_lift_walk processes children before parents
    // (bottom-up). When an outer Let's lift extends a branch's
    // terminal to yield extra phi vars, an inner Let's lift inside
    // that branch (which already ran) didn't see those vars in its
    // body's free_vars — so it might have skipped lifting a phi var
    // it could now justify. Re-run until stable so the inner Let
    // catches up.
    let mut current = node;
    for _ in 0..16 {
        let next = phi_lift_walk(current.clone());
        if format!("{:?}", &next) == format!("{:?}", &current) {
            return next;
        }
        current = next;
    }
    current
}

fn phi_lift_walk(node: IRNode) -> IRNode {
    match node {
        IRNode::Let {
            pattern,
            value,
            body,
        } => {
            let value = phi_lift_walk(*value);
            let body = phi_lift_walk(*body);
            // Detect any Let whose value is If / Match / MatchOption
            // and whose body references vars rebound in branches that
            // are not already covered by `pattern`. Extend the pattern
            // with those phi vars (paired into a tuple) and append a
            // `(existing_pattern_value, phis...)` yield to each branch.
            if matches!(
                &value,
                IRNode::If { .. } | IRNode::Match { .. } | IRNode::MatchOption { .. }
            ) {
                if let Some(rewritten) = try_lift_phis(pattern, value, body) {
                    return rewritten;
                }
                unreachable!("try_lift_phis always returns Some")
            }
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
        } => IRNode::If {
            cond: Box::new(phi_lift_walk(*cond)),
            then_branch: Box::new(phi_lift_walk(*then_branch)),
            else_branch: Box::new(phi_lift_walk(*else_branch)),
        },
        IRNode::Match { scrutinee, cases } => IRNode::Match {
            scrutinee: Box::new(phi_lift_walk(*scrutinee)),
            cases: cases
                .into_iter()
                .map(|(idx, params, body)| (idx, params, phi_lift_walk(body)))
                .collect(),
        },
        IRNode::MatchOption {
            scrutinee,
            binding,
            some_branch,
            none_branch,
        } => IRNode::MatchOption {
            scrutinee: Box::new(phi_lift_walk(*scrutinee)),
            binding,
            some_branch: Box::new(phi_lift_walk(*some_branch)),
            none_branch: Box::new(phi_lift_walk(*none_branch)),
        },
        other => other.map(&mut |n| match n {
            IRNode::Let { .. }
            | IRNode::If { .. }
            | IRNode::Match { .. }
            | IRNode::MatchOption { .. } => phi_lift_walk(n),
            x => x,
        }),
    }
}

/// Returns the rewritten Let, lifting branch-rebound vars referenced
/// by `body` into the existing `pattern`. The pattern's existing
/// variables (if any) are preserved as the first elements of the
/// extended pattern; phi vars are appended afterward and the branches
/// are extended to yield `(existing_pattern_value, phi_vars...)`.
///
/// Always returns `Some` — the caller has already filtered to If /
/// Match / MatchOption values, and a no-op (no phis found, empty
/// existing pattern) is allowed.
fn try_lift_phis(pattern: Vec<TempId>, value: IRNode, body: IRNode) -> Option<IRNode> {
    let body_free = body.free_vars();
    let pattern_set: std::collections::BTreeSet<TempId> = pattern.iter().cloned().collect();
    let phi_candidates_from_defs = |defs: &std::collections::BTreeSet<TempId>| -> Vec<TempId> {
        let mut out: Vec<TempId> = body_free
            .iter()
            .filter(|v| defs.contains(*v) && !pattern_set.contains(*v))
            .cloned()
            .collect();
        out.sort();
        out
    };
    let extend_branch = |branch: IRNode, phis: &[TempId]| -> IRNode {
        if pattern.is_empty() {
            // Nothing to preserve — the branch yields just the phi tuple.
            append_phi_yield(branch, phis)
        } else {
            // Branch yields `(existing_value, phi1, phi2, ...)`.
            append_extended_yield(branch, &pattern, phis)
        }
    };
    match value {
        IRNode::If {
            cond,
            then_branch,
            else_branch,
        } => {
            let then_defs = effective_bindings(&then_branch);
            let else_defs = effective_bindings(&else_branch);
            let mut all_defs = then_defs.clone();
            all_defs.extend(else_defs.iter().cloned());
            let phis = phi_candidates_from_defs(&all_defs);
            if phis.is_empty() {
                return Some(IRNode::Let {
                    pattern,
                    value: Box::new(IRNode::If {
                        cond: Box::new(*cond),
                        then_branch: Box::new(*then_branch),
                        else_branch: Box::new(*else_branch),
                    }),
                    body: Box::new(body),
                });
            }
            let then_ext = extend_branch(*then_branch, &phis);
            let else_ext = extend_branch(*else_branch, &phis);
            let mut new_pattern = pattern;
            new_pattern.extend(phis);
            Some(IRNode::Let {
                pattern: new_pattern,
                value: Box::new(IRNode::If {
                    cond,
                    then_branch: Box::new(then_ext),
                    else_branch: Box::new(else_ext),
                }),
                body: Box::new(body),
            })
        }
        IRNode::Match { scrutinee, cases } => {
            let mut all_defs: std::collections::BTreeSet<TempId> =
                std::collections::BTreeSet::new();
            for (_, _, b) in &cases {
                for v in effective_bindings(b) {
                    all_defs.insert(v);
                }
            }
            let phis = phi_candidates_from_defs(&all_defs);
            if phis.is_empty() {
                return Some(IRNode::Let {
                    pattern,
                    value: Box::new(IRNode::Match { scrutinee, cases }),
                    body: Box::new(body),
                });
            }
            let lifted_cases: Vec<_> = cases
                .into_iter()
                .map(|(i, ps, b)| (i, ps, extend_branch(b, &phis)))
                .collect();
            let mut new_pattern = pattern;
            new_pattern.extend(phis);
            Some(IRNode::Let {
                pattern: new_pattern,
                value: Box::new(IRNode::Match {
                    scrutinee,
                    cases: lifted_cases,
                }),
                body: Box::new(body),
            })
        }
        IRNode::MatchOption {
            scrutinee,
            binding,
            some_branch,
            none_branch,
        } => {
            let some_defs = effective_bindings(&some_branch);
            let none_defs = effective_bindings(&none_branch);
            let mut all_defs = some_defs.clone();
            all_defs.extend(none_defs.iter().cloned());
            let phis = phi_candidates_from_defs(&all_defs);
            if phis.is_empty() {
                return Some(IRNode::Let {
                    pattern,
                    value: Box::new(IRNode::MatchOption {
                        scrutinee,
                        binding,
                        some_branch,
                        none_branch,
                    }),
                    body: Box::new(body),
                });
            }
            let some_ext = extend_branch(*some_branch, &phis);
            let none_ext = extend_branch(*none_branch, &phis);
            let mut new_pattern = pattern;
            new_pattern.extend(phis);
            Some(IRNode::Let {
                pattern: new_pattern,
                value: Box::new(IRNode::MatchOption {
                    scrutinee,
                    binding,
                    some_branch: Box::new(some_ext),
                    none_branch: Box::new(none_ext),
                }),
                body: Box::new(body),
            })
        }
        _ => Some(IRNode::Let {
            pattern,
            value: Box::new(value),
            body: Box::new(body),
        }),
    }
}

/// Like `append_phi_yield` but yields a tuple containing the branch's
/// original terminal value followed by the phi vars. Used when the
/// surrounding Let already had a non-empty pattern that captured the
/// branch's natural return value.
fn append_extended_yield(node: IRNode, existing_pattern: &[TempId], phi_vars: &[TempId]) -> IRNode {
    match node {
        IRNode::Let {
            pattern,
            value,
            body,
        } => IRNode::Let {
            pattern,
            value,
            body: Box::new(append_extended_yield(*body, existing_pattern, phi_vars)),
        },
        IRNode::If {
            cond,
            then_branch,
            else_branch,
        } => IRNode::If {
            cond,
            then_branch: Box::new(append_extended_yield(
                *then_branch,
                existing_pattern,
                phi_vars,
            )),
            else_branch: Box::new(append_extended_yield(
                *else_branch,
                existing_pattern,
                phi_vars,
            )),
        },
        IRNode::Match { scrutinee, cases } => IRNode::Match {
            scrutinee,
            cases: cases
                .into_iter()
                .map(|(i, ps, b)| (i, ps, append_extended_yield(b, existing_pattern, phi_vars)))
                .collect(),
        },
        IRNode::MatchOption {
            scrutinee,
            binding,
            some_branch,
            none_branch,
        } => IRNode::MatchOption {
            scrutinee,
            binding,
            some_branch: Box::new(append_extended_yield(
                *some_branch,
                existing_pattern,
                phi_vars,
            )),
            none_branch: Box::new(append_extended_yield(
                *none_branch,
                existing_pattern,
                phi_vars,
            )),
        },
        terminal => {
            // The pattern arity dictates whether we flatten the terminal
            // tuple or wrap it.
            //   * `pattern.len() == 1`: `let X := <value> ; ...`. The
            //     existing single var captures `<value>` whole. Wrap as
            //     `(<value>, phi1, phi2, ...)` so the extended pattern
            //     `[X, phi1, phi2, ...]` decomposes correctly.
            //   * `pattern.len() > 1`: `let (A, B, ...) := <tuple> ; ...`.
            //     The existing pattern destructures a flat tuple — append
            //     phi vars onto that tuple to keep the pattern's arity
            //     matched.
            //   * `pattern.is_empty()`: caller used `append_phi_yield`
            //     instead; we do not see this branch.
            if existing_pattern.len() <= 1 {
                let mut elems = vec![terminal];
                elems.extend(phi_vars.iter().map(|v| IRNode::Var(v.clone())));
                IRNode::Tuple(elems)
            } else {
                // Multi-arity: flatten if the terminal is already a tuple.
                match terminal {
                    IRNode::Tuple(mut elems) => {
                        elems.extend(phi_vars.iter().map(|v| IRNode::Var(v.clone())));
                        IRNode::Tuple(elems)
                    }
                    other => {
                        // Pattern says >1 but terminal is not a tuple.
                        // Conservatively wrap; pattern arity won't match
                        // a single-element tuple, so treat as
                        // single-arity wrap (caller will see a runtime
                        // arity error — matches original behaviour).
                        let mut elems = vec![other];
                        elems.extend(phi_vars.iter().map(|v| IRNode::Var(v.clone())));
                        IRNode::Tuple(elems)
                    }
                }
            }
        }
    }
}

/// Like `IRNode::bindings()`, but also picks up `WriteBack { parent }`
/// names. Mutable_threading rewrites `... ; <write-back to parent>`
/// using `Let { pattern: [], value: WriteBack { child, parent, .. }
/// }` shape — the renderer projects `parent` into the Lean `let`'s
/// binding name, so for the purposes of phi detection the variable
/// IS rebound by that node even though it does not appear in any
/// `Let` pattern.
fn effective_bindings(node: &IRNode) -> std::collections::BTreeSet<TempId> {
    let mut out = node.bindings();
    collect_writeback_parents(node, &mut out);
    out
}

fn collect_writeback_parents(node: &IRNode, out: &mut std::collections::BTreeSet<TempId>) {
    if let IRNode::WriteBack { parent, .. } = node {
        out.insert(parent.clone());
    }
    for child in node.iter_children() {
        collect_writeback_parents(child, out);
    }
}

/// Replace a branch's terminal expression with `(phi_vars...)` so the
/// branch yields the lifted variables. Recurses through Let chains and
/// nested If / Match so every leaf yields the phi tuple.
fn append_phi_yield(node: IRNode, phi_vars: &[TempId]) -> IRNode {
    match node {
        IRNode::Let {
            pattern,
            value,
            body,
        } => IRNode::Let {
            pattern,
            value,
            body: Box::new(append_phi_yield(*body, phi_vars)),
        },
        IRNode::If {
            cond,
            then_branch,
            else_branch,
        } => IRNode::If {
            cond,
            then_branch: Box::new(append_phi_yield(*then_branch, phi_vars)),
            else_branch: Box::new(append_phi_yield(*else_branch, phi_vars)),
        },
        IRNode::Match { scrutinee, cases } => IRNode::Match {
            scrutinee,
            cases: cases
                .into_iter()
                .map(|(i, ps, b)| (i, ps, append_phi_yield(b, phi_vars)))
                .collect(),
        },
        IRNode::MatchOption {
            scrutinee,
            binding,
            some_branch,
            none_branch,
        } => IRNode::MatchOption {
            scrutinee,
            binding,
            some_branch: Box::new(append_phi_yield(*some_branch, phi_vars)),
            none_branch: Box::new(append_phi_yield(*none_branch, phi_vars)),
        },
        terminal => {
            let phi_tuple = if phi_vars.len() == 1 {
                IRNode::Var(phi_vars[0].clone())
            } else {
                IRNode::Tuple(phi_vars.iter().map(|v| IRNode::Var(v.clone())).collect())
            };
            IRNode::Let {
                pattern: vec![],
                value: Box::new(terminal),
                body: Box::new(phi_tuple),
            }
        }
    }
}

/// Fix `Let { pattern: [], value: WriteRef { reference: Var(X), .. } }`
/// by binding the WriteRef result to X.
///
/// `Mutable.set` in the Lean prelude is pure — it returns a new
/// Mutable rather than mutating in place. The IR translator emits the
/// `WriteRef` op with an empty Let pattern, which the renderer turns
/// into `let _ := Mutable.set X v`, discarding the new Mutable. The
/// subsequent `Mutable.apply X` then uses the unchanged `X`, silently
/// losing the write.
///
/// The fix is to give the Let a real pattern that captures the
/// updated reference: `Let { pattern: [X], value: WriteRef { reference:
/// Var(X), .. } }`. The renderer emits `let X := Mutable.set X v`,
/// shadow-rebinding `X` to the new Mutable so subsequent uses see the
/// write.
pub fn fix_writeref_empty_patterns(node: IRNode) -> IRNode {
    node.map(&mut |n| match n {
        IRNode::Let {
            pattern,
            value,
            body,
        } if pattern.is_empty() => {
            let ref_var = if let IRNode::WriteRef { reference, .. } = value.as_ref() {
                if let IRNode::Var(v) = reference.as_ref() {
                    Some(v.clone())
                } else {
                    None
                }
            } else {
                None
            };
            if let Some(v) = ref_var {
                IRNode::Let {
                    pattern: vec![v],
                    value,
                    body,
                }
            } else {
                IRNode::Let {
                    pattern,
                    value,
                    body,
                }
            }
        }
        other => other,
    })
}

// ============================================================================
// Propagate field-snapshot WriteBacks
// ============================================================================
//
// Some Move-source mutation patterns translate to a WriteBack whose
// `parent` is a temp that was earlier bound as a field snapshot of
// some surrounding struct, e.g.
//
//     let $t5 := self.contents                        -- field snapshot
//     ... operations producing __mut_ret ...
//     WriteBack { child: __mut_ret, parent: $t5 }     -- rebinds $t5
//     ... uses self ...                                -- sees OLD self!
//
// `mutable_threading` does not propagate this kind of WriteBack back
// up to the field's owning struct because the IR translator produces
// `WriteBackEdge::Direct` for ordinary field borrows (the
// `WriteBackEdge::Field` form is reserved for object dynamic fields).
//
// The renderer turns the `Let { pattern: [], value: WriteBack { .. } }`
// shape into `let $t5 := __mut_ret`, which rebinds the temp but never
// touches `self`. The function then returns the unchanged `self`.
//
// Fix: after the WriteBack, emit a real field update on the snapshot's
// origin var:
//
//     let $t5 := self.contents                       -- snapshot
//     ... operations ...
//     WriteBack { child: __mut_ret, parent: $t5 }    -- keep
//     let self := { self with contents := __mut_ret }-- new: propagate
//     ... uses self ...                              -- now sees NEW
//
// We leave the original WriteBack in place so any downstream use of
// the snapshot temp (`$t5`) still gets the updated value via the
// renderer's `let $t5 := __mut_ret` projection.

pub fn propagate_field_snapshot_writebacks(node: IRNode) -> IRNode {
    propagate_walk(
        node,
        &BTreeMap::<TempId, (TempId, StructID, usize, bool)>::new(),
    )
}

fn propagate_walk(
    node: IRNode,
    snapshots: &BTreeMap<TempId, (TempId, StructID, usize, bool)>,
) -> IRNode {
    match node {
        IRNode::Let { .. } => {
            let (bindings, tail) = unroll_let_chain(node);
            propagate_chain(bindings, tail, snapshots)
        }
        IRNode::If {
            cond,
            then_branch,
            else_branch,
        } => IRNode::If {
            cond: Box::new(propagate_walk(*cond, snapshots)),
            then_branch: Box::new(propagate_walk(*then_branch, snapshots)),
            else_branch: Box::new(propagate_walk(*else_branch, snapshots)),
        },
        IRNode::Match { scrutinee, cases } => IRNode::Match {
            scrutinee: Box::new(propagate_walk(*scrutinee, snapshots)),
            cases: cases
                .into_iter()
                .map(|(idx, params, body)| (idx, params, propagate_walk(body, snapshots)))
                .collect(),
        },
        IRNode::MatchOption {
            scrutinee,
            binding,
            some_branch,
            none_branch,
        } => IRNode::MatchOption {
            scrutinee: Box::new(propagate_walk(*scrutinee, snapshots)),
            binding,
            some_branch: Box::new(propagate_walk(*some_branch, snapshots)),
            none_branch: Box::new(propagate_walk(*none_branch, snapshots)),
        },
        other => {
            let snaps = snapshots.clone();
            other.map(&mut |n| match n {
                IRNode::Let { .. }
                | IRNode::If { .. }
                | IRNode::Match { .. }
                | IRNode::MatchOption { .. } => propagate_walk(n, &snaps),
                x => x,
            })
        }
    }
}

fn propagate_chain(
    bindings: Vec<(Vec<TempId>, IRNode)>,
    tail: IRNode,
    inherited: &BTreeMap<TempId, (TempId, StructID, usize, bool)>,
) -> IRNode {
    let mut snaps: BTreeMap<TempId, (TempId, StructID, usize, bool)> = inherited.clone();
    let mut out: Vec<(Vec<TempId>, IRNode)> = Vec::with_capacity(bindings.len());

    let mut iter = bindings.into_iter().peekable();
    while let Some((pattern, value)) = iter.next() {
        let value = propagate_walk(value, &snaps);
        let mut emitted_extra = false;

        // Is this an empty-pattern Let with a Direct WriteBack to a
        // tracked snapshot temp?
        if pattern.is_empty() {
            if let IRNode::WriteBack {
                child: _,
                parent,
                edge: WriteBackEdge::Direct,
            } = &value
            {
                if let Some((origin, struct_id, field_index, is_mutable)) =
                    snaps.get(parent).cloned()
                {
                    // Keep the original WriteBack (rebinds parent) and
                    // append a real field update on origin so the
                    // mutation propagates upstream. We reference
                    // `parent` rather than `child`: the WriteBack
                    // renderer has already unwrapped any Mutable child
                    // via `Mutable.apply` into `parent`, so `parent`
                    // always carries the post-WriteBack plain value
                    // matching the field's declared type.
                    out.push((pattern.clone(), value.clone()));
                    // Idempotency: skip the propagation if the same
                    // field update is already present in the chain —
                    // either just before this WriteBack (some upstream
                    // passes interleave the update before the
                    // WriteBack) or just after (the IR translator and
                    // mutable_threading sometimes emit the update
                    // immediately after the WriteBack, which would
                    // duplicate with our emission and rebind `origin`
                    // to a plain struct value, breaking type-check on
                    // any later `Mutable.set origin ...`).
                    //
                    // Accept both plain `UpdateField { base: Var(origin) }`
                    // and WriteRef-wrapped `WriteRef { ref: Var(origin),
                    // value: UpdateField { base: ReadRef(Var(origin)) } }`
                    // shapes (mutable_threading already emits the latter
                    // for &mut field returns; we should not duplicate).
                    let matches_propagation = |p: &[TempId], v: &IRNode| -> bool {
                        p.len() == 1
                            && p[0] == origin
                            && extract_self_update(v)
                                .map(|(b, s, f, vv, _kind)| {
                                    b == &origin
                                        && s == struct_id
                                        && f == field_index
                                        && matches!(vv, IRNode::Var(bv) if bv == parent)
                                })
                                .unwrap_or(false)
                    };
                    let already_present_back = out
                        .iter()
                        .rev()
                        .take(3)
                        .any(|(p, v)| matches_propagation(p, v));
                    let already_present_forward = iter
                        .peek()
                        .map(|(p, v)| matches_propagation(p, v))
                        .unwrap_or(false);
                    if !already_present_back && !already_present_forward {
                        let inner_update = IRNode::UpdateField {
                            base: Box::new(if is_mutable {
                                IRNode::ReadRef(Box::new(IRNode::Var(origin.clone())))
                            } else {
                                IRNode::Var(origin.clone())
                            }),
                            struct_id,
                            field_index,
                            value: Box::new(IRNode::Var(parent.clone())),
                        };
                        let propagation = if is_mutable {
                            IRNode::WriteRef {
                                reference: Box::new(IRNode::Var(origin.clone())),
                                value: Box::new(inner_update),
                            }
                        } else {
                            inner_update
                        };
                        out.push((vec![origin.clone()], propagation));
                    }
                    // The snapshot remains valid (origin.field == child
                    // == new contents == new origin.field), so leave
                    // `snaps[parent]` in place. We DO need to drop any
                    // snapshot whose origin is also `origin` (their
                    // cached field values may be stale relative to the
                    // new origin).
                    let stale: Vec<TempId> = snaps
                        .iter()
                        .filter_map(|(k, (o, _, _, _))| {
                            if o == &origin && k != parent {
                                Some(k.clone())
                            } else {
                                None
                            }
                        })
                        .collect();
                    for k in stale {
                        snaps.remove(&k);
                    }
                    emitted_extra = true;
                }
            }
        }

        if !emitted_extra {
            // Invalidate FIRST: drop snapshots keyed on or origined-from
            // any rebound var. (Then track the fresh binding below.)
            for v in &pattern {
                snaps.remove(v);
                let stale: Vec<TempId> = snaps
                    .iter()
                    .filter_map(|(k, (o, _, _, _))| if o == v { Some(k.clone()) } else { None })
                    .collect();
                for k in stale {
                    snaps.remove(&k);
                }
            }
            // Then track new snapshots: `let X := <var>.<field>` or
            // `let X := (Mutable.val <var>).<field>`. The Mutable form
            // means the origin is itself a `Mutable<_, OwnerStruct>`,
            // and propagation onto it must be `WriteRef`-wrapped to
            // keep the Mutable wrapper rather than collapsing it to a
            // plain struct value (which would type-mismatch a later
            // `Mutable.set X` / `Mutable.apply X`).
            if pattern.len() == 1 {
                if let IRNode::Field {
                    base,
                    struct_id,
                    field_index,
                } = &value
                {
                    let origin_info = match base.as_ref() {
                        IRNode::Var(b) => Some((b.clone(), false)),
                        IRNode::ReadRef(inner) => {
                            if let IRNode::Var(b) = inner.as_ref() {
                                Some((b.clone(), true))
                            } else {
                                None
                            }
                        }
                        _ => None,
                    };
                    if let Some((base_var, is_mut)) = origin_info {
                        snaps.insert(
                            pattern[0].clone(),
                            (base_var, *struct_id, *field_index, is_mut),
                        );
                    }
                }
            }
            out.push((pattern, value));
        }
    }

    let tail = propagate_walk(tail, &snaps);
    rebuild_let_chain(out, tail)
}

// ============================================================================
// Wrap if-branch UpdateField terminals in WriteRef when bound to a Mutable
// ============================================================================
//
// `Let([X], If { then, else }, body)` where X has Mutable type and a branch
// terminal is `UpdateField { base: Var(X) | base: ReadRef(Var(X)), .. }`
// (a "bare" struct-update on the Mutable's value) renders as
// `let X := if cond then { Mutable.val X with f := v } else ...`. The bare
// UpdateField has the bare struct type (`Account`), but X is `Mutable<Account>`
// — Lean rejects the assignment with `'<field>' is not a field of structure
// 'Mutable'` errors on every later `X.<field>` access.
//
// Test-mode `.aborts` companions are the prevalent source: the abort
// derivation strips the WriteRef around the trailing Mutable.set in each
// branch, leaving the inner UpdateField as the branch terminal. The impl
// version preserves the WriteRef and is unaffected. The fix below normalises
// branches by wrapping bare UpdateField terminals in `WriteRef { reference:
// Var(X), value: <terminal> }`, which renders as `Mutable.set X (...)` and
// returns Mutable<Account> consistently with bare-Var(X) terminals on the
// other side.
//
// Branches are walked recursively through Let chains and nested If/Match so
// every leaf that needs wrapping gets it. Terminals that are bare `Var(X)`
// or unrelated expressions are left alone.

pub fn wrap_mutable_if_branch_terminals(node: IRNode, reg: &mut VariableRegistry) -> IRNode {
    wrap_walk(node, reg)
}

fn wrap_walk(node: IRNode, reg: &mut VariableRegistry) -> IRNode {
    match node {
        IRNode::Let {
            pattern,
            value,
            body,
        } => {
            // Recurse into the value first (with current registry).
            let value = wrap_walk(*value, reg);

            // Detect `Let([X], If { ... }, body)` where X is Mutable and
            // wrap branch terminals.
            let new_value = if pattern.len() == 1 {
                let x = &pattern[0];
                let x_is_mutable =
                    reg.contains(x) && matches!(reg.get_type(x), Type::MutableReference(_, _));
                let value_is_branching = matches!(
                    &value,
                    IRNode::If { .. } | IRNode::Match { .. } | IRNode::MatchOption { .. }
                );
                if x_is_mutable && value_is_branching {
                    wrap_branch_terminals(value, x)
                } else {
                    value
                }
            } else {
                value
            };

            // Register the pattern with the value's type for downstream walk.
            // Be defensive: if any free var of new_value is missing from reg
            // (can happen when this pass runs late and the IR has stray refs
            // from upstream simplification), skip the registration rather
            // than panic. Downstream wrap detection on later Lets only needs
            // X-is-Mutable evidence from PRIOR bindings, so a missing
            // registration just means we miss a wrap opportunity at one
            // site.
            let all_free_in_scope = new_value.free_vars().iter().all(|v| reg.contains(v));
            if all_free_in_scope {
                let val_type = new_value.get_type(reg);
                reg.register_pattern(&pattern, val_type);
            }

            let body = wrap_walk(*body, reg);
            IRNode::Let {
                pattern,
                value: Box::new(new_value),
                body: Box::new(body),
            }
        }
        // Branches share the SAME registry (no per-branch clone). Registry
        // entries are SSA temps — globally unique within a function — so a
        // binding introduced inside one branch can never collide with, or be
        // misread by, a sibling branch or post-branch code: a stale entry is
        // never looked up for a different variable. Threading `&mut reg`
        // instead of `reg.clone()` at every branch turns this pass from
        // O(branches · scope_size) — quadratic on the deep Let-spines of
        // large functions — into linear, the fix for multi-minute finalize
        // times on big packages (e.g. ika-staking). The mutable-check only
        // reads a binding's OWN type via its unique name, so the wider
        // in-scope view leaking across siblings is benign.
        IRNode::If {
            cond,
            then_branch,
            else_branch,
        } => IRNode::If {
            cond: Box::new(wrap_walk(*cond, reg)),
            then_branch: Box::new(wrap_walk(*then_branch, reg)),
            else_branch: Box::new(wrap_walk(*else_branch, reg)),
        },
        IRNode::Match { scrutinee, cases } => IRNode::Match {
            scrutinee: Box::new(wrap_walk(*scrutinee, reg)),
            cases: cases
                .into_iter()
                .map(|(idx, params, body)| (idx, params, wrap_walk(body, reg)))
                .collect(),
        },
        IRNode::MatchOption {
            scrutinee,
            binding,
            some_branch,
            none_branch,
        } => IRNode::MatchOption {
            scrutinee: Box::new(wrap_walk(*scrutinee, reg)),
            binding,
            some_branch: Box::new(wrap_walk(*some_branch, reg)),
            none_branch: Box::new(wrap_walk(*none_branch, reg)),
        },
        // Non-control-flow node (Call, BinOp, Pack, ...). Recurse into its
        // DIRECT children exactly once each. The previous `other.map(..)` used
        // the RECURSIVE bottom-up map, which visits every descendant AND then
        // lets the closure call `wrap_walk` on control-flow descendants —
        // re-walking those subtrees. On deeply right-nested IR (e.g. the
        // ~14-deep `||`/`&&` If-chain of `is_primitive.aborts`) that double
        // traversal is O(n^2) / exponential and took >150s on one function.
        // `map_direct_children` recurses each child once via `wrap_walk`,
        // which itself handles the deeper structure — restoring linear cost.
        other => other.map_direct_children(|n| wrap_walk(n, reg)),
    }
}

/// Walk every branch terminal of an If/Match/MatchOption and wrap bare
/// `UpdateField { base: Var(X) | base: ReadRef(Var(X)), .. }` terminals in
/// `WriteRef { reference: Var(X), value: <terminal> }`. Terminals that are
/// bare `Var(X)` or unrelated are left alone. Nested control flow recurses.
fn wrap_branch_terminals(node: IRNode, x: &TempId) -> IRNode {
    match node {
        IRNode::If {
            cond,
            then_branch,
            else_branch,
        } => IRNode::If {
            cond,
            then_branch: Box::new(wrap_branch_terminals(*then_branch, x)),
            else_branch: Box::new(wrap_branch_terminals(*else_branch, x)),
        },
        IRNode::Match { scrutinee, cases } => IRNode::Match {
            scrutinee,
            cases: cases
                .into_iter()
                .map(|(idx, params, body)| (idx, params, wrap_branch_terminals(body, x)))
                .collect(),
        },
        IRNode::MatchOption {
            scrutinee,
            binding,
            some_branch,
            none_branch,
        } => IRNode::MatchOption {
            scrutinee,
            binding,
            some_branch: Box::new(wrap_branch_terminals(*some_branch, x)),
            none_branch: Box::new(wrap_branch_terminals(*none_branch, x)),
        },
        IRNode::Let {
            pattern,
            value,
            body,
        } => IRNode::Let {
            pattern,
            value,
            body: Box::new(wrap_branch_terminals(*body, x)),
        },
        terminal => {
            if let IRNode::UpdateField { base, .. } = &terminal {
                let base_var = match base.as_ref() {
                    IRNode::Var(b) => Some(b),
                    IRNode::ReadRef(inner) => {
                        if let IRNode::Var(b) = inner.as_ref() {
                            Some(b)
                        } else {
                            None
                        }
                    }
                    _ => None,
                };
                if base_var == Some(x) {
                    return IRNode::WriteRef {
                        reference: Box::new(IRNode::Var(x.clone())),
                        value: Box::new(terminal),
                    };
                }
            }
            terminal
        }
    }
}
