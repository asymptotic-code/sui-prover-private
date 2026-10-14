// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Analysis and optimization passes for TheoremIR

mod callee_requires_entry;
mod callee_requires_precond;
mod cleanup;
mod constant_folding;
mod dead_code_removal;
pub(crate) mod dead_param_elimination;
pub mod decompose_aborts;
mod deep_nesting;
mod dependency_order;
pub mod dynamic_field_rewriting;
mod early_return;
pub mod equation_lemmas;
pub mod frame_lemmas;
pub mod ghost_threading;
mod import_collection;
mod inject_arithmetic_aborts;
mod lean_termination;
mod logical_simplification;
mod loop_body_extraction;
mod loop_inv_entry;
pub mod mutable_threading;
mod native_shadowing;
mod nested_loop_termination;
mod post_state_rename;
mod prop_inference;
mod spec_extraction;
mod spec_type_conversion;
mod stored_value_invariants;
mod temp_inlining;
pub mod tx_context_natives;
mod validation;
pub mod world_threading;

pub use callee_requires_entry::thread_callee_requires_entry;
pub use callee_requires_precond::thread_callee_requires_precond;
pub use cleanup::{
    coalesce_shadow_self_noop_updates, fix_discarded_reconstruct_writebacks,
    fix_writeref_empty_patterns, flatten_sequential_ifs, lift_bool_tails_to_prop,
    lift_post_threading_phis, normalize_unit_branches, propagate_field_snapshot_writebacks,
    wrap_mutable_if_branch_terminals,
};
pub use constant_folding::fold_constants;
pub use dead_code_removal::remove_dead_code;
pub use decompose_aborts::decompose_aborts;
pub use decompose_aborts::decompose_ensures;
pub use deep_nesting::flatten_deep_nesting;
pub use dependency_order::order_by_dependencies;
pub use early_return::{
    fix_undefined_vars_in_aborts, fold_early_returns, fold_early_returns_inner,
    inline_abort_only_after_calls, replace_inhabited_let_values, replace_inhabited_with_false,
    rewrite_asserts_in_aborts, simplify_aborts, strip_abort_branches,
    strip_unreachable_after_tail_calls,
};
pub use equation_lemmas::compute_equation_lemmas;
pub use frame_lemmas::compute_frame_lemmas;
pub use import_collection::collect_imports;
pub use inject_arithmetic_aborts::inject_arithmetic_aborts;
pub use lean_termination::thread_lean_terminations;
pub use logical_simplification::simplify as logical_simplify;
pub use loop_body_extraction::extract_loop_bodies;
pub use loop_inv_entry::thread_loop_inv_entry;
pub use native_shadowing::{mark_native_shadowed, mark_native_shadowed_auto};
pub use nested_loop_termination::thread_nested_loop_termination;
pub use post_state_rename::distinguish_param_rebinds_in_ensures;
pub use prop_inference::{infer_prop_returns, strip_quantifiers_in_aborts, validate_sorts};
pub use spec_extraction::extract_all_specs;
pub use spec_type_conversion::generate_spec_type_conversions;
pub use stored_value_invariants::thread_stored_value_invariants;
pub use temp_inlining::{inline_temps, inline_temps_simple, propagate_copies};
pub use validation::{validate_function, validate_program, ValidationError};

use crate::data::variables::VariableRegistry;
use crate::IRNode;
use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};

const MAX_FIXPOINT_ITERATIONS: usize = 100;

/// Compute a hash of an IR node for change detection by traversing the tree structure.
/// This is much faster than format!() which allocates a string.
fn compute_ir_hash(node: &IRNode) -> u64 {
    let mut hasher = DefaultHasher::new();
    hash_ir_node(node, &mut hasher);
    hasher.finish()
}

/// Recursively hash an IR node structure
fn hash_ir_node(node: &IRNode, hasher: &mut DefaultHasher) {
    // Hash the discriminant to differentiate node types
    std::mem::discriminant(node).hash(hasher);

    // Hash the specific fields and recurse into children
    match node {
        IRNode::Var(name) => name.hash(hasher),
        IRNode::Const(c) => format!("{:?}", c).hash(hasher), // Const is small, format is ok
        IRNode::Let {
            pattern,
            value,
            body,
        } => {
            pattern.hash(hasher);
            hash_ir_node(value, hasher);
            hash_ir_node(body, hasher);
        }
        IRNode::If {
            cond,
            then_branch,
            else_branch,
        } => {
            hash_ir_node(cond, hasher);
            hash_ir_node(then_branch, hasher);
            hash_ir_node(else_branch, hasher);
        }
        IRNode::Call {
            function,
            args,
            type_args,
        } => {
            function.hash(hasher);
            type_args.len().hash(hasher);
            for arg in args {
                hash_ir_node(arg, hasher);
            }
        }
        IRNode::Tuple(elems) => {
            elems.len().hash(hasher);
            for elem in elems {
                hash_ir_node(elem, hasher);
            }
        }
        IRNode::BinOp { op, lhs, rhs } => {
            std::mem::discriminant(op).hash(hasher);
            hash_ir_node(lhs, hasher);
            hash_ir_node(rhs, hasher);
        }
        IRNode::UnOp { op, operand } => {
            std::mem::discriminant(op).hash(hasher);
            hash_ir_node(operand, hasher);
        }
        // Add more cases as needed - for now just use discriminant for complex types
        _ => {
            // For other node types, we rely on the discriminant hash above
            // This is a simplification but should be sufficient for change detection
        }
    }
}

pub fn optimize(node: IRNode, reg: &mut VariableRegistry) -> IRNode {
    optimize_with(node, reg, false, None)
}

/// `optimize` variant that, when `aborts` is set, inlines heavy multi-use temps
/// (see `temp_inlining::inline_temps_aborts`). Used for `.aborts` bodies so the
/// kernel-cheap `conv`-localized proof technique applies. See CLAUDE.md
/// "Kernel deep-recursion on heavy `BoundedNat` obligations".
pub fn optimize_with(
    mut node: IRNode,
    reg: &mut VariableRegistry,
    aborts: bool,
    self_fn: Option<usize>,
) -> IRNode {
    for i in 0..MAX_FIXPOINT_ITERATIONS {
        let prev_hash = compute_ir_hash(&node);
        node = optimize_single_pass(node, reg, aborts, self_fn);
        let new_hash = compute_ir_hash(&node);

        if new_hash == prev_hash {
            break;
        }
        if i >= 50 {
            eprintln!(
                "WARNING: optimize fixpoint did not converge after {} iterations",
                i
            );
            break;
        }
    }
    cleanup::flatten_sequential_ifs(node, reg)
}

fn optimize_single_pass(
    node: IRNode,
    reg: &mut VariableRegistry,
    aborts: bool,
    self_fn: Option<usize>,
) -> IRNode {
    let node = if aborts {
        temp_inlining::inline_temps_aborts(node)
    } else {
        temp_inlining::inline_temps(node, reg)
    };
    let node = dead_code_removal::remove_dead_code(node);
    let node = logical_simplification::simplify(node);
    let node = cleanup::cleanup(node, reg, self_fn);
    early_return::fold_early_returns(node)
}
