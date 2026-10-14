// Copyright (c) Asymptotic
// SPDX-License-Identifier: Apache-2.0

//! Control flow reconstruction module

pub mod bytecode_cfg;
pub mod early_return;
pub mod ir_translation;
mod loop_handling;
pub mod phi_detection;
pub mod skeleton_recovery;

use intermediate_theorem_format::data::functions::FunctionSignature;
use intermediate_theorem_format::data::types::TempId;
use intermediate_theorem_format::IRNode;
use intermediate_theorem_format::{FunctionID, ModuleID, Program, Type};
use std::collections::{BTreeMap, BTreeSet};

/// Whether we are emitting the body (return value) or aborts (Bool) side.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EmitMode {
    Body,
    Aborts,
}

/// Info about the enclosing while loop, used by Continue/Break to emit real Calls.
/// Each loop produces two functions in the current mode:
/// - while_func (loop iteration) — params = scope at loop entry
/// - after_func (continuation after loop exit) — params = scope at loop entry + loop body bindings
pub struct WhileLoopInfo {
    pub while_func_id: FunctionID,
    pub after_func_id: FunctionID,
    /// Parameters for while_func (Continue calls pass these)
    pub while_params: Vec<TempId>,
    /// Parameters for after_func (Break calls pass these)
    pub after_params: Vec<TempId>,
    pub type_args: Vec<Type>,
    /// Name of the loop-invariant hypothesis parameter injected onto this
    /// loop's `while_func` (Some only for loops with a `#[spec_only(loop_inv)]`
    /// target). Continue calls must thread it as the final argument so the
    /// recursive call stays well-typed. `None` for ordinary loops.
    pub hyp_param: Option<TempId>,
}

/// Context threaded through emit for creating helper functions (while loops).
pub struct EmitContext<'a> {
    pub program: &'a mut Program,
    pub module_id: ModuleID,
    pub func_name: String,
    pub type_params: Vec<String>,
    pub variables: BTreeMap<TempId, Type>,
    pub return_type: Type,
    pub mode: EmitMode,
    /// In `EmitMode::Body`, branches that always abort are normally
    /// pruned (the abort logic is captured by the `.aborts` companion
    /// the Aborts pass emits). When `preserve_aborts` is true we keep
    /// those branches in the body — needed by the Test face so the
    /// monadic renderer can evaluate `IRNode::Abort` at runtime.
    /// Always false in `EmitMode::Aborts` (no-op there).
    pub preserve_aborts: bool,
    while_counter: usize,
    /// Stack of enclosing while loops. Continue/Break use the top entry.
    while_stack: Vec<WhileLoopInfo>,
    /// All variables currently in scope (function params + let-bindings from preceding code).
    /// Used by emit_while to determine parameters for extracted loop functions.
    ///
    /// Scope is passed by value down recursive `emit` calls: a branch emits with
    /// a cloned copy, and its additions never affect the parent. There is no
    /// save/restore protocol — the Rust ownership rules of cloning and dropping
    /// replace it.
    scope: BTreeSet<TempId>,
}

impl<'a> EmitContext<'a> {
    pub fn new(
        program: &'a mut Program,
        module_id: ModuleID,
        func_name: String,
        signature: &FunctionSignature,
        variables: BTreeMap<TempId, Type>,
        mode: EmitMode,
    ) -> Self {
        Self::new_with_options(
            program, module_id, func_name, signature, variables, mode, false,
        )
    }

    pub fn new_with_options(
        program: &'a mut Program,
        module_id: ModuleID,
        func_name: String,
        signature: &FunctionSignature,
        variables: BTreeMap<TempId, Type>,
        mode: EmitMode,
        preserve_aborts: bool,
    ) -> Self {
        let scope: BTreeSet<TempId> = signature
            .parameters
            .iter()
            .filter(|p| p.ssa_value.as_ref() != "_")
            .map(|p| p.ssa_value.clone())
            .collect();
        Self {
            program,
            module_id,
            func_name,
            type_params: signature.type_params.clone(),
            return_type: signature.return_type.clone(),
            variables,
            mode,
            preserve_aborts,
            while_counter: 0,
            while_stack: Vec::new(),
            scope,
        }
    }

    /// Extend scope with ALL let-bindings from an IRNode, including those
    /// inside If/Match branches. Branch-local bindings don't leak because
    /// branches emit with a clone of the scope (see `emit_if`/`emit_switch`).
    pub fn extend_scope(&mut self, node: &IRNode) {
        self.scope.extend(node.bindings());
    }

    /// Add a single variable to scope (e.g., a phi variable discovered after branch emission).
    pub fn extend_scope_var(&mut self, var: TempId) {
        self.scope.insert(var);
    }

    /// Get the current scope.
    pub fn scope(&self) -> &BTreeSet<TempId> {
        &self.scope
    }

    /// Snapshot the current scope for later restoration.
    pub fn save_scope(&self) -> BTreeSet<TempId> {
        self.scope.clone()
    }

    /// Restore a previously saved scope. Note: `observed` is NOT restored — it's
    /// a monotonic record of every binding seen during emission.
    pub fn restore_scope(&mut self, saved: BTreeSet<TempId>) {
        self.scope = saved;
    }

    pub fn next_while_name(&mut self) -> String {
        let name = format!("{}.while_{}", self.func_name, self.while_counter);
        self.while_counter += 1;
        name
    }

    pub fn push_while(&mut self, info: WhileLoopInfo) {
        self.while_stack.push(info);
    }

    pub fn pop_while(&mut self) {
        self.while_stack
            .pop()
            .expect("pop_while called with empty while_stack");
    }

    pub fn current_while(&self) -> Option<&WhileLoopInfo> {
        self.while_stack.last()
    }

    /// Look up an enclosing loop by level (0 = innermost). Returns None if
    /// `level` exceeds the current nesting depth.
    pub fn enclosing_while(&self, level: usize) -> Option<&WhileLoopInfo> {
        let len = self.while_stack.len();
        if level >= len {
            return None;
        }
        self.while_stack.get(len - 1 - level)
    }
}

/// The aborts value for a path that does not abort.
pub fn no_abort() -> IRNode {
    IRNode::Const(intermediate_theorem_format::Const::Bool(false))
}

/// The aborts value for a path that always aborts.
pub fn does_abort() -> IRNode {
    IRNode::Const(intermediate_theorem_format::Const::Bool(true))
}
