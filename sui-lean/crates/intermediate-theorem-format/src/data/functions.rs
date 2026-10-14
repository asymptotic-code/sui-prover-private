// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Function IR data structures

use crate::data::types::{TempId, Type};
use crate::data::variables::VariableRegistry;
use crate::data::Dependable;
use crate::{IRNode, ModuleID, Program};
use move_model::model::{FunId, QualifiedId};

/// Unique identifier for a function in the program — just an index.
pub type FunctionID = usize;

/// Expectation attached to a `#[test]` function. Determines the correctness
/// obligation emitted in the `Correctness/` module.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TestExpectation {
    /// Plain `#[test]` — the function must run to completion without aborting.
    MustSucceed,
    /// `#[test] #[expected_failure]` — the function must abort. `abort_code=N`
    /// is treated the same as bare `expected_failure` for now: we assert the
    /// function aborts but do not validate the code.
    MustAbort,
}

/// Function parameter
#[derive(Debug, Clone)]
pub struct Parameter {
    pub name: String,
    pub param_type: Type,
    pub ssa_value: TempId,
}

/// How a proof parameter's Lean type is produced.
#[derive(Debug, Clone)]
pub enum ProofParamType {
    /// A verbatim Lean type term, rendered as-is (e.g. the precondition
    /// hypothesis `pool_token_exchange_rate_at_epoch_spec.requires pool epoch`).
    Verbatim(String),
    /// A loop-invariant hook predicate applied, at render time, to the carrying
    /// function's type params and value params (e.g. hook
    /// `Foo.while_0.loop_hyp` → `Foo.while_0.loop_hyp T a b`). Deferred to render
    /// so the application reflects the *final* parameter list (after
    /// dead-param elimination), with the renderer's identifier escaping.
    LoopInvHook(String),
    /// A stored-value data-invariant hypothesis: `TypedMap.all <K> <V> <pred>
    /// <map_expr>`, where `map_expr` is a field path over the carrying
    /// function's value params (built by `stored_value_invariants`) and the key
    /// / value types are rendered by the renderer (which owns type-to-Lean
    /// formatting). See `analysis/stored_value_invariants.rs`.
    DataInv {
        key_type: Type,
        value_type: Type,
        pred: String,
        map_expr: String,
    },
    /// The world-mode face of the stored-value invariant (unified-backend
    /// design §7, Phase 5): renders `Prover.World.World.allDf __world
    /// (World.uidNat <parent_expr>) <pred>`, where `parent_expr` is a UID
    /// field path over the carrying function's value params. The stored value
    /// type is implicit — `allDf` infers it from the predicate's domain — so
    /// no K/V types are carried. Produced only for `world_mode` packages.
    DataInvWorld { parent_expr: String, pred: String },
}

/// A proof-typed parameter appended after a function's value parameters. These
/// carry a Lean term as their type that the `Type` enum cannot represent (an
/// applied predicate), so they live alongside `parameters` rather than within
/// it. Making them first-class signature members — instead of render-time
/// side-tables — is what lets the validator, arity checks, and the renderer all
/// read one source of truth (see `Program::materialize_proof_params`).
#[derive(Debug, Clone)]
pub struct ProofParam {
    /// Parameter name; also the variable name referenced in the body
    /// (e.g. `hinv`, `hpre`).
    pub name: String,
    /// How to produce the parameter's Lean type.
    pub param_type: ProofParamType,
}

/// Function signature
#[derive(Debug, Clone)]
pub struct FunctionSignature {
    pub type_params: Vec<String>,
    pub parameters: Vec<Parameter>,
    /// Proof-typed parameters rendered after `parameters`. Populated by
    /// `Program::materialize_proof_params` as the final finalize step; empty
    /// before then. Single source of truth for hypothesis binders — every
    /// consumer (validator scope/arity, renderer, goal statements) reads here.
    pub proof_params: Vec<ProofParam>,
    pub return_type: Type,
}

impl FunctionSignature {
    /// Total binder arity: value parameters plus injected proof parameters.
    /// This is the count call sites must match — use it instead of
    /// `parameters.len()` anywhere arity is checked.
    pub fn arity(&self) -> usize {
        self.parameters.len() + self.proof_params.len()
    }
}

/// A function in the program. All functions are equal — defs, aborts, requires,
/// ensures, theorems — they're all just a Function. The renderer decides how to
/// emit each one based on whether `theorem` is set.
#[derive(Debug, Clone)]
pub struct Function {
    /// Module this function belongs to
    pub module_id: ModuleID,

    /// Function name (e.g., "empty", "empty.aborts", "empty.ensures")
    pub name: String,

    /// Function signature
    pub signature: FunctionSignature,

    /// Function body — the expression whose value is the function's return value.
    pub body: IRNode,

    /// If set, this function is rendered as a theorem with this proof body
    /// instead of as a def.
    pub theorem: Option<IRNode>,

    /// Whether this is a native function (no body)
    pub is_native: bool,

    /// Mutual recursion group ID (None if not mutually recursive)
    pub mutual_group_id: Option<usize>,

    /// If this function is a Move `#[test]`, the expectation it encodes.
    pub test_expectation: Option<TestExpectation>,

    /// Move `#[ext(pure, uninterpreted)]`: render as a Lean `opaque` constant
    /// (binders + return type, no body) so proofs get congruence-only
    /// reasoning. The placeholder Move body is never emitted or inlined.
    pub is_uninterpreted: bool,
}

impl Function {
    /// Build a VariableRegistry containing only this function's parameter types.
    /// Use as the base scope, then call `registry.add_node(node)` as you traverse
    /// the IR to populate types from Let bindings.
    pub fn param_registry<'a>(&self, program: &'a Program) -> VariableRegistry<'a> {
        VariableRegistry::new(
            self.signature
                .parameters
                .iter()
                .map(|p| (p.ssa_value.clone(), p.param_type.clone()))
                .collect(),
            program,
        )
    }

    /// Check if this function is a simple struct field accessor.
    pub fn is_field_accessor(&self) -> Option<(crate::StructID, usize)> {
        use crate::IRNode;

        if self.signature.parameters.len() != 1 {
            return None;
        }

        match &self.body {
            IRNode::Field {
                struct_id,
                field_index,
                base,
            } => {
                if let IRNode::Var(name) = base.as_ref() {
                    if *name == self.signature.parameters[0].ssa_value {
                        return Some((*struct_id, *field_index));
                    }
                }
                None
            }
            _ => None,
        }
    }
}

impl Dependable for Function {
    type Id = usize;
    type MoveKey = QualifiedId<FunId>;

    fn dependencies(&self) -> impl Iterator<Item = Self::Id> {
        self.body.calls()
    }

    fn with_recursion_info(mut self, mutual_group_id: Option<usize>, _is_recursive: bool) -> Self {
        self.mutual_group_id = mutual_group_id;
        self
    }

    fn get_mutual_group_id(&self) -> Option<usize> {
        self.mutual_group_id
    }
}
