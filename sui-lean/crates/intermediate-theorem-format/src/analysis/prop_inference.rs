// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Prop/Bool sort discipline for the spec surface.
//!
//! `forall!`/`exists!` quantify over an entire type and are therefore logical
//! propositions, not computable booleans (see `IRNode::get_type`). There is NO
//! opaque `spec_forall`/`spec_exists` fallback — quantifiers always render as
//! native Lean `∀`/`∃`. Two passes keep the IR well-sorted:
//!
//! * [`infer_prop_returns`] — Move types every spec helper `bool`, but a helper
//!   whose body is a proposition (a quantifier, or a logical `&&`/`||`/`!`/`if`
//!   combination of one) is logically `Prop`. This promotes such functions
//!   `Bool -> Prop` and propagates to callers (fixpoint), so e.g. a `bool`
//!   loop-invariant predicate that is a big `&&`-chain containing a `forall!`
//!   becomes a `Prop` conjunction with a native `∀`.
//!
//! * [`validate_sorts`] — the proper hard-fail. After inference, a quantifier
//!   must live only in `Prop` positions. If a `Bool`-returning function still
//!   contains a `forall!`/`exists!`, the quantifier is genuinely stuck in a
//!   computable-Bool position that cannot be lifted; we panic with an
//!   actionable message rather than emit an unsound/opaque result.

use crate::data::Program;
use crate::{BinOp, Const, IRNode, QuantifierKind, Type, UnOp};

/// In `.aborts` companions, replace every `forall!`/`exists!` with `false`.
/// A quantifier predicate is required to be pure (the quantifier-fold enforces
/// `ext(pure)`/`no_abort`), so evaluating it never aborts — its abort
/// contribution is `false`. This keeps `.aborts` bodies purely computable Bool
/// (no Prop quantifier stuck in a Bool position). Runs before
/// [`infer_prop_returns`] so `.aborts` stays Bool.
pub fn strip_quantifiers_in_aborts(program: &mut Program) {
    let aborts_ids: Vec<usize> = program
        .functions
        .iter()
        .filter(|(_, f)| !f.is_native && f.name.ends_with(".aborts"))
        .map(|(id, _)| id)
        .collect();
    for id in aborts_ids {
        let body = std::mem::take(&mut program.functions.get_mut(id).body);
        let new_body = body.map(&mut |n| match n {
            IRNode::Quantifier {
                kind: QuantifierKind::Forall | QuantifierKind::Exists,
                ..
            } => IRNode::Const(Const::Bool(false)),
            other => other,
        });
        program.functions.get_mut(id).body = new_body;
    }
}

/// True if `node` denotes a logical proposition. Total and panic-free, and
/// cheap: it reads callee return types straight from `program` (no
/// `VariableRegistry`, which would clone the whole signature map per call).
fn is_prop_expr(node: &IRNode, program: &Program) -> bool {
    match node {
        IRNode::Quantifier { kind, .. } => {
            matches!(kind, QuantifierKind::Forall | QuantifierKind::Exists)
        }
        IRNode::ToProp(_) => true,
        IRNode::UnOp {
            op: UnOp::Not,
            operand,
        } => is_prop_expr(operand, program),
        IRNode::BinOp {
            op: BinOp::And | BinOp::Or,
            lhs,
            rhs,
        } => is_prop_expr(lhs, program) || is_prop_expr(rhs, program),
        IRNode::Call { function, .. } => {
            matches!(
                program.functions.get(function).signature.return_type,
                Type::Prop
            )
        }
        // The value flows from the tail of a Let / either If branch / either
        // If condition (a `c && b` short-circuit lowers to `if c then b`).
        IRNode::Let { body, .. } => is_prop_expr(body, program),
        IRNode::If {
            cond,
            then_branch,
            else_branch,
        } => {
            is_prop_expr(cond, program)
                || is_prop_expr(then_branch, program)
                || is_prop_expr(else_branch, program)
        }
        _ => false,
    }
}

/// Promote every non-native function whose body is a proposition from `Bool`
/// to `Prop`, to a fixpoint so the promotion propagates to callers. Returns the
/// ids promoted. A no-op on programs without quantifiers.
pub fn infer_prop_returns(program: &mut Program) -> Vec<usize> {
    let mut promoted = Vec::new();
    loop {
        let candidates: Vec<usize> = program
            .functions
            .iter()
            .filter(|(_, f)| !f.is_native && f.signature.return_type == Type::Bool)
            .map(|(id, _)| id)
            .collect();

        let mut changed = false;
        for id in candidates {
            let promote = {
                let func = program.functions.get(&id);
                is_prop_expr(&func.body, program)
            };
            if promote {
                program.functions.get_mut(id).signature.return_type = Type::Prop;
                promoted.push(id);
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
    promoted
}

/// Whether a body syntactically contains a `forall!`/`exists!` anywhere.
fn contains_quantifier(node: &IRNode) -> bool {
    node.iter().any(|n| {
        matches!(
            n,
            IRNode::Quantifier {
                kind: QuantifierKind::Forall | QuantifierKind::Exists,
                ..
            }
        )
    })
}

/// Enforce: after inference, a `forall!`/`exists!` lives only in `Prop`
/// positions. A `Bool`-returning function that still contains one means the
/// quantifier is stuck where a computable Bool is required — panic loudly
/// rather than fall back to an opaque/unsound encoding.
pub fn validate_sorts(program: &Program) {
    let mut violations: Vec<String> = Vec::new();
    for (_, func) in program.functions.iter() {
        if func.is_native {
            continue;
        }
        if func.signature.return_type == Type::Bool && contains_quantifier(&func.body) {
            violations.push(format!(
                "  `{}` returns Bool but its body contains a `forall!`/`exists!`",
                func.name
            ));
        }
    }
    if !violations.is_empty() {
        panic!(
            "Prop/Bool sort violation: a `forall!`/`exists!` (a proposition over a type) is stuck \
             in a computable-Bool position. A proposition is not decidable (no instance short of \
             explosive enumeration or classical choice), so it cannot be a runtime Bool. Restructure \
             the spec so the quantifier sits in a proposition (the enclosing predicate should be \
             logical, not a value computed and branched on).\n{}",
            violations.join("\n")
        );
    }
}
