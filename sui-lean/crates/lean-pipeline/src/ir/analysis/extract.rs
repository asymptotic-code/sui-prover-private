//! Lift a `Block` into its own `Function`.
//!
//! This standalone utility validates explicit captures and constructs a
//! sibling [`Function`]. Allocation and insertion remain caller-owned.
//!
//! Scope of this helper:
//! - **Block-level only**. Single-expression extraction wraps in
//!   `Block { stmts: [], tail: Value(expr) }` first.
//! - **Captures are explicit**. Caller supplies the `(VarId, Type)`
//!   list (typically computed via `crate::ir::analysis::free_vars`,
//!   then intersected with the parent's local-type table for types).
//!   Order is preserved -- callers that want determinism should sort
//!   on the way in.
//! - **Tails are NOT rewritten**. A `BlockTail::Continue { level: 0 }`
//!   inside the extracted body still references "the innermost
//!   enclosing loop" -- which from inside the helper is meaningless.
//!   Callers must pre-rewrite jump tails into `Value(Call(...))`
//!   targeting the appropriate sibling helpers before calling
//!   `extract_block`. This keeps the helper free of stage-specific
//!   knowledge.
//! - **Mut-ref captures are rejected**. Capturing a
//!   `Type::MutableRef` across a function boundary requires
//!   honoring stage-3 (mut-to-let)'s augmented-return convention --
//!   the helper would have to take a `Mutation T` param AND rewrite
//!   tails to return augmented tuples. That work is deferred; until
//!   then, callers must either pre-rewrite mut-ref locals away or
//!   avoid extracting blocks that capture them.
//!
//! What the helper DOES do:
//! - Validates captures (no `MutableRef`).
//! - Validates that captures cover every free var of `body`
//!   (defensive; catches caller bugs in the free-vars computation).
//! - Builds a `Function` with the right signature, kind, effects,
//!   type_params, and body.
//!
//! What the helper does NOT do:
//! - Allocate a `FunId`.
//! - Insert into a `Program`.
//! - Recompute effects (caller decides; default conservatively
//!   `Effects::CONSERVATIVE`).

use std::collections::BTreeSet;

use crate::ir::analysis::free_vars::free_vars;
use crate::ir::expr::Block;
use crate::ir::function::{Function, FunctionKind, Param, Signature};
use crate::ir::ty::Type;
use crate::ir::{ModId, VarId};

/// Specification of an extraction target.
#[derive(Debug, Clone)]
pub struct ExtractSpec {
    /// Module that owns the extracted helper. Typically the parent
    /// function's module.
    pub module: ModId,
    /// Human-readable Lean name (e.g. `"f.while_0"`,
    /// `"f.while_0.after"`, `"g.aborts"`). The renderer reads this
    /// directly; the pipeline tracks the structural relationship via
    /// [`FunctionKind`] independently.
    pub name: String,
    /// Structural role.
    pub kind: FunctionKind,
    /// Captured locals -> the helper's params, in this order. Each
    /// entry is `(var_name, var_type)`. `var_name` is reused as
    /// both the [`Param::var`] (SSA id) and the [`Param::name`]
    /// (user-visible). Caller is responsible for ordering -- a
    /// sorted order yields deterministic output.
    pub captured: Vec<(VarId, Type)>,
    /// Helper's return type. The caller is responsible for choosing a type
    /// compatible with the rewritten body and its call sites.
    pub return_type: Type,
    /// Type parameters inherited from the parent. The helper takes
    /// the full list even if the body doesn't reference all of
    /// them -- simpler than computing the used subset, and the
    /// renderer can dead-code-eliminate later.
    pub type_params: Vec<String>,
    /// Effects classification. The caller decides whether to inherit or
    /// recompute it.
    pub effects: crate::ir::Effects,
}

/// Errors produced by [`extract_block`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ExtractError {
    /// `captured` contains a `Type::MutableRef`. Extraction across
    /// function boundaries with mut-ref captures requires honoring
    /// stage-3's mut-to-let augmented-return contract. Transparent
    /// support is deferred; until then, callers must avoid
    /// extracting blocks that capture mut-refs.
    MutableRefCapture { var: VarId },
    /// `body` references `var` but `captured` doesn't list it and
    /// nothing inside `body` binds it. Defensive; usually means the
    /// caller's free-vars computation missed a use.
    UncapturedFreeVar { var: VarId },
    /// Two entries in `captured` use the same `VarId`. Would produce
    /// an ambiguous `Param` list.
    DuplicateCapture { var: VarId },
}

/// Build a `Function` from a `Block` plus an extraction spec.
///
/// Does not allocate a `FunId` or insert into a `Program`; the caller owns
/// both operations.
pub fn extract_block(spec: ExtractSpec, body: Block) -> Result<Function, ExtractError> {
    // Reject mut-ref captures (extension point).
    for (var, ty) in &spec.captured {
        if matches!(ty, Type::MutableRef { .. }) {
            return Err(ExtractError::MutableRefCapture { var: var.clone() });
        }
    }

    // Reject duplicate captures.
    let mut seen: BTreeSet<VarId> = BTreeSet::new();
    for (var, _) in &spec.captured {
        if !seen.insert(var.clone()) {
            return Err(ExtractError::DuplicateCapture { var: var.clone() });
        }
    }

    // Validate that captures cover every free var of body.
    let actual = free_vars(&body);
    for v in &actual {
        if !seen.contains(v) {
            return Err(ExtractError::UncapturedFreeVar { var: v.clone() });
        }
    }

    let params = spec
        .captured
        .into_iter()
        .map(|(var, ty)| Param {
            name: var.to_string(),
            var,
            ty,
        })
        .collect();

    Ok(Function {
        module: spec.module,
        name: spec.name,
        signature: Signature {
            type_params: spec.type_params,
            params,
            return_type: spec.return_type,
        },
        body,
        kind: spec.kind,
        effects: spec.effects,
        explicit_pure: false,
    })
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::builder::{block, just, let_stmt, lit_u64, tail_value, unit, var};
    use crate::ir::function::{FunctionKind, SpecKind};
    use crate::ir::ops::BinOp;
    use crate::ir::ty::Type;
    use crate::ir::Expr;

    fn vid(s: &str) -> VarId {
        s.into()
    }

    fn simple_spec(captured: Vec<(VarId, Type)>) -> ExtractSpec {
        ExtractSpec {
            module: 0,
            name: "f.helper".to_string(),
            kind: FunctionKind::Synthetic,
            captured,
            return_type: Type::UInt(64),
            type_params: vec![],
            effects: crate::ir::Effects::CONSERVATIVE,
        }
    }

    #[test]
    fn extracts_block_with_no_captures() {
        // Body: `{ 42 }` -- no free vars, no captures needed.
        let body = just(lit_u64(42));
        let f = extract_block(simple_spec(vec![]), body.clone()).expect("extracts");
        assert_eq!(f.module, 0);
        assert_eq!(f.name, "f.helper");
        assert_eq!(f.signature.params.len(), 0);
        assert_eq!(f.signature.return_type, Type::UInt(64));
        assert_eq!(f.body, body);
        assert!(matches!(f.kind, FunctionKind::Synthetic));
        assert_eq!(f.effects, crate::ir::Effects::CONSERVATIVE);
    }

    #[test]
    fn extracts_block_with_captures_in_param_order() {
        // Body uses `x` and `y`; captures = [(x, u64), (y, u64)].
        let body = just(Expr::BinOp {
            op: BinOp::Add,
            lhs: Box::new(var("x")),
            rhs: Box::new(var("y")),
        });
        let f = extract_block(
            simple_spec(vec![(vid("x"), Type::UInt(64)), (vid("y"), Type::UInt(64))]),
            body,
        )
        .expect("extracts");
        assert_eq!(f.signature.params.len(), 2);
        assert_eq!(&*f.signature.params[0].var, "x");
        assert_eq!(f.signature.params[0].name, "x");
        assert_eq!(f.signature.params[0].ty, Type::UInt(64));
        assert_eq!(&*f.signature.params[1].var, "y");
    }

    #[test]
    fn rejects_mut_ref_capture() {
        let body = just(var("r"));
        let mut_ref = Type::MutableRef {
            inner: Box::new(Type::UInt(64)),
            root: Box::new(Type::UInt(64)),
        };
        let err = extract_block(simple_spec(vec![(vid("r"), mut_ref)]), body)
            .expect_err("must reject mut-ref capture");
        assert_eq!(err, ExtractError::MutableRefCapture { var: vid("r") });
    }

    #[test]
    fn rejects_uncaptured_free_var() {
        // Body uses `x` and `y` but captures only `x`.
        let body = just(Expr::BinOp {
            op: BinOp::Add,
            lhs: Box::new(var("x")),
            rhs: Box::new(var("y")),
        });
        let err = extract_block(simple_spec(vec![(vid("x"), Type::UInt(64))]), body)
            .expect_err("must reject uncaptured free var");
        assert_eq!(err, ExtractError::UncapturedFreeVar { var: vid("y") });
    }

    #[test]
    fn rejects_duplicate_capture() {
        let body = just(var("x"));
        let err = extract_block(
            simple_spec(vec![(vid("x"), Type::UInt(64)), (vid("x"), Type::Bool)]),
            body,
        )
        .expect_err("must reject duplicate capture");
        assert_eq!(err, ExtractError::DuplicateCapture { var: vid("x") });
    }

    #[test]
    fn body_with_local_let_doesnt_need_to_capture_local() {
        // Body: `{ let z = 1; z + x }` -- z is bound locally, x is free.
        let body = block(
            vec![let_stmt(&["z"], lit_u64(1))],
            tail_value(Expr::BinOp {
                op: BinOp::Add,
                lhs: Box::new(var("z")),
                rhs: Box::new(var("x")),
            }),
        );
        let f =
            extract_block(simple_spec(vec![(vid("x"), Type::UInt(64))]), body).expect("extracts");
        assert_eq!(f.signature.params.len(), 1);
        assert_eq!(&*f.signature.params[0].var, "x");
    }

    #[test]
    fn loop_body_kind_preserved() {
        let body = just(unit());
        let spec = ExtractSpec {
            module: 3,
            name: "f.while_0".to_string(),
            kind: FunctionKind::LoopBody { parent: 7, slot: 0 },
            captured: vec![],
            return_type: Type::Unit,
            type_params: vec![],
            effects: crate::ir::Effects::PURE,
        };
        let f = extract_block(spec, body).unwrap();
        match f.kind {
            FunctionKind::LoopBody { parent, slot } => {
                assert_eq!(parent, 7);
                assert_eq!(slot, 0);
            }
            other => panic!("expected LoopBody, got {other:?}"),
        }
        assert_eq!(f.module, 3);
        assert_eq!(f.effects, crate::ir::Effects::PURE);
    }

    #[test]
    fn spec_companion_kind_preserved() {
        let body = just(crate::ir::builder::lit_bool(false));
        let spec = ExtractSpec {
            module: 0,
            name: "g.aborts".to_string(),
            kind: FunctionKind::Spec {
                kind: SpecKind::Aborts,
                target: 11,
            },
            captured: vec![],
            return_type: Type::Bool,
            type_params: vec![],
            effects: crate::ir::Effects::PURE,
        };
        let f = extract_block(spec, body).unwrap();
        match f.kind {
            FunctionKind::Spec {
                kind: SpecKind::Aborts,
                target,
            } => assert_eq!(target, 11),
            other => panic!("expected Spec(Aborts), got {other:?}"),
        }
    }

    #[test]
    fn type_params_inherited_verbatim() {
        let body = just(unit());
        let spec = ExtractSpec {
            module: 0,
            name: "f.helper".to_string(),
            kind: FunctionKind::Synthetic,
            captured: vec![],
            return_type: Type::Unit,
            type_params: vec!["T".to_string(), "U".to_string()],
            effects: crate::ir::Effects::CONSERVATIVE,
        };
        let f = extract_block(spec, body).unwrap();
        assert_eq!(
            f.signature.type_params,
            vec!["T".to_string(), "U".to_string()]
        );
    }
}
