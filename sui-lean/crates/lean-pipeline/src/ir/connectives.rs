//! Logical-connective intrinsics for proof-obligation statements.
//!
//! `stage_12_obligations` builds each theorem statement as a Bool
//! `Expr::Call` tree over three synthetic connective natives -- `imp`
//! (implication), `iff`, and `neg`. They take Bool args and return Bool
//! in the IR, so statements stay entirely Bool (no `Prop` type enters
//! the IR). The renderer intercepts calls to them and emits the real
//! Lean `→` / `↔` / `¬` over `ToProp`-coerced operands -- it does NOT
//! desugar to `&&` / `||` / `!` (those are the existing `BinOp::And/Or`
//! / `UnOp::Not`, which render the Bool operators).
//!
//! This module is the single source of truth for the connectives'
//! identity: their reserved native names, signatures, effects, and
//! synthetic provenance. Stage 12 registers them through
//! `Program::insert_synthetic_native`, and the renderer requires that
//! complete identity before dispatching them. The names carry a `$`
//! prefix and never appear verbatim in normal rendered output.

use crate::ir::{Effects, NativeDecl, Param, Signature, Type, VarId};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Connective {
    /// `a → b`
    Imp,
    /// `a ↔ b`
    Iff,
    /// `¬ a`
    Neg,
}

impl Connective {
    pub const ALL: [Connective; 3] = [Connective::Imp, Connective::Iff, Connective::Neg];

    /// Reserved native name. Never rendered verbatim -- the renderer
    /// maps a call to this callee onto a Lean operator.
    pub fn native_name(self) -> &'static str {
        match self {
            Connective::Imp => "$prover_imp",
            Connective::Iff => "$prover_iff",
            Connective::Neg => "$prover_neg",
        }
    }

    /// Recover the connective a callee name denotes, if any. Used by the
    /// renderer to dispatch a `Call` onto `→` / `↔` / `¬`.
    pub fn from_native_name(name: &str) -> Option<Connective> {
        Connective::ALL
            .into_iter()
            .find(|c| c.native_name() == name)
    }

    /// Recover a pipeline connective only from its complete synthetic
    /// declaration. Reserved names alone are not intrinsic: user natives and
    /// malformed framework declarations must render as ordinary calls.
    pub fn from_native_decl(decl: &NativeDecl) -> Option<Connective> {
        let connective = Self::from_native_name(&decl.name)?;
        (decl.signature == connective.signature()
            && decl.effects == Effects::PURE
            && decl.explicit_pure
            && decl.is_framework
            && decl.spec_target.is_none()
            && decl.user_native.is_none())
        .then_some(connective)
    }

    /// Operand count: `Neg` is unary, `Imp` / `Iff` binary.
    pub fn arity(self) -> usize {
        match self {
            Connective::Neg => 1,
            Connective::Imp | Connective::Iff => 2,
        }
    }

    /// `(Bool, ..) -> Bool`, one Bool param per operand. The registered
    /// synthetic native carries this signature so call sites type-check
    /// against the IR validator's arity check.
    pub fn signature(self) -> Signature {
        let params = (0..self.arity())
            .map(|i| Param {
                name: format!("a{i}"),
                var: VarId::from(format!("$c{i}")),
                ty: Type::Bool,
            })
            .collect();
        Signature {
            type_params: Vec::new(),
            params,
            return_type: Type::Bool,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn decl(connective: Connective) -> NativeDecl {
        NativeDecl {
            module: 0,
            name: connective.native_name().to_string(),
            signature: connective.signature(),
            effects: Effects::PURE,
            explicit_pure: true,
            is_framework: true,
            spec_target: None,
            user_native: None,
        }
    }

    #[test]
    fn native_name_roundtrips() {
        for c in Connective::ALL {
            assert_eq!(Connective::from_native_name(c.native_name()), Some(c));
        }
        assert_eq!(Connective::from_native_name("imp"), None);
        assert_eq!(Connective::from_native_name("$prover_xor"), None);
    }

    #[test]
    fn arity_and_signature() {
        assert_eq!(Connective::Neg.arity(), 1);
        assert_eq!(Connective::Imp.arity(), 2);
        assert_eq!(Connective::Iff.arity(), 2);
        for c in Connective::ALL {
            let sig = c.signature();
            assert_eq!(sig.params.len(), c.arity());
            assert_eq!(sig.return_type, Type::Bool);
            assert!(sig.params.iter().all(|p| p.ty == Type::Bool));
        }
    }

    #[test]
    fn declaration_dispatch_requires_synthetic_identity() {
        for connective in Connective::ALL {
            let exact = decl(connective);
            assert_eq!(Connective::from_native_decl(&exact), Some(connective));

            let mut user_native = exact.clone();
            user_native.is_framework = false;
            user_native.user_native = Some(true);
            assert_eq!(Connective::from_native_decl(&user_native), None);

            let mut malformed = exact;
            malformed.signature.return_type = Type::Prop;
            assert_eq!(Connective::from_native_decl(&malformed), None);
        }
    }
}
