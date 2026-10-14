//! Stage 10 postcondition: no raw `BinOp` / `Cast` on `Type::UInt(N)`
//! survives.
//!
//! Walks every non-native function body (via the shared typed-scope
//! walker in [`crate::ir::analysis::scope`]) and reports the first
//! offending site.
//!
//! The check is best-effort in two ways, both preserved by the local
//! [`WalkErr`] split:
//!
//! - A **per-node** `type_of` failure at a `BinOp` / `Cast` operand is
//!   tolerated -- we only flag a site we can positively type as
//!   `UInt(N)`. The base validator that runs after stage 10 catches
//!   other malformedness.
//! - A **scope-building** `type_of` failure (an unresolvable `Let`
//!   value / `While` init) skips the rest of that function. This is the
//!   same per-function tolerance the collect / rewrite passes apply:
//!   they skip such a function too (see `rewrite::run`), so the raw
//!   `BinOp`s they leave behind there must not be re-flagged here.
//!
//! Because the rewrite and this check now share one scope-building
//! policy (`bind_pattern`, full recursion, accurate match-arm types),
//! the rewrite lowers exactly the sites this check inspects -- a
//! survivor here would mean the rewrite genuinely failed to lower it.

use crate::ir::analysis::scope::{walk_typed_block, TypedScope, TypedScopeVisitor};
use crate::ir::analysis::type_of::{type_of, TypeOfError};
use crate::ir::expr::Expr;
use crate::ir::ops::{BinOp, UnOp};
use crate::ir::ty::Type;
use crate::ir::{FunId, Program};

use super::Stage10Error;

pub fn check(program: &Program) -> Result<(), Stage10Error> {
    for (fid, f) in &program.functions {
        let scope: TypedScope = f
            .signature
            .params
            .iter()
            .map(|p| (p.var.clone(), p.ty.clone()))
            .collect();
        let mut checker = SurvivorCheck { fid: *fid, program };
        match walk_typed_block(&mut checker, &f.body, scope, program) {
            Ok(()) => {}
            Err(WalkErr::Survivor(msg)) => return Err(Stage10Error::Postcondition(msg)),
            // Scope-building type_of failure: the base validator owns
            // that malformedness, and collect/rewrite already skipped
            // this function. Tolerate it here too.
            Err(WalkErr::TypeOf(_)) => {}
        }
    }
    Ok(())
}

/// A raw `BinOp` / `Cast` survivor (real violation) vs. a scope-building
/// `type_of` failure (tolerated per-function skip). Keeping them
/// distinct lets `check` propagate the former and swallow the latter.
enum WalkErr {
    Survivor(String),
    TypeOf(TypeOfError),
}

impl From<TypeOfError> for WalkErr {
    fn from(e: TypeOfError) -> Self {
        WalkErr::TypeOf(e)
    }
}

struct SurvivorCheck<'a> {
    fid: FunId,
    program: &'a Program,
}

impl TypedScopeVisitor for SurvivorCheck<'_> {
    type Error = WalkErr;

    fn visit_expr(&mut self, e: &Expr, scope: &TypedScope) -> Result<(), WalkErr> {
        match e {
            Expr::BinOp { op, lhs, .. } => {
                if let Ok(lhs_ty) = type_of(lhs, scope, self.program) {
                    if matches!(lhs_ty, Type::UInt(_)) && !matches!(op, BinOp::And | BinOp::Or) {
                        return Err(WalkErr::Survivor(format!(
                            "function {}: raw BinOp::{op:?} on {lhs_ty:?} survived stage 10",
                            self.fid
                        )));
                    }
                }
            }
            Expr::UnOp { op, operand } => {
                if let UnOp::Cast(_) = op {
                    if let Ok(ty) = type_of(operand, scope, self.program) {
                        if matches!(ty, Type::UInt(_)) {
                            return Err(WalkErr::Survivor(format!(
                                "function {}: raw UnOp::Cast on {ty:?} survived stage 10",
                                self.fid
                            )));
                        }
                    }
                }
                if let UnOp::BitNot = op {
                    if let Ok(ty) = type_of(operand, scope, self.program) {
                        if matches!(ty, Type::UInt(_)) {
                            return Err(WalkErr::Survivor(format!(
                                "function {}: raw UnOp::BitNot on {ty:?} survived stage 10",
                                self.fid
                            )));
                        }
                    }
                }
            }
            _ => {}
        }
        Ok(())
    }
}
