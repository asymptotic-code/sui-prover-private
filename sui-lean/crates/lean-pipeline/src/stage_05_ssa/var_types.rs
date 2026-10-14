//! Best-effort per-function `VarId -> Type` map for stage 5.
//!
//! Stage 5's `UninitFromZeroIterLoop` path needs a typed `default`
//! init for a loop-carried var whose pre-loop value isn't available
//! (e.g. a World dynamic-field store key borrowed late in a loop body
//! and written back at the loop header). This recovers each
//! source-name's type so the init can be `Const::Default(ty)`.
//!
//! A [`Visitor`] walks the pre-SSA body: seed scope from params, then
//! `type_of` + `bind_pattern` each `Stmt::Let` (value typed in the
//! pre-binding scope), recursing into every nested block via the shared
//! traversal. Best-effort -- untypable lets are skipped (the caller
//! falls back to the original reject when a needed var's type is
//! missing).

use std::collections::BTreeMap;

use crate::ir::analysis::type_of::{bind_pattern, type_of};
use crate::ir::visit::Visitor;
use crate::ir::{Function, Program, Stmt, Type, VarId};

/// Build a `source-name -> Type` map over `func`'s pre-SSA body.
pub fn collect(func: &Function, program: &Program) -> BTreeMap<VarId, Type> {
    let mut collector = TypeCollector {
        scope: func
            .signature
            .params
            .iter()
            .map(|p| (p.var.clone(), p.ty.clone()))
            .collect(),
        program,
    };
    collector.visit_block(&func.body);
    collector.scope
}

struct TypeCollector<'a> {
    scope: BTreeMap<VarId, Type>,
    program: &'a Program,
}

impl Visitor for TypeCollector<'_> {
    fn visit_stmt(&mut self, s: &Stmt) {
        match s {
            Stmt::Let { pattern, value } => {
                // Type the value in the pre-binding scope, recurse into
                // it for nested lets, then bind the pattern. A failed
                // inference leaves the var ABSENT (no `Unit` fallback) so
                // the uninit-loop path can tell "type known" from
                // "unknown" and reject the unknown case rather than emit
                // an ill-typed `Const::Default(Unit)`.
                let vt = type_of(value, &self.scope, self.program);
                self.visit_expr(value);
                if let Ok(vt) = vt {
                    let _ = bind_pattern(pattern, &vt, &mut self.scope);
                }
            }
            Stmt::Eval(e) => self.visit_expr(e),
        }
    }
}
