//! Stage-3 postcondition wrapper.
//!
//! Per `plans/lean-pipeline/stage-03-demut.md` "Outputs", stage 3
//! promises:
//!
//! - Zero `Expr::WriteRef`, zero `Expr::WriteBack` anywhere in any
//!   non-native function body.
//! - Every non-native function with `&mut`-typed params has been
//!   demoted: param types are stripped of `Type::MutableRef`.
//! - Every `Expr::Call` to a demoted callee destructures the
//!   augmented return.
//!
//! `Expr::MutBorrow` (`BorrowLoc` / `BorrowField`) and `Expr::ReadRef`
//! and body-local `Type::MutableRef` are NOT constrained -- those are
//! stage 4's concern.

use crate::ir::validate::{validate_program, ValidationError};
use crate::ir::visit::{walk_block_default, walk_expr_default, Visitor};
use crate::ir::{Block, Expr, FunId, Program, Type};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PostconditionError {
    /// The base IR validator rejected the program.
    BaseValidator(ValidationError),
    /// A non-native function still has `Type::MutableRef` in a
    /// parameter slot. Stage 3 should have stripped these.
    MutRefInParam { function: FunId, param_index: usize },
    /// A non-native function body still contains an `Expr::WriteRef`.
    WriteRefSurvived { function: FunId },
    /// A non-native function body still contains an `Expr::WriteBack`.
    WriteBackSurvived { function: FunId },
}

impl From<ValidationError> for PostconditionError {
    fn from(e: ValidationError) -> Self {
        PostconditionError::BaseValidator(e)
    }
}

/// Run stage-3 postcondition checks against `program`.
pub fn check(program: &Program) -> Result<(), PostconditionError> {
    validate_program(program)?;
    check_no_mut_in_params(program)?;
    check_no_write_ops_in_bodies(program)?;
    Ok(())
}

fn check_no_mut_in_params(program: &Program) -> Result<(), PostconditionError> {
    for (&fid, func) in &program.functions {
        for (idx, param) in func.signature.params.iter().enumerate() {
            if matches!(param.ty, Type::MutableRef { .. }) {
                return Err(PostconditionError::MutRefInParam {
                    function: fid,
                    param_index: idx,
                });
            }
        }
    }
    Ok(())
}

fn check_no_write_ops_in_bodies(program: &Program) -> Result<(), PostconditionError> {
    for (&fid, func) in &program.functions {
        let mut walker = WriteOpWalker { found: None };
        walker.visit_block(&func.body);
        if let Some(kind) = walker.found {
            return Err(match kind {
                WriteOpKind::WriteRef => PostconditionError::WriteRefSurvived { function: fid },
                WriteOpKind::WriteBack => PostconditionError::WriteBackSurvived { function: fid },
            });
        }
    }
    Ok(())
}

#[derive(Debug, Clone, Copy)]
enum WriteOpKind {
    WriteRef,
    WriteBack,
}

struct WriteOpWalker {
    found: Option<WriteOpKind>,
}

impl Visitor for WriteOpWalker {
    fn visit_block(&mut self, b: &Block) {
        if self.found.is_none() {
            walk_block_default(self, b);
        }
    }

    fn visit_expr(&mut self, e: &Expr) {
        if self.found.is_some() {
            return;
        }
        match e {
            Expr::WriteRef { .. } => self.found = Some(WriteOpKind::WriteRef),
            Expr::WriteBack { .. } => self.found = Some(WriteOpKind::WriteBack),
            _ => walk_expr_default(self, e),
        }
    }
}
