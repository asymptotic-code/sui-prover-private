//! Stage-4 postcondition wrapper.
//!
//! Per `plans/lean-pipeline/stage-04-erase-mut.md` "Outputs", stage 4
//! promises:
//!
//! - Zero `Expr::ReadRef` anywhere in any non-native function body.
//! - Zero `Expr::BorrowLoc` / `Expr::BorrowField` outside the tail
//!   position of a pattern-4b sub-field-mutref-returning function.
//! - Zero `Type::MutableRef` reachable from any non-pattern-4b
//!   function body or non-pattern-4b function signature.
//!
//! The checker recognises pattern-4b via the same tail-shape test
//! `strip_types::is_pattern_4b` uses: return type is `MutableRef`
//! AND the body's tail is `BlockTail::Value(BorrowLoc | BorrowField)`.

use crate::ir::validate::{validate_program, ValidationError};
use crate::ir::{
    visit::{walk_block_default, walk_expr_default, Visitor},
    Block, BlockTail, Expr, FunId, Program, Type,
};

/// Stage-4 postcondition errors.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PostconditionError {
    /// The base IR validator rejected the program.
    BaseValidator(ValidationError),
    /// A non-native function body still contains an `Expr::ReadRef`.
    /// Stage 4 should have substituted these.
    LingeringReadRef { function: FunId },
    /// A non-native function body still contains an `Expr::BorrowLoc`
    /// or `Expr::BorrowField` that is NOT the tail value of a
    /// pattern-4b sub-field-mutref-returning function. These bindings
    /// should have been dropped as dead by Rewrite 2.
    RogueMutBorrow { function: FunId },
    /// A non-native, non-pattern-4b function references
    /// `Type::MutableRef` somewhere reachable from its body
    /// (`Call::type_args` / `Pack::type_args` / `Quantifier::binder_type`).
    /// Stage 4 should have stripped these.
    ResidualMutableRefInBody { function: FunId },
    /// A non-native, non-pattern-4b function signature still has a
    /// `Type::MutableRef` somewhere (param or return).
    MutableRefInNonPattern4bReturn { function: FunId },
}

impl From<ValidationError> for PostconditionError {
    fn from(e: ValidationError) -> Self {
        PostconditionError::BaseValidator(e)
    }
}

/// Run stage-4 postcondition checks against `program`.
///
/// Walks every non-native function. Skips natives entirely (they
/// retain their hand-written `Mutable<V, S>` signatures). Pattern-4b
/// functions are exempt from the body-mutref and return-mutref
/// checks; their tail `BorrowLoc` / `BorrowField` is also exempt
/// from the rogue-mutborrow check.
pub fn check(program: &Program) -> Result<(), PostconditionError> {
    validate_program(program)?;
    for (&fid, func) in &program.functions {
        let is_4b = is_pattern_4b_return(&func.signature.return_type, &func.body);

        check_read_refs(fid, &func.body)?;
        check_borrow_ops(fid, &func.body, is_4b)?;
        check_signature_mutref(fid, &func.signature, is_4b)?;
        check_body_type_slots(fid, &func.body, is_4b)?;
    }
    Ok(())
}

/// Pattern 4b: return type is `MutableRef` AND body tail is a
/// `BorrowLoc` / `BorrowField`.
fn is_pattern_4b_return(return_type: &Type, body: &Block) -> bool {
    if !matches!(return_type, Type::MutableRef { .. }) {
        return false;
    }
    matches!(
        &body.tail,
        BlockTail::Value(Expr::BorrowLoc(_))
            | BlockTail::Value(Expr::Borrow {
                step: crate::ir::path::PathStep::Field { .. },
                ..
            })
    )
}

// ---------------------------------------------------------------------------
// ReadRef check
// ---------------------------------------------------------------------------

fn check_read_refs(fid: FunId, body: &Block) -> Result<(), PostconditionError> {
    let mut w = FindReadRef { found: false };
    w.visit_block(body);
    if w.found {
        Err(PostconditionError::LingeringReadRef { function: fid })
    } else {
        Ok(())
    }
}

struct FindReadRef {
    found: bool,
}

impl Visitor for FindReadRef {
    fn visit_block(&mut self, b: &Block) {
        if self.found {
            return;
        }
        walk_block_default(self, b);
    }
    fn visit_expr(&mut self, e: &Expr) {
        if self.found {
            return;
        }
        if matches!(e, Expr::ReadRef(_)) {
            self.found = true;
            return;
        }
        walk_expr_default(self, e);
    }
}

// ---------------------------------------------------------------------------
// BorrowLoc / BorrowField check
// ---------------------------------------------------------------------------

fn check_borrow_ops(fid: FunId, body: &Block, is_4b: bool) -> Result<(), PostconditionError> {
    // Pattern 4b: exempt the body's tail BorrowLoc/BorrowField (and
    // its supporting `Stmt::Let { value: BorrowLoc | BorrowField }`
    // bindings that chain into it). The simple shape: every
    // `BorrowLoc` / `BorrowField` appears either inside a
    // `Stmt::Let` value or in the tail. Allow these only when 4b.
    //
    // The check is: walk every Block descending into `If`/`Match`/`While`
    // arms; for each block, the tail expression and Stmt::Let values
    // may carry BorrowLoc/BorrowField iff this is the function's
    // top-level body AND is_4b. Any non-4b function has zero
    // BorrowLoc/BorrowField, anywhere.
    if is_4b {
        check_borrow_ops_pattern_4b(fid, body)
    } else {
        check_borrow_ops_non_pattern_4b(fid, body)
    }
}

fn check_borrow_ops_non_pattern_4b(fid: FunId, body: &Block) -> Result<(), PostconditionError> {
    let mut w = FindBorrow { found: false };
    w.visit_block(body);
    if w.found {
        Err(PostconditionError::RogueMutBorrow { function: fid })
    } else {
        Ok(())
    }
}

fn check_borrow_ops_pattern_4b(fid: FunId, body: &Block) -> Result<(), PostconditionError> {
    // For pattern 4b: only the top-level body's tail and the
    // `Stmt::Let { value: BorrowLoc | BorrowField }` bindings
    // feeding it are allowed. Anywhere else (nested If/Match
    // bodies, BorrowOps not in this top-level shape) is rogue.
    //
    // Practical implementation: scan ALL stmts in the top-level
    // body. Each `Stmt::Let { value: BorrowLoc | BorrowField }` is
    // permitted; every other expr must have no BorrowOp. The tail
    // is permitted to be a top-level BorrowLoc/BorrowField; if it
    // wraps something else, the wrapping expression must contain
    // no BorrowOps. Then descend into nested blocks (If/Match/...)
    // with the non-4b rule.
    for stmt in &body.stmts {
        match stmt {
            crate::ir::Stmt::Let { value, .. } => {
                if matches!(
                    value,
                    Expr::BorrowLoc(_)
                        | Expr::Borrow {
                            step: crate::ir::path::PathStep::Field { .. },
                            ..
                        }
                ) {
                    // Permitted. The base of a `BorrowField` may
                    // also descend into nested expressions, but stage
                    // 2 emits `BorrowField` with `base: Var(_)` or
                    // `base: BorrowLoc(_)` -- never a deeper tree
                    // containing arbitrary mid-IR ops. Quick check:
                    // ensure no nested BorrowOps inside arbitrary
                    // expressions.
                    if let Expr::Borrow {
                        step: crate::ir::path::PathStep::Field { .. },
                        base,
                    } = value
                    {
                        // base is allowed to be Var or BorrowLoc; if
                        // it nests deeper, recurse.
                        if !matches!(
                            base.as_ref(),
                            Expr::Var(_)
                                | Expr::BorrowLoc(_)
                                | Expr::Borrow {
                                    step: crate::ir::path::PathStep::Field { .. },
                                    ..
                                }
                        ) {
                            return Err(PostconditionError::RogueMutBorrow { function: fid });
                        }
                    }
                } else {
                    // Disallowed: a Stmt::Let whose value isn't a
                    // BorrowLoc/BorrowField must not contain any
                    // BorrowOp.
                    let mut w = FindBorrow { found: false };
                    w.visit_expr(value);
                    if w.found {
                        return Err(PostconditionError::RogueMutBorrow { function: fid });
                    }
                }
            }
            crate::ir::Stmt::Eval(e) => {
                let mut w = FindBorrow { found: false };
                w.visit_expr(e);
                if w.found {
                    return Err(PostconditionError::RogueMutBorrow { function: fid });
                }
            }
        }
    }
    // The tail: at the top level for 4b, may be BorrowLoc / BorrowField
    // (the function's return value). Anything else: no embedded
    // BorrowOps.
    match &body.tail {
        BlockTail::Value(Expr::BorrowLoc(_))
        | BlockTail::Value(Expr::Borrow {
            step: crate::ir::path::PathStep::Field { .. },
            ..
        }) => {}
        BlockTail::Value(e) => {
            let mut w = FindBorrow { found: false };
            w.visit_expr(e);
            if w.found {
                return Err(PostconditionError::RogueMutBorrow { function: fid });
            }
        }
        BlockTail::Break { value, .. }
        | BlockTail::Continue { value, .. }
        | BlockTail::Return(value)
        | BlockTail::ReturnFromBlock { value, .. } => {
            let mut w = FindBorrow { found: false };
            w.visit_expr(value);
            if w.found {
                return Err(PostconditionError::RogueMutBorrow { function: fid });
            }
        }
        BlockTail::Abort { code } => {
            let mut w = FindBorrow { found: false };
            w.visit_expr(code);
            if w.found {
                return Err(PostconditionError::RogueMutBorrow { function: fid });
            }
        }
    }
    Ok(())
}

struct FindBorrow {
    found: bool,
}

impl Visitor for FindBorrow {
    fn visit_block(&mut self, b: &Block) {
        if self.found {
            return;
        }
        walk_block_default(self, b);
    }
    fn visit_expr(&mut self, e: &Expr) {
        if self.found {
            return;
        }
        if matches!(
            e,
            Expr::BorrowLoc(_)
                | Expr::Borrow {
                    step: crate::ir::path::PathStep::Field { .. },
                    ..
                }
        ) {
            self.found = true;
            return;
        }
        walk_expr_default(self, e);
    }
}

// ---------------------------------------------------------------------------
// Signature MutableRef check
// ---------------------------------------------------------------------------

fn check_signature_mutref(
    fid: FunId,
    sig: &crate::ir::Signature,
    is_4b: bool,
) -> Result<(), PostconditionError> {
    for param in &sig.params {
        if contains_mutable_ref(&param.ty) {
            return Err(PostconditionError::MutableRefInNonPattern4bReturn { function: fid });
        }
    }
    if !is_4b && contains_mutable_ref(&sig.return_type) {
        return Err(PostconditionError::MutableRefInNonPattern4bReturn { function: fid });
    }
    Ok(())
}

/// Recursively check whether `t` contains a `Type::MutableRef`
/// anywhere (including under `Vector`, `Tuple`, `Reference`, or
/// `Struct::type_args`).
fn contains_mutable_ref(t: &Type) -> bool {
    match t {
        Type::MutableRef { .. } => true,
        Type::Vector(inner) | Type::Reference(inner) => contains_mutable_ref(inner),
        Type::Tuple(items) => items.iter().any(contains_mutable_ref),
        Type::Struct { type_args, .. } => type_args.iter().any(contains_mutable_ref),
        _ => false,
    }
}

// ---------------------------------------------------------------------------
// Body type-slot check
// ---------------------------------------------------------------------------

fn check_body_type_slots(fid: FunId, body: &Block, _is_4b: bool) -> Result<(), PostconditionError> {
    // is_4b doesn't grant a body-type-slot exemption: stage 4
    // strips `type_args` / `binder_type` mutref even in pattern-4b
    // functions. The exemption is only at the signature level.
    let mut w = FindMutRefInTypeSlots { found: false };
    w.visit_block(body);
    if w.found {
        Err(PostconditionError::ResidualMutableRefInBody { function: fid })
    } else {
        Ok(())
    }
}

struct FindMutRefInTypeSlots {
    found: bool,
}

impl Visitor for FindMutRefInTypeSlots {
    fn visit_block(&mut self, b: &Block) {
        if self.found {
            return;
        }
        walk_block_default(self, b);
    }
    fn visit_expr(&mut self, e: &Expr) {
        if self.found {
            return;
        }
        match e {
            Expr::Call { type_args, .. } | Expr::Pack { type_args, .. }
                if type_args.iter().any(contains_mutable_ref) =>
            {
                self.found = true;
                return;
            }
            Expr::Quantifier { binder_type, .. } if contains_mutable_ref(binder_type) => {
                self.found = true;
                return;
            }
            _ => {}
        }
        walk_expr_default(self, e);
    }
}
