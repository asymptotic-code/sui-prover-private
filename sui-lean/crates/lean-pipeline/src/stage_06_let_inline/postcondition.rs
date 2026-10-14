//! Stage-6 postcondition wrapper.
//!
//! After `run()` completes, the IR satisfies:
//!
//! - No trivial-copy Let `Stmt::Let { pattern: [Some(v)], value: Var(_) | Const(_) }`.
//! - No single-use pure-and-total Let `Stmt::Let { pattern: [Some(v)], value: <pure-total> }`
//!   where `use_count(v) == 1`.
//! - No identity Let `Stmt::Let { pattern: [Some(v)], value: Var(v) }`.
//! - No fully-wildcard Let `Stmt::Let { pattern: [None, None, ...], value: _ }`.
//! - No `Stmt::Eval(<pure-and-total>)`.
//!
//! Each violation maps to a specific `PostconditionError` variant so
//! tests can `assert_matches!` on the precise reason.

use crate::ir::{
    validate::{validate_program, ValidationError},
    visit::{walk_block_default, walk_expr_default, walk_stmt_default, Visitor},
    Block, Expr, FunId, Program, Stmt,
};

use super::effects_predicate::is_pure_total;
use super::use_count::count_uses;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PostconditionError {
    /// Base IR validator rejected the program.
    BaseValidator(ValidationError),
    /// A non-native function has a surviving identity Let
    /// (`let v = Var(v)`).
    IdentityLet { function: FunId },
    /// A non-native function has a surviving trivial-copy Let
    /// (`let v = Var(_) | Const(_)`); sub-pass 2a should have
    /// eliminated it.
    TrivialCopyLet { function: FunId },
    /// A non-native function has a surviving single-use
    /// pure-and-total Let; sub-pass 2b should have inlined it.
    SingleUsePureTotalLet { function: FunId },
    /// A non-native function has a `Stmt::Eval(<pure-and-total>)`;
    /// sub-pass 2d should have dropped it.
    ///
    /// Note: `AllWildcardLet` is not a stage-6 variant -- the base IR
    /// validator already rejects fully-wildcard `Stmt::Let` via
    /// [`crate::ir::validate::ValidationErrorKind::AllWildcardLet`].
    /// Any such Let surfaces here as
    /// `PostconditionError::BaseValidator(...)` before any stage-6
    /// check runs.
    DeadPureTotalEval { function: FunId },
}

impl From<ValidationError> for PostconditionError {
    fn from(e: ValidationError) -> Self {
        PostconditionError::BaseValidator(e)
    }
}

/// Run the base IR validator plus stage-6-specific checks.
pub fn check(program: &Program) -> Result<(), PostconditionError> {
    validate_program(program)?;
    for (&fid, func) in &program.functions {
        let counts = count_uses(&func.body);
        let mut w = ChecksWalker {
            program,
            counts: &counts,
            found: None,
            function: fid,
        };
        w.visit_block(&func.body);
        if let Some(err) = w.found {
            return Err(err);
        }
    }
    Ok(())
}

struct ChecksWalker<'a> {
    program: &'a Program,
    counts: &'a super::use_count::UseCount,
    found: Option<PostconditionError>,
    function: FunId,
}

impl<'a> ChecksWalker<'a> {
    fn fail(&mut self, err: PostconditionError) {
        if self.found.is_none() {
            self.found = Some(err);
        }
    }

    fn check_stmt(&mut self, s: &Stmt) {
        match s {
            Stmt::Let { pattern, value } => {
                // Identity Let.
                if pattern.len() == 1 {
                    if let Some(v) = &pattern[0] {
                        if let Expr::Var(w) = value {
                            if w == v {
                                self.fail(PostconditionError::IdentityLet {
                                    function: self.function,
                                });
                                return;
                            }
                        }
                    }
                }
                // Trivial-copy Let.
                //
                // Mirror `single_use::inline_candidate`'s gating
                // (see the SingleUsePureTotalLet block below): a Let
                // whose binder `v` is referenced via
                // `Expr::BorrowLoc(v)` or `Expr::WriteBack { child:
                // v, .. }` is intentionally NOT inlined -- those
                // VarId slots can't be substituted by an `Expr`,
                // so the Let has to survive to keep `v` bound.
                // Stage 3's mut-to-let lowering routinely produces
                // `let new_var = old_var` patterns precisely to
                // re-bind values across writeback boundaries; those
                // are well-formed trivial copies, not stage-6
                // inliner misses. Without this gate, every mut-rich
                // function with a writeback rewires through a
                // trivial-copy alias would fail the postcondition.
                if pattern.len() == 1 && matches!(value, Expr::Var(_) | Expr::Const(_)) {
                    if let Some(v) = &pattern[0] {
                        if !self.counts.has_borrow_use(v) {
                            self.fail(PostconditionError::TrivialCopyLet {
                                function: self.function,
                            });
                            return;
                        }
                    }
                }
                // Single-use pure-total Let.
                //
                // Mirror `single_use::inline_candidate`'s gating: the
                // inliner deliberately skips a Let whose binder `v`
                // is referenced via `Expr::BorrowLoc(v)` or
                // `Expr::WriteBack { child: v, .. }` -- those VarId
                // slots are not substitutable by an `Expr`, so the
                // Let must survive to keep `v` bound. The
                // postcondition has to skip them too, or it
                // false-positives on well-formed pattern-4b shapes
                // like
                //   let v = Pack { ... };
                //   let _ = WriteBack { ..., child: v };
                if pattern.len() == 1 {
                    if let Some(v) = &pattern[0] {
                        if self.counts.get(v) == 1
                            && !self.counts.has_borrow_use(v)
                            && is_pure_total(value, self.program)
                            && !matches!(value, Expr::Var(_) | Expr::Const(_))
                        {
                            self.fail(PostconditionError::SingleUsePureTotalLet {
                                function: self.function,
                            });
                        }
                    }
                }
                // Note: fully-wildcard Lets (every pattern position
                // is `None`) are rejected by the base IR validator
                // before stage-6 checks run; no stage-6-specific
                // variant for them.
            }
            Stmt::Eval(e) => {
                if is_pure_total(e, self.program) {
                    self.fail(PostconditionError::DeadPureTotalEval {
                        function: self.function,
                    });
                }
            }
        }
    }
}

impl<'a> Visitor for ChecksWalker<'a> {
    fn visit_block(&mut self, b: &Block) {
        if self.found.is_some() {
            return;
        }
        walk_block_default(self, b);
    }

    fn visit_stmt(&mut self, s: &Stmt) {
        if self.found.is_some() {
            return;
        }
        self.check_stmt(s);
        walk_stmt_default(self, s);
    }

    fn visit_expr(&mut self, e: &Expr) {
        if self.found.is_some() {
            return;
        }
        walk_expr_default(self, e);
    }
}
