//! Stage 7 (rewrite) postcondition validator.
//!
//! See `plans/lean-pipeline/stage-07-rewrite.md` "Output invariants"
//! for the full list. Validates:
//!
//! - Zero `BlockTail::Break / Continue / ReturnFromBlock` and zero
//!   `Expr::LabeledBlock` anywhere.
//! - Zero inner `BlockTail::Return`. Outermost Returns are permitted only on
//!   loop helpers and requires/ensures companions.
//! - Zero `Expr::While` anywhere.
//! - For every source `FunId f`: a paired `Spec(Aborts) { target: f }`
//!   companion exists.
//! - Every `Spec(Aborts)` companion's `signature.return_type` matches
//!   the canonical `Option<MoveAbortCode>` shape (registered by
//!   `option_aborts::ensure_aborts_types`).
//! - Zero surviving `Stmt::Eval(Call(prover::*_id, ..))` (predicates
//!   were collected + removed in phase 1).
//!
use crate::ir::builder::ProverFnIds;
use crate::ir::expr::{Block, BlockTail, Expr};
use crate::ir::function::{FunctionKind, SpecKind};
use crate::ir::ty::Type;
use crate::ir::validate::{validate_program, ValidationError};
use crate::ir::visit::{walk_expr_default, walk_tail_default, Visitor};
use crate::ir::{FunId, Program};

use super::option_aborts::{
    is_abort_result_type, ABORT_CODE_QUALIFIED_NAME, OPTION_QUALIFIED_NAME,
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PostconditionError {
    /// Base IR validation failed.
    BaseValidator(ValidationError),
    /// A function-tail `BlockTail::Return(_)` survived in a
    /// non-helper body. Phase 2's return-collapse should have
    /// converted it to `Value(_)`.
    LingeringFunctionTailReturn { function: FunId },
    /// A nested `BlockTail::Return(_)` survived return lifting. The
    /// renderer cannot preserve its early-exit semantics.
    LingeringInnerReturn { function: FunId },
    /// `BlockTail::Break` or `Continue` survived. Phase 2's loop
    /// extraction should have rewritten them to tail-Calls.
    LingeringBreakOrContinue { function: FunId },
    /// A labeled-block return survived extraction.
    LingeringReturnFromBlock { function: FunId },
    /// A labeled block survived extraction.
    LingeringLabeledBlock { function: FunId },
    /// `BlockTail::Abort` survived. Phase 1's `.aborts` materialiser
    /// rewrites every Abort to `Return(Some(code))` in the cloned
    /// body; phase 2 collapses function-tail Returns to Values.
    /// (Source bodies CAN still have Aborts -- phase 1 doesn't
    /// touch them; the .aborts variant is the only place where
    /// abort info gets lifted into `Option`.)
    LingeringAbortInAbortsBody { function: FunId },
    /// `Expr::While` survived phase 2's loop extraction.
    LingeringWhile { function: FunId },
    /// A `Call(prover::*_id, ..)` survived. Phase 1's
    /// `spec_companion::collect_predicates` should have extracted
    /// and removed every such call.
    LingeringSpecCall { function: FunId },
    /// A Source function has no `Spec(Aborts) { target: f }`
    /// companion.
    MissingAbortsCompanion { source: FunId },
    /// A `Spec(Aborts)` companion's return type isn't the canonical
    /// `Option<MoveAbortCode>` shape.
    AbortsReturnTypeMismatch { variant: FunId },
    /// A function in the `.aborts` FAMILY whose return type is not the
    /// canonical `AbortResult` still calls a function that HAS an
    /// `.aborts` companion -- so that callee's abort face is silently
    /// dropped.
    ///
    /// This is the misfiled-value-chain shape: a VALUE loop shipped
    /// under an `.aborts.` name because the retype+splice pass declined.
    /// The pass matches only when the dead `let` is the last top-level
    /// statement of the `Spec(Aborts)` body, so an abortable callee
    /// BEFORE the labeled block pushes it into a spliced guard arm and
    /// the match is missed. Measured at 13 clusters / 40 defs in
    /// sui-system, with the residue named (unactioned) in
    /// `aborts_variant.rs`'s own doc comment.
    ///
    /// See `plans/lean-pipeline/stage-07-aborts-labeled-loop-followup.md`.
    MisfiledAbortsFamilyValueChain {
        function: FunId,
        dropped_callee: FunId,
    },
}

/// Run base validation plus the stage-7-rewrite structural checks.
pub fn check(program: &Program, prover_ids: &ProverFnIds) -> Result<(), PostconditionError> {
    for (fid, function) in &program.functions {
        let control = classify_control_flow(&function.body);
        let permits_function_tail_return = matches!(
            function.kind,
            FunctionKind::LoopBody { .. }
                | FunctionKind::LoopAfter { .. }
                | FunctionKind::Spec {
                    kind: SpecKind::Requires | SpecKind::Ensures,
                    ..
                }
        );
        if control.function_tail_return && !permits_function_tail_return {
            return Err(PostconditionError::LingeringFunctionTailReturn { function: *fid });
        }
        if control.residual_inner_returns > 0 {
            return Err(PostconditionError::LingeringInnerReturn { function: *fid });
        }
        if control.breaks > 0 || control.continues > 0 {
            return Err(PostconditionError::LingeringBreakOrContinue { function: *fid });
        }
        if control.return_from_blocks > 0 {
            return Err(PostconditionError::LingeringReturnFromBlock { function: *fid });
        }
        if control.labeled_blocks > 0 {
            return Err(PostconditionError::LingeringLabeledBlock { function: *fid });
        }
    }

    validate_program(program).map_err(PostconditionError::BaseValidator)?;

    // Resolve the canonical Option<MoveAbortCode> Struct ids.
    let option_id = program.struct_id_by_qualified_name(OPTION_QUALIFIED_NAME);
    let abort_code_id = program.struct_id_by_qualified_name(ABORT_CODE_QUALIFIED_NAME);

    let mut sources_seen: std::collections::BTreeSet<FunId> = std::collections::BTreeSet::new();
    let mut aborts_targets: std::collections::BTreeSet<FunId> = std::collections::BTreeSet::new();

    for (fid, f) in &program.functions {
        let is_aborts_companion = matches!(
            f.kind,
            FunctionKind::Spec {
                kind: SpecKind::Aborts,
                ..
            }
        );
        if matches!(f.kind, FunctionKind::Source) {
            sources_seen.insert(*fid);
        }
        if let FunctionKind::Spec {
            kind: SpecKind::Aborts,
            target,
        } = f.kind
        {
            aborts_targets.insert(target);
            // Verify the variant's return type is Option<MoveAbortCode>.
            if !is_canonical_aborts_return_type(&f.signature.return_type, option_id, abort_code_id)
            {
                return Err(PostconditionError::AbortsReturnTypeMismatch { variant: *fid });
            }
        }

        let signals = scan_body(&f.body, prover_ids);

        if is_aborts_companion && signals.has_abort {
            return Err(PostconditionError::LingeringAbortInAbortsBody { function: *fid });
        }

        if signals.has_while {
            return Err(PostconditionError::LingeringWhile { function: *fid });
        }

        if signals.has_spec_call {
            return Err(PostconditionError::LingeringSpecCall { function: *fid });
        }
    }

    // Every Source function must have a paired Spec(Aborts).
    for source in &sources_seen {
        if !aborts_targets.contains(source) {
            return Err(PostconditionError::MissingAbortsCompanion { source: *source });
        }
    }

    // No misfiled value chain under an `.aborts.` name.
    //
    // `aborts_targets` IS the abort-map key set -- a function appears
    // there exactly when something must splice its abort face -- so no
    // map needs threading here.
    //
    // A member of the `.aborts` family that does not return AbortResult
    // is either a legitimate loop-step inductive (exempted below) or a
    // value chain that was never retyped, in which case every abortable
    // callee it reaches has had its face dropped.
    for (fid, f) in &program.functions {
        if !crate::ir::names::is_aborts_family_name(&f.name) {
            continue;
        }
        if is_canonical_aborts_return_type(&f.signature.return_type, option_id, abort_code_id) {
            continue;
        }
        if returns_loop_step(program, &f.signature.return_type) {
            continue;
        }
        for callee in collect_callees(&f.body) {
            if aborts_targets.contains(&callee)
                && super::aborts_variant::callee_can_abort(program, callee)
            {
                return Err(PostconditionError::MisfiledAbortsFamilyValueChain {
                    function: *fid,
                    dropped_callee: callee,
                });
            }
        }
    }

    Ok(())
}

/// True when `t` is one of `aborts_defunctionalize`'s synthesised
/// `cont | done` loop-step inductives. Those are the one legitimate
/// non-`AbortResult` return inside the `.aborts` family.
fn returns_loop_step(program: &Program, t: &Type) -> bool {
    let Type::Struct { struct_id, .. } = t else {
        return false;
    };
    program
        .structs
        .get(struct_id)
        .map_or(false, super::aborts_defunctionalize::is_loop_step_struct)
}

pub(super) fn collect_callees(b: &Block) -> std::collections::BTreeSet<FunId> {
    struct Calls {
        out: std::collections::BTreeSet<FunId>,
    }
    impl Visitor for Calls {
        fn visit_expr(&mut self, e: &Expr) {
            if let Expr::Call { fun, .. } = e {
                self.out.insert(*fun);
            }
            walk_expr_default(self, e);
        }
    }
    let mut c = Calls {
        out: std::collections::BTreeSet::new(),
    };
    c.visit_block(b);
    c.out
}

/// Verify `t` is `Type::Struct { struct_id: option_id, type_args:
/// [Type::Struct { struct_id: abort_code_id, .. }] }`.
fn is_canonical_aborts_return_type(
    t: &Type,
    option_id: Option<crate::ir::StructId>,
    abort_code_id: Option<crate::ir::StructId>,
) -> bool {
    let (Some(opt_id), Some(ac_id)) = (option_id, abort_code_id) else {
        return false;
    };
    is_abort_result_type(t, opt_id, ac_id)
}

// ---------------------------------------------------------------------------
// Body scan
// ---------------------------------------------------------------------------

#[derive(Default, Debug, Clone, Copy)]
struct Signals {
    has_abort: bool,
    has_while: bool,
    has_spec_call: bool,
}

fn scan_body(b: &Block, ids: &ProverFnIds) -> Signals {
    let mut scan = Scan {
        ids,
        out: Signals::default(),
    };
    scan.visit_block(b);
    scan.out
}

struct Scan<'a> {
    ids: &'a ProverFnIds,
    out: Signals,
}

impl Visitor for Scan<'_> {
    fn visit_expr(&mut self, e: &Expr) {
        match e {
            Expr::While { .. } => self.out.has_while = true,
            Expr::Call { fun, .. } if is_prover_call(*fun, self.ids) => {
                self.out.has_spec_call = true
            }
            _ => {}
        }
        walk_expr_default(self, e);
    }

    fn visit_tail(&mut self, t: &BlockTail) {
        if matches!(t, BlockTail::Abort { .. }) {
            self.out.has_abort = true;
        }
        walk_tail_default(self, t);
    }
}

/// Control-flow forms that survive at the stage-7 boundary.
///
/// Return lifting can leave inner Returns in place when it declines a
/// potentially unsafe transformation. The strict postcondition rejects that
/// residual class because rendering cannot preserve its early-exit semantics.
#[derive(Default, Debug, Clone, Copy, PartialEq, Eq)]
pub struct PostStage7ControlFlow {
    pub function_tail_return: bool,
    pub residual_inner_returns: usize,
    pub breaks: usize,
    pub continues: usize,
    pub return_from_blocks: usize,
    pub labeled_blocks: usize,
}

/// Classify control-flow forms. The postcondition rejects every nonzero count;
/// `function_tail_return` has the documented helper/spec exceptions.
pub fn classify_control_flow(block: &Block) -> PostStage7ControlFlow {
    #[derive(Default)]
    struct ControlScan {
        returns: usize,
        out: PostStage7ControlFlow,
    }

    impl Visitor for ControlScan {
        fn visit_expr(&mut self, expr: &Expr) {
            if matches!(expr, Expr::LabeledBlock { .. }) {
                self.out.labeled_blocks += 1;
            }
            walk_expr_default(self, expr);
        }

        fn visit_tail(&mut self, tail: &BlockTail) {
            match tail {
                BlockTail::Return(_) => self.returns += 1,
                BlockTail::Break { .. } => self.out.breaks += 1,
                BlockTail::Continue { .. } => self.out.continues += 1,
                BlockTail::ReturnFromBlock { .. } => self.out.return_from_blocks += 1,
                BlockTail::Value(_) | BlockTail::Abort { .. } => {}
            }
            walk_tail_default(self, tail);
        }
    }

    let function_tail_return = matches!(block.tail, BlockTail::Return(_));
    let mut scan = ControlScan::default();
    scan.visit_block(block);
    scan.out.function_tail_return = function_tail_return;
    scan.out.residual_inner_returns = scan.returns - usize::from(function_tail_return);
    scan.out
}

fn is_prover_call(fun: FunId, ids: &ProverFnIds) -> bool {
    Some(fun) == ids.requires || Some(fun) == ids.ensures || Some(fun) == ids.asserts
}
