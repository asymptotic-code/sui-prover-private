//! Stage-5 (SSA) postcondition.
//!
//! Checks beyond the base IR validator:
//!
//! 1. **No shadowing.** Every `VarId` binding (function param,
//!    `Stmt::Let` pattern, `MatchArm::bindings`, `Quantifier::binder`)
//!    is unique within a function. This is the SSA invariant.
//! 2. **Break/Continue arity.** Every `BlockTail::Break` /
//!    `BlockTail::Continue { level: k, value }` carries a payload
//!    whose arity matches `iter_locals.len()` of the target `While`
//!    (resolved by walking up `level + 1` enclosing `While`s).
//! 3. **Body-tail arity.** A `While` body's value-tailed implicit
//!    continue leaves have arity matching `iter_locals.len()`. A
//!    top-level `Value(if ... { continue } else { continue })` is not
//!    itself a scalar implicit continue; the branch tails decide
//!    whether control falls through. Bodies whose reachable tail
//!    leaves are terminators (Break / Return / Abort) are exempt --
//!    the loop doesn't fall through on those paths.
//!
//! See `plans/lean-pipeline/stage-05-ssa.md` "Output invariants".

use std::collections::BTreeSet;

use crate::ir::visit::{walk_expr_default, walk_tail_default, Visitor};
use crate::ir::{
    expr::{Block, BlockTail},
    validate::{validate_program, ValidationError},
    Expr, FunId, MatchArm, Program, Stmt, VarId,
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PostconditionError {
    BaseValidator(ValidationError),
    /// A `VarId` was bound twice within the same function. Stage 5's
    /// alpha-rename should have made every binding fresh.
    Shadowing {
        function: FunId,
        var: VarId,
    },
    /// A `BlockTail::Break` / `Continue { level, value }` payload
    /// has arity that doesn't match the target `While`'s
    /// `iter_locals.len()`.
    JumpArityMismatch {
        function: FunId,
        level: u32,
        expected: usize,
        actual: usize,
    },
    /// A `While` body's top-level `BlockTail::Value(V)` has arity
    /// that doesn't match the enclosing `While`'s
    /// `iter_locals.len()`.
    BodyTailArityMismatch {
        function: FunId,
        expected: usize,
        actual: usize,
    },
    /// A `BlockTail::Break` / `Continue { level }` referenced a
    /// `level` deeper than the enclosing `While` nesting. The base
    /// validator catches this generically (`JumpLevelOutOfBounds`);
    /// this variant exists for completeness when the postcondition
    /// is run in isolation.
    JumpLevelOutOfBounds {
        function: FunId,
        level: u32,
        depth: usize,
    },
    /// An `Expr::ReadRef(inner)` whose `inner` types to a value
    /// (non-reference) type. Stage 7's scope build (`type_of`) panics
    /// on this shape (`ReadRef of non-reference type ...`). Its usual
    /// source is a pre-SSA `ReadRef` wrapped over a var whose defs
    /// merge into a mixed-type phi -- see the `NormalizeMode::Early`
    /// guard in `stage_02_ir_cfg::pipeline`.
    ReadRefOverValue {
        function: FunId,
        detail: String,
    },
}

impl From<ValidationError> for PostconditionError {
    fn from(e: ValidationError) -> Self {
        PostconditionError::BaseValidator(e)
    }
}

/// Run all stage-5 postcondition checks.
pub fn check(program: &Program) -> Result<(), PostconditionError> {
    validate_program(program)?;
    for (&fid, func) in &program.functions {
        // No-shadowing applies to functions stage 5 actually walked
        // (Source / Test). Stage 7 synthesizes Spec (aborts /
        // requires / ensures), LoopBody, and LoopAfter helpers from
        // source bodies AFTER stage 5 has run. Those synthesized
        // bodies compose snippets from the source in ways that can
        // legitimately produce duplicate SSA names (e.g.
        // `make_self_contained_aborts_body` lifts inner Lets to the
        // outer scope of the aborts body while their original
        // `Let { ... }` shape stays embedded in the source `If`
        // expression that's also copied into the predicate). The
        // duplicates rebind to the same value in both positions, so
        // they're harmless to render (Lean accepts shadowing in
        // `let`-chains) but they would falsely fail the
        // strict-SSA invariant if we checked them here. The
        // Synthetic kind catches stage-2-prelude and stage-10
        // generated thunks; nothing rebinds vars in those, but
        // skipping is the safe default.
        let is_post_stage5_synthetic = matches!(
            func.kind,
            crate::ir::FunctionKind::Spec { .. }
                | crate::ir::FunctionKind::LoopBody { .. }
                | crate::ir::FunctionKind::LoopAfter { .. }
                | crate::ir::FunctionKind::Synthetic,
        );
        if !is_post_stage5_synthetic {
            // Pass 1: no-shadowing.
            let mut seen: BTreeSet<VarId> = BTreeSet::new();
            for p in &func.signature.params {
                if !seen.insert(p.var.clone()) {
                    return Err(PostconditionError::Shadowing {
                        function: fid,
                        var: p.var.clone(),
                    });
                }
            }
            check_block_no_shadow(fid, &func.body, &mut seen)?;
        }
        // Pass 2: Break/Continue/body-tail arity.
        check_block_arity(fid, &func.body, &[])?;
    }
    Ok(())
}

/// Arity of a tail-position value expression.
/// Single value -> 1; explicit `Tuple([..])` -> its length; `Unit` -> 0.
fn arity_of_value(e: &Expr) -> usize {
    match e {
        Expr::Tuple(elems) => elems.len(),
        Expr::Unit => 0,
        _ => 1,
    }
}

/// Validates Break/Continue arity and While body-tail arity against the
/// stack of enclosing `While::iter_locals` lengths (innermost last). The
/// `loops` stack is pushed on `While` entry; `iter_locals` init exprs are
/// checked in the OUTER (pre-loop) scope before the push.
struct ArityCheck {
    fid: FunId,
    loops: Vec<usize>,
    err: Option<PostconditionError>,
}

impl Visitor for ArityCheck {
    fn visit_tail(&mut self, t: &BlockTail) {
        if self.err.is_some() {
            return;
        }
        match t {
            BlockTail::Break { level, value } | BlockTail::Continue { level, value } => {
                let depth = self.loops.len();
                if (*level as usize) >= depth {
                    self.err = Some(PostconditionError::JumpLevelOutOfBounds {
                        function: self.fid,
                        level: *level,
                        depth,
                    });
                    return;
                }
                let expected = self.loops[depth - 1 - (*level as usize)];
                let actual = arity_of_value(value);
                if expected != actual {
                    self.err = Some(PostconditionError::JumpArityMismatch {
                        function: self.fid,
                        level: *level,
                        expected,
                        actual,
                    });
                    return;
                }
                self.visit_expr(value);
            }
            _ => walk_tail_default(self, t),
        }
    }

    fn visit_expr(&mut self, e: &Expr) {
        if self.err.is_some() {
            return;
        }
        match e {
            Expr::While {
                header,
                cond,
                body,
                iter_locals,
                ..
            } => {
                // Init exprs evaluate in outer (pre-loop) scope.
                for (_, init) in iter_locals {
                    self.visit_expr(init);
                    if self.err.is_some() {
                        return;
                    }
                }
                self.loops.push(iter_locals.len());
                self.visit_block(header);
                self.visit_expr(cond);
                self.visit_block(body);
                // Body-tail arity: every implicit-continue value leaf
                // must match the enclosing `iter_locals.len()`.
                if self.err.is_none() {
                    if let BlockTail::Value(v) = &body.tail {
                        let expected = iter_locals.len();
                        self.err = check_implicit_continue_value_arity(self.fid, v, expected);
                    }
                }
                self.loops.pop();
            }
            _ => walk_expr_default(self, e),
        }
    }
}

fn check_block_arity(fid: FunId, block: &Block, loops: &[usize]) -> Result<(), PostconditionError> {
    let mut v = ArityCheck {
        fid,
        loops: loops.to_vec(),
        err: None,
    };
    v.visit_block(block);
    match v.err {
        Some(e) => Err(e),
        None => Ok(()),
    }
}

fn check_implicit_continue_block_arity(
    fid: FunId,
    block: &Block,
    expected: usize,
) -> Option<PostconditionError> {
    match &block.tail {
        BlockTail::Value(e) => check_implicit_continue_value_arity(fid, e, expected),
        _ => None,
    }
}

fn check_implicit_continue_value_arity(
    fid: FunId,
    value: &Expr,
    expected: usize,
) -> Option<PostconditionError> {
    match value {
        Expr::If {
            then_branch,
            else_branch,
            ..
        } => check_implicit_continue_block_arity(fid, then_branch, expected)
            .or_else(|| check_implicit_continue_block_arity(fid, else_branch, expected)),
        Expr::Match { cases, .. } => cases
            .iter()
            .find_map(|case| check_implicit_continue_block_arity(fid, &case.body, expected)),
        _ => {
            let actual = arity_of_value(value);
            (expected != actual).then_some(PostconditionError::BodyTailArityMismatch {
                function: fid,
                expected,
                actual,
            })
        }
    }
}

/// Enforces the SSA no-shadowing invariant: every binder (`Stmt::Let`
/// pattern slot, `MatchArm::bindings`, `Quantifier::binder`) is unique
/// within the function. `seen` is pre-seeded with the function params by
/// the caller. `While::iter_locals` binders are intentionally not
/// checked here -- they are fresh by construction and were excluded by
/// the pre-refactor checker.
struct NoShadow<'a> {
    fid: FunId,
    seen: &'a mut BTreeSet<VarId>,
    err: Option<PostconditionError>,
}

impl NoShadow<'_> {
    fn bind(&mut self, v: &VarId) {
        if self.err.is_none() && !self.seen.insert(v.clone()) {
            self.err = Some(PostconditionError::Shadowing {
                function: self.fid,
                var: v.clone(),
            });
        }
    }
}

impl Visitor for NoShadow<'_> {
    fn visit_stmt(&mut self, s: &Stmt) {
        if self.err.is_some() {
            return;
        }
        match s {
            Stmt::Let { pattern, value } => {
                // Value is evaluated before the pattern binders come into
                // scope; check it first.
                self.visit_expr(value);
                for slot in pattern.iter().flatten() {
                    self.bind(slot);
                    if self.err.is_some() {
                        return;
                    }
                }
            }
            Stmt::Eval(e) => self.visit_expr(e),
        }
    }

    fn visit_match_arm(&mut self, arm: &MatchArm) {
        if self.err.is_some() {
            return;
        }
        for b in &arm.bindings {
            self.bind(b);
            if self.err.is_some() {
                return;
            }
        }
        self.visit_block(&arm.body);
    }

    fn visit_expr(&mut self, e: &Expr) {
        if self.err.is_some() {
            return;
        }
        match e {
            Expr::Quantifier {
                binder,
                domain,
                body,
                ..
            } => {
                // Domain is evaluated in outer scope; binder is bound for
                // the body only.
                match domain {
                    crate::ir::QuantDomain::Unbounded => {}
                    crate::ir::QuantDomain::Range { start, end } => {
                        self.visit_expr(start);
                        self.visit_expr(end);
                    }
                    crate::ir::QuantDomain::Collection(c) => self.visit_expr(c),
                    crate::ir::QuantDomain::VecRange { vec, start, end } => {
                        self.visit_expr(vec);
                        self.visit_expr(start);
                        self.visit_expr(end);
                    }
                }
                self.bind(binder);
                if self.err.is_some() {
                    return;
                }
                self.visit_block(body);
            }
            _ => walk_expr_default(self, e),
        }
    }
}

fn check_block_no_shadow(
    fid: FunId,
    block: &Block,
    seen: &mut BTreeSet<VarId>,
) -> Result<(), PostconditionError> {
    let mut v = NoShadow {
        fid,
        seen,
        err: None,
    };
    v.visit_block(block);
    match v.err {
        Some(e) => Err(e),
        None => Ok(()),
    }
}

/// Every `Expr::ReadRef(inner)` in every function has an `inner`
/// whose `type_of` is a `Reference` / `MutableRef` (or is
/// undeterminable). A `ReadRef` over a value type is malformed IR:
/// stage 7's `type_of`-based scope build panics with
/// `ReadRef of non-reference type ...`.
///
/// Kept OUT of [`check`] on purpose. `check` is wrapped by the
/// render-held `Stage05SsaPostcondition` invariant umbrella; a
/// `ReadRef` shape that some later stage legitimately transforms
/// could then false-fire at render on the transformed IR (the
/// stage-N-postcondition-on-transformed-IR trap). This check is
/// stage-5-only -- called directly from `stage_05_ssa::run`'s debug
/// self-check and registered as the stage-5-lifespan
/// `stage-05-readref-inner-is-reference` invariant.
///
/// The framework version collects EVERY finding; this returns the
/// first as a single `PostconditionError`.
pub fn check_readref_inner_is_reference(program: &Program) -> Result<(), PostconditionError> {
    match readref_over_value_findings(program).into_iter().next() {
        None => Ok(()),
        Some((function, detail)) => Err(PostconditionError::ReadRefOverValue { function, detail }),
    }
}

/// Collect `(fid, detail)` for every `Expr::ReadRef(inner)` whose
/// `inner` types to a value. `type_of` failures are ignored (the
/// shape can't be judged) and a `Tuple([_])` singleton is unwrapped
/// first, mirroring `type_of`'s own `ReadRef` handling of a
/// mut-augmented call returning a 1-tuple.
pub(crate) fn readref_over_value_findings(program: &Program) -> Vec<(FunId, String)> {
    use crate::ir::analysis::scope::{walk_typed_block, TypedScope, TypedScopeVisitor};
    use crate::ir::analysis::type_of::{type_of, TypeOfError};
    use crate::ir::ty::Type;

    struct Walker<'a> {
        program: &'a Program,
        fid: FunId,
        findings: Vec<(FunId, String)>,
    }

    impl TypedScopeVisitor for Walker<'_> {
        type Error = TypeOfError;

        fn visit_expr(&mut self, e: &Expr, scope: &TypedScope) -> Result<(), TypeOfError> {
            if let Expr::ReadRef(inner) = e {
                if let Ok(inner_ty) = type_of(inner, scope, self.program) {
                    let inner_ty = match inner_ty {
                        Type::Tuple(items) if items.len() == 1 => items.into_iter().next().unwrap(),
                        other => other,
                    };
                    if !matches!(inner_ty, Type::Reference(_) | Type::MutableRef { .. }) {
                        self.findings.push((
                            self.fid,
                            format!("ReadRef inner types to non-reference {inner_ty:?}"),
                        ));
                    }
                }
            }
            Ok(())
        }
    }

    let mut out = Vec::new();
    for (&fid, func) in &program.functions {
        let scope: TypedScope = func
            .signature
            .params
            .iter()
            .map(|p| (p.var.clone(), p.ty.clone()))
            .collect();
        let mut w = Walker {
            program,
            fid,
            findings: Vec::new(),
        };
        // A `type_of` failure while building scope stops the walk for
        // this function (partial coverage). Findings recorded before
        // the stop used a valid incremental scope, so they stand.
        let _ = walk_typed_block(&mut w, &func.body, scope, program);
        out.extend(w.findings);
    }
    out
}
