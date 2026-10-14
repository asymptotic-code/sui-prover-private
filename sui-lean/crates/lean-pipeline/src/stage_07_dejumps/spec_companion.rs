//! Phases 1 + 4 -- collect spec predicates and emit `.requires` /
//! `.ensures` companions.
//!
//! See `plans/lean-pipeline/stage-07-rewrite.md` for the design.
//!
//! ## Phase 1: `collect_predicates`
//!
//! Walks every processable function body and:
//! 1. For each `Stmt::Eval(Call(prover::requires_id | ensures_id |
//!    asserts_id, [p]))`: appends `p` to the matching predicate list
//!    and removes the stmt from the body.
//! 2. Rejects `Stmt::Let { value: Call(prover::*, ..) }` and any
//!    sub-expression-position `Expr::Call(prover::*, ..)` with
//!    `Stage7Error::SpecCallInValuePosition` (the predicates only
//!    make sense as Eval'd top-level intrinsics).
//!
//! Returns `BTreeMap<FunId, Predicates>` for downstream consumption:
//! - `.aborts` materialiser uses `asserts` to inject synthetic abort
//!   guards.
//! - `.requires` / `.ensures` emitter uses the matching predicate
//!   lists.
//!
//! ## Phase 4: `emit_requires_ensures`
//!
//! For each function with non-empty `requires`, emits a sibling
//! `<f>.requires` of `FunctionKind::Spec { Requires, target: f }`
//! with `body = conjoin_all(requires)` and `return_type = Prop`.
//!
//! For each function with non-empty `ensures`, emits a sibling
//! `<f>.ensures` of `FunctionKind::Spec { Ensures, target: f }` with
//! the extra `result: f.return_type` param at the end.
//!
//! Note: `prover::asserts` does NOT emit its own companion. The
//! `.aborts` variant absorbs each `asserts(p)` as a synthetic abort
//! guard during phase 2's materialisation.

use std::collections::{BTreeMap, BTreeSet};

use crate::ir::builder::ProverFnIds;
use crate::ir::expr::{Block, BlockTail, Expr, MatchArm, Stmt};
use crate::ir::function::{Function, FunctionKind, Param, SpecKind};
use crate::ir::ty::Type;
use crate::ir::visit::{walk_expr_mut_try, TryMutVisitor};
use crate::ir::{FunId, Program};

use super::aborts_variant::AbortsMap;
use super::{make_spec_companion, Stage7Error};

/// Collected spec predicates for one function.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Predicates {
    pub requires: Vec<Expr>,
    pub ensures: Vec<Expr>,
    pub asserts: Vec<Expr>,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum SpecKindLite {
    Requires,
    Ensures,
    Asserts,
}

// ---------------------------------------------------------------------------
// Phase 1: predicate collection
// ---------------------------------------------------------------------------

/// Walk every processable function body, collect predicate exprs
/// from `Stmt::Eval(Call(prover::*_id, [p]))` sites, remove the stmts
/// in place.
///
/// Skips:
/// - native / vendor functions (already have their `.aborts` natives
///   registered),
/// - `LoopBody` / `LoopAfter` helpers (no spec calls expected),
/// - functions that already have a `Spec(Aborts) { target: f }`
///   companion (idempotency).
pub fn collect_predicates(
    program: &mut Program,
    ids: &ProverFnIds,
) -> Result<BTreeMap<FunId, Predicates>, Stage7Error> {
    let already_processed: BTreeSet<FunId> = program
        .functions
        .values()
        .filter_map(|f| match f.kind {
            FunctionKind::Spec { target, .. } => Some(target),
            _ => None,
        })
        .collect();

    let processable_fids: Vec<FunId> = program
        .functions
        .iter()
        .filter_map(|(fid, f)| {
            if already_processed.contains(fid) {
                return None;
            }
            match f.kind {
                FunctionKind::Source | FunctionKind::Test { .. } => Some(*fid),
                _ => None,
            }
        })
        .collect();

    let mut out: BTreeMap<FunId, Predicates> = BTreeMap::new();
    for fid in processable_fids {
        let f = program.functions.get_mut(&fid).expect("fid present");
        // Detach body so we can mutate it without holding a borrow on
        // `program`. Restore at the end.
        let placeholder = Block {
            stmts: Vec::new(),
            tail: BlockTail::Value(Expr::Unit),
        };
        let mut body = std::mem::replace(&mut f.body, placeholder);
        let mut preds = Predicates::default();
        PredicateCollector {
            ids,
            out: &mut preds,
        }
        .visit_block_mut(&mut body)?;
        let f = program.functions.get_mut(&fid).expect("fid present");
        f.body = body;
        if !is_empty(&preds) {
            out.insert(fid, preds);
        }
    }
    Ok(out)
}

fn is_empty(p: &Predicates) -> bool {
    p.requires.is_empty() && p.ensures.is_empty() && p.asserts.is_empty()
}

fn matches_prover(fun: FunId, ids: &ProverFnIds) -> Option<SpecKindLite> {
    if Some(fun) == ids.requires {
        Some(SpecKindLite::Requires)
    } else if Some(fun) == ids.ensures {
        Some(SpecKindLite::Ensures)
    } else if Some(fun) == ids.asserts {
        Some(SpecKindLite::Asserts)
    } else {
        None
    }
}

fn push_pred(out: &mut Predicates, kind: SpecKindLite, p: Expr) {
    match kind {
        SpecKindLite::Requires => out.requires.push(p),
        SpecKindLite::Ensures => out.ensures.push(p),
        SpecKindLite::Asserts => out.asserts.push(p),
    }
}

/// Strips `prover::{requires,ensures,asserts}(p)` evals out of a body in
/// place, collecting each `p` into `out` under the matching kind. A
/// `prover::*` call reached in any non-top-level-`Eval` position (a let
/// value, a call arg, ...) is rejected with `SpecCallInValuePosition` --
/// the intrinsics only make sense as eval'd top-level statements.
struct PredicateCollector<'a> {
    ids: &'a ProverFnIds,
    out: &'a mut Predicates,
}

impl TryMutVisitor for PredicateCollector<'_> {
    type Error = Stage7Error;

    fn visit_block_mut(&mut self, b: &mut Block) -> Result<(), Stage7Error> {
        let mut i = 0;
        while i < b.stmts.len() {
            // A top-level `Stmt::Eval(prover::<kind>(p))` is collected and
            // removed in place; everything else is recursed into.
            let collected = match &b.stmts[i] {
                Stmt::Eval(Expr::Call { fun, args, .. }) => match matches_prover(*fun, self.ids) {
                    Some(kind) => {
                        if args.len() != 1 {
                            return Err(Stage7Error::SpecCallInValuePosition);
                        }
                        Some((kind, args[0].clone()))
                    }
                    None => None,
                },
                _ => None,
            };
            match collected {
                Some((kind, p)) => {
                    push_pred(self.out, kind, p);
                    b.stmts.remove(i);
                }
                None => {
                    self.visit_stmt_mut(&mut b.stmts[i])?;
                    i += 1;
                }
            }
        }
        self.visit_tail_mut(&mut b.tail)
    }

    fn visit_expr_mut(&mut self, e: &mut Expr) -> Result<(), Stage7Error> {
        // Reaching a `prover::*` call here means it sits in a value
        // position (top-level evals are stripped in `visit_block_mut`).
        if let Expr::Call { fun, .. } = e {
            if matches_prover(*fun, self.ids).is_some() {
                return Err(Stage7Error::SpecCallInValuePosition);
            }
        }
        walk_expr_mut_try(self, e)
    }
}

// ---------------------------------------------------------------------------
// Phase 4: emit .requires / .ensures companions
// ---------------------------------------------------------------------------

/// Emit `<f>.requires` and `<f>.ensures` siblings from collected
/// predicates. Skips functions whose `requires` / `ensures` lists are
/// empty.
///
/// Each companion body is rebuilt STRUCTURALLY from `pre_strip_bodies`
/// (the source body snapshot taken before `collect_predicates` stripped
/// the `prover::*` calls), so branch-distributed predicates keep their
/// guards: `if c { ensures!(A) } else { ensures!(B) }` becomes
/// `if c then A else B`, not the over-constrained flat `A && B`. See
/// `build_pred_body`.
pub fn emit_requires_ensures(
    program: &mut Program,
    predicates: &BTreeMap<FunId, Predicates>,
    pre_strip_bodies: &BTreeMap<FunId, Block>,
    ids: &ProverFnIds,
    _aborts_map: &AbortsMap,
) -> Result<(), Stage7Error> {
    let mut next_fid = program.next_function_id();
    for (&target_fid, preds) in predicates {
        let target = program
            .functions
            .get(&target_fid)
            .expect("target fid present")
            .clone();
        // The pre-strip snapshot still carries the `prover::*` calls in
        // their guard structure; every `predicates` key is a processable
        // Source/Test fid, which is exactly the set snapshotted in
        // `stage_07_dejumps::run`.
        let src = pre_strip_bodies
            .get(&target_fid)
            .expect("pre-strip body present for predicate target");

        // One companion per non-empty predicate list. Only `.ensures`
        // carries the trailing `result` param. (`.asserts` is ALSO folded
        // into `.aborts` by aborts_variant; this standalone Bool companion
        // is what the stage-12 theorems reference.)
        for (lite, kind, list, add_result) in [
            (
                SpecKindLite::Requires,
                SpecKind::Requires,
                &preds.requires,
                false,
            ),
            (
                SpecKindLite::Asserts,
                SpecKind::Asserts,
                &preds.asserts,
                false,
            ),
            (
                SpecKindLite::Ensures,
                SpecKind::Ensures,
                &preds.ensures,
                true,
            ),
        ] {
            if list.is_empty() {
                continue;
            }
            let fid = next_fid;
            next_fid += 1;
            let body = build_pred_body(src, lite, ids, list.len())?;
            program.functions.insert(
                fid,
                build_companion(&target, target_fid, kind, body, add_result),
            );
        }
    }
    Ok(())
}

/// Build a companion body of `kind` by mirroring `src`'s control flow:
/// each block contributes the conjunction of its direct `prover::<kind>`
/// args; an `if`/`match` contributes an `if`/`match` whose branches are
/// the branches' contributions (a branch with no predicate of `kind`
/// contributes `true`, so `if c { ensures!(A) }` -> `if c then A else
/// true` == `c -> A`); `Stmt::Let`s are kept in place as scaffolding
/// (with any `prover::*` calls stripped from their value) so predicate
/// var refs resolve without a flat prelude. `expected` is the flat count
/// of `kind` predicates collected from the whole body; if the structural
/// pass reproduces fewer, a predicate sits somewhere it can't (loop /
/// quantifier body) and we fail loudly rather than silently drop it.
fn build_pred_body(
    src: &Block,
    kind: SpecKindLite,
    ids: &ProverFnIds,
    expected: usize,
) -> Result<Block, Stage7Error> {
    let mut consumed = 0usize;
    let (stmts, contribs) = collect_struct(src, kind, ids, &mut consumed)?;
    if consumed != expected {
        return Err(Stage7Error::SpecPredicateUnreachable);
    }
    Ok(Block {
        stmts,
        tail: BlockTail::Value(conjoin(&contribs)),
    })
}

/// Walk `b`'s statements + tail, returning (scaffolding lets to retain,
/// predicate contributions of `kind` in source order). `consumed` counts
/// each `prover::<kind>` leaf reproduced.
fn collect_struct(
    b: &Block,
    kind: SpecKindLite,
    ids: &ProverFnIds,
    consumed: &mut usize,
) -> Result<(Vec<Stmt>, Vec<Expr>), Stage7Error> {
    let mut retained: Vec<Stmt> = Vec::new();
    let mut contribs: Vec<Expr> = Vec::new();
    for s in &b.stmts {
        match s {
            Stmt::Eval(Expr::Call { fun, args, .. }) if matches_prover(*fun, ids) == Some(kind) => {
                if args.len() != 1 {
                    return Err(Stage7Error::SpecCallInValuePosition);
                }
                *consumed += 1;
                contribs.push(args[0].clone());
            }
            Stmt::Eval(e @ (Expr::If { .. } | Expr::Match { .. })) => {
                if let Some(c) = expr_contribution(e, kind, ids, consumed)? {
                    contribs.push(c);
                }
            }
            // Everything else evaluated for effect -- a `prover::*` of a
            // different kind (belongs to another companion) or a pure
            // side-effect stmt -- contributes nothing to this companion.
            Stmt::Eval(_) => {}
            Stmt::Let { pattern, value } => {
                // A predicate nested in the let's value (an `if`/`match`)
                // still contributes structurally...
                if let Some(c) = expr_contribution(value, kind, ids, consumed)? {
                    contribs.push(c);
                }
                // ...and the let is retained as scaffolding, but with ALL
                // `prover::*` calls stripped from its value so no spec
                // call leaks into the (pure) companion body.
                let mut cleaned = value.clone();
                let mut throwaway = Predicates::default();
                PredicateCollector {
                    ids,
                    out: &mut throwaway,
                }
                .visit_expr_mut(&mut cleaned)?;
                retained.push(Stmt::Let {
                    pattern: pattern.clone(),
                    value: cleaned,
                });
            }
        }
    }
    if let BlockTail::Value(e @ (Expr::If { .. } | Expr::Match { .. })) = &b.tail {
        if let Some(c) = expr_contribution(e, kind, ids, consumed)? {
            contribs.push(c);
        }
    }
    Ok((retained, contribs))
}

/// Contribution of an `if`/`match` expression to a companion of `kind`:
/// `Some` mirroring the branch structure when at least one branch (or
/// arm) carries a predicate of `kind`, else `None`.
fn expr_contribution(
    e: &Expr,
    kind: SpecKindLite,
    ids: &ProverFnIds,
    consumed: &mut usize,
) -> Result<Option<Expr>, Stage7Error> {
    match e {
        Expr::If {
            cond,
            then_branch,
            else_branch,
        } => {
            let (ts, tc) = collect_struct(then_branch, kind, ids, consumed)?;
            let (es, ec) = collect_struct(else_branch, kind, ids, consumed)?;
            if tc.is_empty() && ec.is_empty() {
                return Ok(None);
            }
            Ok(Some(Expr::If {
                cond: cond.clone(),
                then_branch: Box::new(branch_from(ts, tc)),
                else_branch: Box::new(branch_from(es, ec)),
            }))
        }
        Expr::Match {
            struct_id,
            selector,
            cases,
        } => {
            let mut new_cases: Vec<MatchArm> = Vec::with_capacity(cases.len());
            let mut any = false;
            for arm in cases {
                let (as_stmts, ac) = collect_struct(&arm.body, kind, ids, consumed)?;
                if !ac.is_empty() {
                    any = true;
                }
                new_cases.push(MatchArm {
                    variant: arm.variant,
                    bindings: arm.bindings.clone(),
                    body: Box::new(branch_from(as_stmts, ac)),
                });
            }
            if !any {
                return Ok(None);
            }
            Ok(Some(Expr::Match {
                struct_id: *struct_id,
                selector: selector.clone(),
                cases: new_cases,
            }))
        }
        _ => Ok(None),
    }
}

/// A branch block: its scaffolding lets wrapping the conjunction of its
/// contributions, or `true` when it carries no predicate of the kind (so
/// the conditional collapses to an implication on the guarded path).
fn branch_from(stmts: Vec<Stmt>, contribs: Vec<Expr>) -> Block {
    if contribs.is_empty() {
        Block {
            stmts: Vec::new(),
            tail: BlockTail::Value(Expr::Const(crate::ir::ty::Const::Bool(true))),
        }
    } else {
        Block {
            stmts,
            tail: BlockTail::Value(conjoin(&contribs)),
        }
    }
}

/// Build a `Spec(Requires/Ensures)` companion `Function`.
fn build_companion(
    target: &Function,
    target_fid: FunId,
    kind: SpecKind,
    body: Block,
    add_result_param: bool,
) -> Function {
    // `.asserts` is a Bool predicate -- it feeds the Bool-encoded
    // theorem statements (where the connectives are Bool->Bool).
    // `.requires` / `.ensures` are Prop (lifted from their Bool body).
    let return_type = match kind {
        SpecKind::Asserts => Type::Bool,
        SpecKind::Requires | SpecKind::Ensures => Type::Prop,
        SpecKind::Aborts => unreachable!(".aborts emitted by aborts_variant, not spec_companion"),
    };
    let extra_params = if add_result_param {
        let result_var = fresh_result_var(&target.signature.params);
        vec![Param {
            name: "result".to_string(),
            var: result_var,
            ty: target.signature.return_type.clone(),
        }]
    } else {
        Vec::new()
    };
    make_spec_companion(target, target_fid, kind, body, extra_params, return_type)
}

/// Conjoin `preds` with `BinOp::And`. Empty -> `Bool(true)`; singleton
/// -> the bare predicate; otherwise left-associated AND.
fn conjoin(preds: &[Expr]) -> Expr {
    use crate::ir::ops::BinOp;
    use crate::ir::ty::Const;
    if preds.is_empty() {
        return Expr::Const(Const::Bool(true));
    }
    let mut iter = preds.iter().cloned();
    let mut acc = iter.next().unwrap();
    for p in iter {
        acc = Expr::BinOp {
            op: BinOp::And,
            lhs: Box::new(acc),
            rhs: Box::new(p),
        };
    }
    acc
}

/// Allocate a fresh `VarId` for the `result` param that doesn't
/// collide with any existing param's var.
fn fresh_result_var(params: &[Param]) -> crate::ir::VarId {
    let mut name = "result".to_string();
    let mut suffix = 0u32;
    loop {
        let candidate = crate::ir::VarId::from(name.clone());
        if !params.iter().any(|p| p.var == candidate) {
            return candidate;
        }
        suffix += 1;
        name = format!("result_{suffix}");
    }
}
