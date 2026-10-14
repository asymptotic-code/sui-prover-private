//! Stage 7 (rewrite) -- `.aborts` variant + unified control-flow extraction.
//!
//! See `plans/lean-pipeline/stage-07-rewrite.md` for the design.
//!
//! ## Scope
//!
//! This module is the sole stage-7 implementation. Instead of the
//! retired `dejumps` approach (a parallel `Bool` predicate), we take a
//! fundamentally different approach to abort derivation: instead of synthesising a
//! `Bool` predicate by walking the body in parallel, we **clone the
//! body as a sibling function** (the `.aborts` variant) and rewrite
//! it at the IR level to return `Option<MoveAbortCode>`. Then we run
//! unified control-flow extraction over BOTH variants, lowering
//! `Expr::While`, `BlockTail::Break / Continue / Return` to
//! tail-functions.
//!
//! ## Phases
//!
//! 1. **`spec_companion::collect_predicates`** -- walk every source
//!    function, collect `prover::requires / ensures / asserts`
//!    predicates, remove the spec calls from the body.
//! 2. **`aborts_variant::materialise`** -- for each non-native,
//!    non-Spec source function, allocate a sibling FunId for
//!    `.aborts` and clone the body. Apply per-tail rewrites
//!    (function-tail `Value(_) → Value(None)`, `Return(_) →
//!    Return(None)`, `Abort{code} → Return(Some(code))`) and
//!    sub-expression splices (asserts, callee aborts via
//!    `aborts_map`, `BorrowMapKey`).
//! 3. **Control-flow extraction** -- over every Source + Spec(Aborts)
//!    body:
//!    - `Expr::While` -> `LoopBody` + `LoopAfter` helpers.
//!    - `BlockTail::Break / Continue` -> tail-Calls into helpers.
//!    - safely liftable inner `BlockTail::Return` -> continuation function
//!      `f.cont_N`, with the Return-arm becoming a direct `Value` and the
//!      other-arm becoming a tail-Call. Unlifted Returns remain classified
//!      residuals at the renderer boundary; known exclusions include
//!      borrow/mutation threading and source self-recursion.
//!    - function-tail `BlockTail::Return(v)` -> `Value(v)` (today's
//!      function-tail collapse rule, applied as cleanup).
//! 4. **`spec_companion::emit_requires_ensures`** -- emit
//!    `Spec(Requires)` / `Spec(Ensures)` siblings from collected
//!    predicates.
//! 5. **`postcondition::check`** -- validate invariants.

pub mod aborts_defunctionalize;
pub mod aborts_live_loop;
pub mod aborts_loop_propagate;
pub mod aborts_variant;
pub mod asymmetric_arms;
pub mod cont_inline;
pub mod labeled_block_extract;
pub mod loop_extract;
pub mod option_aborts;
pub mod postcondition;
pub mod return_collapse;
pub mod return_lift;
pub mod spec_companion;

#[cfg(test)]
mod tests;

use std::collections::BTreeMap;

use crate::ir::builder::ProverFnIds;
use crate::ir::{
    AbortPayloadMode, AbortProvenance, Block, Effects, FunId, Function, FunctionKind, Param,
    Program, Signature, SpecKind, StructId, Type, VarId,
};

pub(super) fn find_world_struct_id(program: &Program) -> Option<StructId> {
    program.struct_id_by_qualified_name(crate::stage_04_effects::world::WORLD_QUALIFIED_NAME)
}

pub(super) fn current_world_var(
    scope: &BTreeMap<VarId, Type>,
    world_id: StructId,
) -> Option<VarId> {
    scope
        .iter()
        .filter(|(_, ty)| crate::stage_04_effects::common::is_world_type(ty, world_id))
        .max_by(|(left, _), (right, _)| {
            crate::ir::names::world_ssa_generation(left.as_ref())
                .cmp(&crate::ir::names::world_ssa_generation(right.as_ref()))
                .then_with(|| left.cmp(right))
        })
        .map(|(var, _)| var.clone())
}

pub(super) fn make_spec_companion(
    target: &Function,
    target_fid: FunId,
    kind: SpecKind,
    body: Block,
    extra_params: Vec<Param>,
    return_type: Type,
) -> Function {
    let name = match kind {
        SpecKind::Aborts => crate::ir::names::aborts_name(&target.name),
        SpecKind::Requires => crate::ir::names::requires_name(&target.name),
        SpecKind::Ensures => crate::ir::names::ensures_name(&target.name),
        SpecKind::Asserts => crate::ir::names::asserts_name(&target.name),
    };
    let mut params = target.signature.params.clone();
    params.extend(extra_params);
    Function {
        module: target.module,
        name,
        signature: Signature {
            type_params: target.signature.type_params.clone(),
            params,
            return_type,
        },
        body,
        kind: FunctionKind::Spec {
            kind,
            target: target_fid,
        },
        effects: Effects::PURE,
        explicit_pure: false,
    }
}

/// Errors produced by stage 7 (rewrite).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Stage7Error {
    AmbiguousAbortOrigin {
        addressed_module: String,
        first_module: crate::ir::ModId,
        duplicate_module: crate::ir::ModId,
    },
    /// `prover::requires/ensures/asserts` call appears in a non-`Eval`
    /// position (e.g. its return is bound to a `let`).
    SpecCallInValuePosition,
    /// `BlockTail::Break { level: k }` referenced a level deeper than
    /// the enclosing while-stack at this point.
    JumpLevelOutOfBounds { level: u32, depth: u32 },
    /// A `BlockTail::Break/Continue { value }` payload's shape doesn't
    /// match the target loop's `iter_local_count`.
    JumpValueArityMismatch { expected: usize, carried: String },
    /// Stage 5 must record one post-header exit value for every loop-carried
    /// iteration local. A mismatch would make the condition-false edge drop
    /// or misalign state.
    ///
    /// `function` / `function_name` identify the parent whose loop carries the
    /// bad `While`. Without them this error is two bare integers, which in a
    /// 4000-function package can only be resolved by bisecting the corpus.
    HeaderExitArityMismatch {
        function: FunId,
        function_name: String,
        expected: usize,
        found: usize,
    },
    /// A loop jump occurs inside an operand whose remaining evaluation
    /// context cannot yet be represented without changing evaluation order.
    JumpInOperand,
    /// Catch-all for `type_of` failures inside loop extraction's
    /// `map_type_err`.
    UnexpectedWhile,
    /// A `prover::*` predicate sits in a position the structural
    /// `.requires`/`.ensures`/`.asserts` companion builder cannot
    /// reproduce as `if`/`match` (e.g. inside a `while` loop or
    /// quantifier body), so it would be silently dropped. Real specs
    /// never put predicates there; this fires loudly if one ever does.
    SpecPredicateUnreachable,
    /// An abortable callee `g` (one with an `.aborts` companion in
    /// `aborts_map`) appears in a value / argument position -- nested
    /// inside a compound expression (a `Call` argument, `BinOp`
    /// operand, `Pack` field, ...) rather than as the direct RHS of a
    /// `Stmt::Let` or a bare `Stmt::Eval`. The callee-aborts splice
    /// only guards statement-position calls; a nested one would have
    /// its abort verdict silently dropped, rendering the enclosing
    /// `.aborts` companion unsoundly total (see
    /// `aborts_variant::check_no_value_position_aborts`). stage_06
    /// let-inline guarantees this never happens today (it never folds a
    /// non-total op into a value position); this fires loudly if that
    /// invariant ever breaks. `callee` is the offending source FunId.
    ValuePositionAbort { callee: FunId },
}

/// Run stage 7 (rewrite) over `program`.
pub fn run(program: &mut Program, prover_ids: &ProverFnIds) -> Result<(), Stage7Error> {
    run_with_payload_mode(program, prover_ids, AbortPayloadMode::Proof)
}

pub fn run_with_payload_mode(
    program: &mut Program,
    prover_ids: &ProverFnIds,
    payload_mode: AbortPayloadMode,
) -> Result<(), Stage7Error> {
    AbortProvenance::configure(program, payload_mode).map_err(|error| {
        Stage7Error::AmbiguousAbortOrigin {
            addressed_module: error.addressed_module,
            first_module: error.first_module,
            duplicate_module: error.duplicate_module,
        }
    })?;
    // Snapshot each source body BEFORE collect_predicates strips the
    // `prover::*` calls. `materialise` needs the `prover::asserts(p)`
    // calls in their source positions to lower each into an in-place
    // abort guard (`if !p { return Aborted } else { rest }`), keeping
    // branch-conditional asserts inside their branch.
    let pre_strip_bodies: std::collections::BTreeMap<crate::ir::FunId, crate::ir::expr::Block> =
        program
            .functions
            .iter()
            .filter(|(_, f)| {
                matches!(
                    f.kind,
                    crate::ir::function::FunctionKind::Source
                        | crate::ir::function::FunctionKind::Test { .. }
                )
            })
            .map(|(id, f)| (*id, f.body.clone()))
            .collect();

    // Phase 1: collect predicates + remove spec calls from source bodies.
    let predicates = spec_companion::collect_predicates(program, prover_ids)?;

    // Phase 2: materialise `.aborts` variants (lowering asserts in place
    // from the pre-strip bodies).
    let aborts_map = aborts_variant::materialise(program, &pre_strip_bodies, prover_ids)?;

    // Phase 3a-pre: extract every `Expr::LabeledBlock` into helper
    // functions. Runs BEFORE loop_extract so any `Expr::While` inside
    // a LabeledBlock body lands inside the helper, where loop_extract
    // then processes it normally.
    labeled_block_extract::run(program)?;

    // Phase 3a: extract every `Expr::While` into LoopBody + LoopAfter
    // helpers FIRST, before inner-Return lifting. After this pass
    // the IR contains zero loop structure outside the synthetic
    // LoopBody if-cond wraps -- so the inner-Return lift below can
    // walk function bodies without ever seeing `Expr::While`. This
    // ordering eliminates the CPS Let-lift's compounding duplication
    // when an inner Return sits inside a while body: the while is
    // already gone by the time we look at the surrounding stmt.
    loop_extract::run(program)?;

    // Phase 3a.5: for `.aborts` variants, convert aborting loop helpers
    // to return AbortResult and propagate the loop's abort verdict in the
    // parent body. Runs AFTER loop_extract (the helpers exist) and BEFORE
    // return_lift (which then lifts the now-AbortResult helpers' inner
    // `Return(Aborted)` normally). See aborts_loop_propagate.rs.
    aborts_loop_propagate::run(program, &aborts_map)?;

    // Phase 3a.5b (S2): propagate callee-aborts dropped from loops nested
    // inside EXTRACTED LABELED BLOCKS. `loop_extract` types such a loop by
    // its `<f>.aborts.labeled_N` wrapper parent (accumulator-typed), so
    // `aborts_loop_propagate` (which groups loops under a DIRECT `Spec(Aborts)`
    // parent) skips it and every callee-abort inside is dropped -- the loop
    // renders unconditionally NoAbort (a soundness gap, sibling of the phase
    // 3b.6 value-nested case). This pass retypes the loop chain to AbortResult,
    // deadens its value-leaves, splices the loop's callee-aborts, and
    // propagates the wrapper's verdict through the `Spec(Aborts)` parent's
    // dead consumption. Runs BEFORE phase 3a.6 (whose `Spec(Aborts)`-parent
    // filter still excludes these Synthetic-parented loops) and BEFORE
    // return_lift (which lifts the injected inner `Return(Aborted)`s).
    aborts_variant::retype_and_splice_labeled_block_loops(program, &aborts_map);

    // Phase 3a.6: thread discarded callee-aborts inside extracted
    // `.aborts` loop bodies. Phase 2 (`materialise`) skips callee-abort
    // triggers inside live `While` bodies (scoping). loop_extract has
    // since lifted those bodies into standalone AbortResult-typed
    // LoopBody helpers, so the splice is now well-scoped. Runs AFTER
    // aborts_loop_propagate (its input stays unperturbed) and BEFORE
    // return_lift (which lifts the injected inner `Return`s).
    let spliced_loops =
        aborts_variant::splice_callee_aborts_in_extracted_loops(program, &aborts_map);

    // Keep loop self-calls directly under their tail conditionals. Wrapping
    // them in return_lift's carrier makes Lean's partial-fixpoint monotonicity
    // checker reject otherwise valid recursive loops.
    //
    // Collapse function-tail Returns first. The asymmetric rewrite moves the
    // surrounding remainder into a formerly collapsed arm; without this
    // normalization a regular LoopBody's safe tail Return becomes an inner
    // Return before `return_lift` sees it (DeepBook
    // `clean_up_expired_orders.while_0`).
    return_collapse::run(program)?;
    asymmetric_arms::run_regular_loop_helpers(program);

    // Phase 3b: lift inner Returns out of let-value / eval positions.
    // The ordinary path allocates `f.cont_N` continuation helpers; source
    // bodies whose mutable state cannot be captured safely use an in-place
    // `AbortResult<return_type>` carrier instead. This runs over `.aborts`
    // companions, relevant source/test functions, and synthetic/loop helpers.
    return_lift::run(program)?;

    // Phase 3b.5: live-accumulator loop-abort fold. The dead-accumulator
    // case (3a.5) cannot handle a loop whose accumulator is consumed by a
    // post-loop continuation; by now `return_lift` has extracted that
    // continuation into a function, so the fold is expressible. Runs AFTER
    // return_lift. See aborts_live_loop.rs.
    aborts_live_loop::run(program)?;

    // Phase 3b.5b: the same fold for a loop nested in an EXTRACTED LABELED
    // BLOCK whose accumulator is consumed LIVE. Phase 3a.5b converts such a
    // chain only when every consumption is dead, and phase 3b.5 never
    // enumerates it (its `LoopBody`'s parent is the Synthetic
    // `.aborts.labeled_N` wrapper, not the `Spec(Aborts)` fn), so the VALUE
    // loop shipped under an `.aborts.` name with every callee-abort inside it
    // dropped -- the soundness gap `postcondition::check`'s
    // `MisfiledAbortsFamilyValueChain` reports.
    //
    // Sits HERE, and not with its 3a.5b sibling, for the same reason 3b.5
    // does: the manufactured continuation is the host's post-consumption
    // remainder, and only after `return_lift` (3b) is that remainder free of
    // inner Returns and safe to lift verbatim into a function body. Must
    // stay BEFORE the phase-3b.6 `return_lift` below, which is what lifts
    // the `Return(Aborted)`s this pass's own loop splice injects, and before
    // `cont_inline` / `rethread_loop_self_calls` (3d / 3d.5), which flatten
    // and re-thread the `__la_*` extras it adds. See aborts_live_loop.rs.
    aborts_live_loop::run_labeled_wrapper_loops(program, &aborts_map)?;

    // Phase 3b.6: late callee-aborts splice for `.aborts` loop bodies that
    // only became `AbortResult`-typed AFTER phase 3a.6 -- loops whose
    // accumulator is dead in the `.aborts` variant but consumed in the source
    // (a `while` nested in a value-position `if`/`match`, world-threaded:
    // `earned`, `update_reward`). `aborts_loop_propagate` (3a.5) /
    // `aborts_live_loop` (3b.5) retype these, but only AFTER phase 3a.6
    // already skipped the splice (they were still accumulator-typed then),
    // so their callee-aborts were silently dropped -- the loop rendered as
    // unconditionally NoAbort (a soundness gap: `f.aborts = NoAbort` did not
    // entail the loop-body abort preconditions). Splice them now, then run
    // `return_lift` again to lift the injected inner `Return(Aborted)`s (out of
    // value-position `if`/`match` arms) exactly as phase 3b did for the phase
    // 3a.6 splice. `spliced_loops` excludes the phase-3a.6 set, so no loop is
    // double-spliced; a no-op when there is nothing new to splice.
    aborts_variant::splice_callee_aborts_in_late_loops(program, &aborts_map, &spliced_loops);
    return_lift::run(program)?;

    // Phase 3c: remaining control-flow cleanup. Collapse function-tail
    // Returns before asymmetric-arm reconstruction moves the remainder into
    // an inner branch, then collapse again for any tail exposed by that
    // rewrite. The first collapse is essential for regular LoopBody helpers:
    // their function-tail `Return(Call(loop_after))` is safe, but moving it
    // first would turn it into an illegal inner Return inside a value-producing
    // branch (DeepBook `clean_up_expired_orders.while_0`).
    return_collapse::run(program)?;
    asymmetric_arms::run(program)?;
    return_collapse::run(program)?;

    // Phase 3d: inline single-use Synthetic continuations into their unique
    // callers, flattening return_lift's cont chains so the Lean interpreter
    // (no TCO) does not deep-recurse on deeply-lifted tests like
    // `test_multiaddr` (code-2000 interpreter overflow). Semantics-preserving.
    // A `.aborts.labeled_N` wrapper phase 3b.5b just rewrote its host to
    // TAIL-call is inlinable here and is ALSO the `parent` of that chain's
    // LoopBody/LoopAfter, so the pass re-points the pair onto the absorbing
    // host rather than leaving `function-kind-references-resolve` dangling.
    cont_inline::run(program)?;

    // Phase 3d.5: re-thread the live-accumulator fold's `__la_*` extras into
    // loop self-calls that `cont_inline` only just flattened from continuation
    // calls into direct self-recursion. Must run AFTER cont_inline, when the
    // self-calls exist. See
    // aborts_live_loop::rethread_loop_self_calls.
    aborts_live_loop::rethread_loop_self_calls(program)?;

    // Phase 3d.6: defunctionalize deep `.aborts.while_N` loops -- emit a total
    // `<loop>_step` returning a `cont <next>|done <AbortResult>` sum + a tiny
    // recursive matcher, so `partial_fixpoint`'s monotonicity proof for the
    // loop stays shallow (the heavy body sits in the total step fn, outside the
    // fixpoint). Runs AFTER cont_inline + self-call rethreading. See
    // aborts_defunctionalize.rs.
    aborts_defunctionalize::run(program);

    // Defunctionalization can replace the last call to a lifted continuation.
    // Remove those orphan chains before their obsolete capture types reach
    // the next stage's type invariant; structural loop parents remain roots.
    cont_inline::prune_unreferenced_continuations(program);

    // Phase 4: emit `.requires` / `.ensures` companions. Rebuilds each
    // companion body STRUCTURALLY from the pre-strip snapshot so that
    // branch-distributed predicates keep their `if`/`match` guards
    // (`if c { ensures!(A) } else { ensures!(B) }` -> `if c then A else
    // B`, not the over-constrained `A && B`).
    spec_companion::emit_requires_ensures(
        program,
        &predicates,
        &pre_strip_bodies,
        prover_ids,
        &aborts_map,
    )?;

    #[cfg(debug_assertions)]
    {
        if let Err(e) = postcondition::check(program, prover_ids) {
            let function = match &e {
                postcondition::PostconditionError::LingeringInnerReturn { function } => {
                    program.functions.get(function).map(|f| f.name.as_str())
                }
                postcondition::PostconditionError::BaseValidator(error) => error
                    .function
                    .and_then(|fid| program.functions.get(&fid))
                    .map(|f| f.name.as_str()),
                postcondition::PostconditionError::MisfiledAbortsFamilyValueChain {
                    function,
                    ..
                } => program.functions.get(function).map(|f| f.name.as_str()),
                _ => None,
            };
            let dropped_callee = match &e {
                postcondition::PostconditionError::MisfiledAbortsFamilyValueChain {
                    dropped_callee,
                    ..
                } => program
                    .functions
                    .get(dropped_callee)
                    .map(|f| f.name.as_str()),
                _ => None,
            };
            debug_assert!(
                false,
                "stage 7 (rewrite) postcondition failed in {function:?} (dropped callee {dropped_callee:?}): {e:?}"
            );
        }
    }

    Ok(())
}
