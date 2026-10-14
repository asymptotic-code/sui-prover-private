//! Phase 2 -- `.aborts` variant materialisation.
//!
//! For each non-native, non-Spec source `Function f`:
//! 1. Reserve a sibling FunId `f.aborts` in `aborts_map` (so callee
//!    composition can refer to mutually recursive callees that
//!    haven't been materialised yet).
//! 2. Clone `f.body` into `aborts_body`. Every `Stmt::Let { .. }` is
//!    preserved verbatim — the cloned body inherits the original's
//!    scoping.
//! 3. Walk `aborts_body` and apply the per-tail rewrites:
//!    - **Function-tail** `BlockTail::Value(_) → BlockTail::Value(None)`.
//!    - `BlockTail::Return(_) → BlockTail::Return(None)`.
//!    - `BlockTail::Abort { code } → BlockTail::Return(Some(code))`.
//!    - **Inner** `BlockTail::Value(_)`, `BlockTail::Break/Continue`
//!      left unchanged.
//! 4. Apply sub-expression splices: lift early-exits out of stmt /
//!    sub-expression positions to enclosing block tails. (Slice 1 of
//!    the rewrite implements per-tail rewrites only; splices land
//!    in slice 2 — see "Status" below.)
//!
//! Sets `f.aborts.signature.return_type = Option<MoveAbortCode>`,
//! `f.aborts.kind = FunctionKind::Spec { kind: Aborts, target: f.id }`,
//! `f.aborts.effects = Effects::PURE`.
//!
//! ## Status
//!
//! Slice 1 (this file's current state) implements:
//! - Synthetic struct registration (via `option_aborts`).
//! - FunId allocation + sibling `.aborts` Function emission.
//! - Per-tail rewrites for Value/Return/Abort.
//! - Identity copy of every other Expr / Stmt / Block shape.
//!
//! Not yet implemented (slice 2):
//! - Sub-expression splices for prover::asserts.
//! - Sub-expression splices for callee aborts (g.aborts ∈ aborts_map).
//! - Sub-expression splices for Expr::BorrowMapKey.
//! - ANF lifting of value-position Calls to functions with `.aborts`.
//!   This is a NO-OP today: stage_06 let-inline never folds a
//!   non-total op into a value / argument position (`single_use.rs`
//!   only inlines `is_pure_total` values, and an abortable `Call` is
//!   never pure-total), so an abortable callee always reaches this
//!   stage bound to its own `Stmt::Let` -- statement position, which
//!   the callee-aborts splice DOES guard. Because full ANF-lifting is
//!   unimplemented, a value-position abortable callee would silently
//!   lose its abort guard (the companion would render unsoundly
//!   total). `check_no_value_position_aborts` (invoked at the end of
//!   `materialise`'s phase-1b, after the block splice) is the
//!   fail-loud tripwire: it returns `Stage7Error::ValuePositionAbort`
//!   the instant that stage_06 invariant ever breaks, instead of
//!   dropping the guard silently.

use std::collections::{BTreeMap, BTreeSet};

use crate::ir::builder::ProverFnIds;
use crate::ir::expr::{Block, BlockTail, Expr, MatchArm, Stmt};
use crate::ir::function::{Function, FunctionKind, SpecKind};
use crate::ir::ops::BitOp;
use crate::ir::quant::QuantDomain;
use crate::ir::ty::{Const, Type};
use crate::ir::{
    canonical_addressed_module, AbortPayloadMode, FunId, ObservedErrorKind, Program,
    UNKNOWN_ABORT_ORIGIN_TAG,
};

use super::option_aborts::{ensure_aborts_types, AbortsTypeIds, OPTION_NONE_TAG, OPTION_SOME_TAG};
use super::{make_spec_companion, Stage7Error};

/// Map from source FunId to its `.aborts` companion FunId.
pub type AbortsMap = BTreeMap<FunId, FunId>;

/// Materialise the `.aborts` variant for every processable source
/// function. Returns the `aborts_map` consumed by
/// `spec_companion::emit_requires_ensures`.
pub fn materialise(
    program: &mut Program,
    pre_strip_bodies: &BTreeMap<FunId, crate::ir::expr::Block>,
    prover_ids: &ProverFnIds,
) -> Result<AbortsMap, Stage7Error> {
    let types = ensure_aborts_types(program);

    // A hand-written native `.aborts` companion normally returns `Bool`
    // (the framework convention -- the callee-aborts splice then wraps a
    // `true` into the fixed `Aborted { code := 0 }`). A few natives
    // (`validate_metadata_bcs`) instead return the full
    // `Abort.AbortResult AbortCode` so they can carry a SPECIFIC code.
    // stage 2 registered their synthetic companion with a `Bool` return
    // type (the `AbortResult` struct didn't exist yet); retype it now to
    // the real `AbortResult` type so `program_lookup_return_type` reports
    // it and the splice match-propagates the code instead of collapsing.
    retype_abort_code_native_companions(program, &types);

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

    // Phase 1a: pre-allocate FunIds so mutually-recursive callee
    // composition (slice 2) can refer to siblings before they're
    // materialised. Also seed aborts_map with pre-existing
    // Spec(Aborts) companions (e.g. hand-written natives or
    // re-running stage 7 on a partially-processed program) and
    // synthetic native aborts companions registered by stage 10
    // (BoundedU{N}_<op>_aborts).
    let mut aborts_map: AbortsMap = program
        .functions
        .iter()
        .filter_map(|(id, f)| match f.kind {
            FunctionKind::Spec {
                kind: SpecKind::Aborts,
                target,
            } => Some((target, *id)),
            _ => None,
        })
        .chain(
            program
                .natives
                .decls
                .iter()
                .filter_map(|(id, d)| d.spec_target.map(|t| (t, *id))),
        )
        .collect();
    let mut next_fid = program.next_function_id();
    for fid in &processable_fids {
        let aborts_fid = next_fid;
        next_fid += 1;
        aborts_map.insert(*fid, aborts_fid);
    }

    // Phase 1b: build each `.aborts` function.
    for &source_fid in &processable_fids {
        let aborts_fid = aborts_map[&source_fid];
        let source = program
            .functions
            .get(&source_fid)
            .expect("source fid present")
            .clone();
        let source_types =
            types.with_origin_tag(program.abort_provenance.tag_for_module(source.module));
        // Use the PRE-STRIP body (still carrying `prover::asserts`
        // calls) so step 2 can lower them in place. The program's own
        // copy has had the spec calls removed by collect_predicates.
        let mut aborts_body = pre_strip_bodies
            .get(&source_fid)
            .expect("pre-strip body present for processable source fid")
            .clone();

        // Step 1: apply per-tail rewrites uniformly. The pass also
        // substitutes Return(Call(g)) -> Return(Call(g.aborts)) for
        // early-return-of-abortable-call patterns
        // (`if cond { return neg_from(x) }; ...`).
        rewrite_block(
            &mut aborts_body,
            &source_types,
            &aborts_map,
            /* is_function_tail = */ true,
        );

        // Step 2: wrap the body in early-exit guards for every
        // collected `prover::asserts(p)` predicate. Critical: this
        // MUST happen before the callee-aborts splice. The assert
        // predicates may reference let-bindings from the body's
        // stmts. At step 2's wrap point those lets are still at the
        // body's top-level stmts, in scope at the body's tail
        // (where the wrap places its If). After the splice (step
        // 3), the splice moves post-trigger stmts (including some
        // of those let-bindings) into the Match's NoAbort arm; if
        // the wrap happened after the splice, the assert If would
        // sit outside the Match while referencing vars bound inside
        // it -- a scope violation.
        //
        // Wrapping before splice keeps the assert guards at their
        // source positions; the splice then naturally moves any guard
        // (with the let-bindings it references) into the Match's NoAbort
        // arm, preserving scope. Branch-conditional asserts stay inside
        // their branch -- see `lower_prover_asserts_in_block`.
        lower_prover_asserts_in_block(&mut aborts_body, prover_ids, &source_types);

        // Step 3: splice callee aborts. For every Stmt::Eval(Call(g,
        // args)) or Stmt::Let { value: Call(g, args), .. } whose `g`
        // has an `.aborts` companion in `aborts_map`, rewrite the
        // enclosing block to inject a `let __c = g.aborts(args)` and
        // an abort-check at the block tail.
        //
        // The splice's Aborted arm uses `BlockTail::Return(__c)`
        // (early-exit terminator). The Return is structurally an
        // early-exit; it carries no contribution to the Match's
        // value type. The inner-Return lift pass (return_lift.rs)
        // later extracts continuation tail-functions so the
        // rendered Lean type-checks.
        let scope = collect_function_var_types(&source, program);
        splice_callee_aborts_in_block(
            &mut aborts_body,
            &mut SpliceCtx {
                aborts_map: &aborts_map,
                types: &source_types,
                program,
                next_var_suffix: 0,
                inside_loop_body: false,
                scope,
                only_callee: None,
            },
        );

        // Fail-loud tripwire for the latent ANF gap. The block splice
        // above only guards abortable callees in STATEMENT position
        // (`Stmt::Let { value: Call(g) }` / `Stmt::Eval(Call(g))`); a
        // value-position abortable callee (nested in a `Call` argument,
        // `BinOp` operand, ...) slips through with its abort verdict
        // silently dropped. stage_06 let-inline guarantees that never
        // happens (it never folds a non-total op into a value
        // position), so this is a no-op on well-formed input; it errors
        // the instant that invariant ever breaks.
        check_no_value_position_aborts(&aborts_body, program, &aborts_map)?;

        let aborts_fn = make_spec_companion(
            &source,
            source_fid,
            SpecKind::Aborts,
            aborts_body,
            Vec::new(),
            types.option_abort_code_type(),
        );
        program.functions.insert(aborts_fid, aborts_fn);
    }

    strip_ghost_args_from_native_aborts_calls(program, &aborts_map);
    Ok(aborts_map)
}

/// Retype the synthetic `.aborts` companion of every native in
/// [`crate::stage_02_ir_cfg::natives::NATIVES_WITH_ABORT_CODE_COMPANIONS`]
/// from `Bool` to `Abort.AbortResult AbortCode`. A companion is
/// identified by its `spec_target` pointing back to the base native; the
/// base's `(package, module, name)` is matched against the code-companion
/// list. Without this the callee-aborts splice sees a `Bool` return type
/// and collapses every failing check to the fixed `code := 0`.
fn retype_abort_code_native_companions(program: &mut Program, types: &AbortsTypeIds) {
    use crate::stage_02_ir_cfg::natives::native_aborts_companion_returns_code;
    let abort_result_ty = types.option_abort_code_type();
    let to_retype: Vec<FunId> = program
        .natives
        .decls
        .iter()
        .filter_map(|(cid, companion)| {
            let base_fid = companion.spec_target?;
            let base = program.natives.decls.get(&base_fid)?;
            let module = program.modules.get(&base.module)?;
            if native_aborts_companion_returns_code(&module.package_name, &module.name, &base.name)
            {
                Some(*cid)
            } else {
                None
            }
        })
        .collect();
    for cid in to_retype {
        if let Some(companion) = program.natives.decls.get_mut(&cid) {
            companion.signature.return_type = abort_result_ty.clone();
        }
    }
}

/// A ghost-writing native's `.aborts` companion (e.g. `object::new.aborts`,
/// `(ctx): Bool`) is hand-written and NOT ghost-augmented, but the
/// callee-aborts substitution/splice turns a source `Call(native, args)`
/// into `Call(native.aborts, args)` verbatim -- and `args` carries the
/// trailing ghost slots that stage-4 threading appended to the source call.
/// (The ghost fixpoint guarantees every reachable caller threads exactly
/// `ghost_vars[native]` of them.) Drop those trailing args from each native
/// `<name>.aborts` call so the arity matches the companion's Lean def.
fn strip_ghost_args_from_native_aborts_calls(program: &mut Program, aborts_map: &AbortsMap) {
    // native `<name>.aborts` FunId -> count of trailing ghost args to drop.
    let strip: BTreeMap<FunId, usize> = aborts_map
        .iter()
        .filter(|(g, _)| program.natives.decls.contains_key(g))
        .filter_map(|(g, g_aborts)| program.ghost_vars.get(g).map(|v| (*g_aborts, v.len())))
        .filter(|(_, n)| *n > 0)
        .collect();
    if strip.is_empty() {
        return;
    }
    use crate::ir::visit::MutVisitor as _;
    let mut visitor = GhostAbortsArgStrip { strip: &strip };
    for f in program.functions.values_mut() {
        visitor.visit_block_mut(&mut f.body);
    }
}

struct GhostAbortsArgStrip<'a> {
    strip: &'a BTreeMap<FunId, usize>,
}

impl crate::ir::visit::MutVisitor for GhostAbortsArgStrip<'_> {
    fn visit_expr_mut(&mut self, e: &mut Expr) {
        if let Expr::Call { fun, args, .. } = e {
            if let Some(&n) = self.strip.get(fun) {
                let keep = args.len().saturating_sub(n);
                args.truncate(keep);
            }
        }
        crate::ir::visit::walk_expr_mut_default(self, e);
    }
}

// ---------------------------------------------------------------------------
// Extracted-loop callee-aborts splice (phase 3a.6)
// ---------------------------------------------------------------------------

/// Thread discarded callee-aborts that `materialise` deliberately
/// skipped inside live `While` bodies (`SpliceCtx::inside_loop_body`).
///
/// At materialise time, splicing a callee-abort `Match` into a live
/// `While` body would break header-var scoping, so the trigger is
/// punted. By the time this runs, `loop_extract` has lifted every
/// `While` body into a standalone `LoopBody` helper, and (for void
/// `.aborts` loops) re-typed that helper's return as `AbortResult`
/// via its `Unit -> parent_return_type` override. The body is now an
/// ordinary block, so the same splice that runs in `materialise` is
/// well-scoped here.
///
/// Scope is restricted to `LoopBody` helpers of `Spec(Aborts)`
/// parents whose return type is already `AbortResult`. The guard is
/// what makes this zero-blast-radius: it only injects `Return(Aborted)`
/// where the return type is `AbortResult`, so it can never mistype a
/// value-accumulating loop helper (whose return is the accumulator).
/// It runs AFTER `aborts_loop_propagate`, so that pass sees the
/// unperturbed input; `return_lift` (3b) then lifts the injected
/// inner `Return`s exactly as it does for the materialise-time splice.
pub(super) fn splice_callee_aborts_in_extracted_loops(
    program: &mut Program,
    aborts_map: &AbortsMap,
) -> BTreeSet<FunId> {
    let target_fids = abort_result_loop_bodies(program);
    for &fid in &target_fids {
        splice_one_extracted_loop(program, fid, aborts_map);
    }
    target_fids
}

/// Second, late splice pass (phase 3b.6). `aborts_loop_propagate` /
/// `aborts_live_loop` retype an `.aborts` loop body to `AbortResult`
/// only AFTER `loop_extract` typed it by its accumulator -- so a loop
/// whose accumulator is dead in the `.aborts` variant but is consumed
/// in the source (a `while` nested inside a value-position `if`/`match`,
/// world-threaded: `earned`, `update_reward`) becomes `AbortResult`-typed
/// only in phase 3b.5, AFTER the phase-3a.6 splice already skipped it (it
/// was still accumulator-typed then). Those loop bodies reach
/// `aborts_defunctionalize` `AbortResult`-typed but with EVERY callee-abort
/// dropped -- the loop renders as unconditionally NoAbort, so
/// `f.aborts = NoAbort` fails to entail the loop's abort preconditions (a
/// soundness gap).
///
/// This pass splices them right after `aborts_live_loop` (phase 3b.6): at
/// that point they are `AbortResult`-typed and the parent's loop-result
/// consumption has already been rewritten to propagate the abort verdict.
/// `exclude` is the set already spliced in phase 3a.6, so no loop is
/// double-spliced. The driver runs `return_lift` again immediately after,
/// lifting the injected inner `Return(Aborted)`s out of value-position
/// `if`/`match` arms -- exactly as phase 3b did for the phase-3a.6 splice.
///
/// Scope: only `LoopBody` helpers of a DIRECT `Spec(Aborts)` parent that
/// are `AbortResult`-typed by this point (see `abort_result_loop_bodies`).
/// A loop that becomes `AbortResult`-typed only later (e.g. one nested in
/// an extracted labeled block, whose parent is the labeled-block helper
/// rather than the `Spec(Aborts)` fn) is NOT covered here and remains for a
/// follow-up.
pub(super) fn splice_callee_aborts_in_late_loops(
    program: &mut Program,
    aborts_map: &AbortsMap,
    exclude: &BTreeSet<FunId>,
) -> BTreeSet<FunId> {
    let mut spliced = BTreeSet::new();
    for fid in abort_result_loop_bodies(program) {
        if exclude.contains(&fid) {
            continue;
        }
        splice_one_extracted_loop(program, fid, aborts_map);
        spliced.insert(fid);
    }
    spliced
}

/// `LoopBody` helpers of `Spec(Aborts)` parents whose return type is
/// already `AbortResult`. Restricting to `AbortResult`-typed bodies is
/// what keeps the splice sound: it only injects `Return(Aborted)` where
/// the return type is `AbortResult`, so it can never mistype a
/// value-accumulating loop helper.
fn abort_result_loop_bodies(program: &mut Program) -> BTreeSet<FunId> {
    let abort_result_ty = ensure_aborts_types(program).option_abort_code_type();
    let aborts_parents: BTreeSet<FunId> = program
        .functions
        .iter()
        .filter(|(_, f)| {
            matches!(
                f.kind,
                FunctionKind::Spec {
                    kind: SpecKind::Aborts,
                    ..
                }
            )
        })
        .map(|(id, _)| *id)
        .collect();
    program
        .functions
        .iter()
        .filter(|(_, f)| match f.kind {
            FunctionKind::LoopBody { parent, .. } => {
                aborts_parents.contains(&parent) && f.signature.return_type == abort_result_ty
            }
            _ => false,
        })
        .map(|(id, _)| *id)
        .collect()
}

pub(super) fn splice_one_extracted_loop(program: &mut Program, fid: FunId, aborts_map: &AbortsMap) {
    let types = ensure_aborts_types(program);
    let func = program
        .functions
        .get(&fid)
        .expect("loop body present")
        .clone();
    let scope = collect_function_var_types(&func, program);
    let func_types = types.with_origin_tag(program.abort_provenance.tag_for_module(func.module));
    let mut body = func.body;
    splice_callee_aborts_in_block(
        &mut body,
        &mut SpliceCtx {
            aborts_map,
            types: &func_types,
            program,
            next_var_suffix: 0,
            inside_loop_body: false,
            scope,
            only_callee: None,
        },
    );
    program.functions.get_mut(&fid).unwrap().body = body;
}

// ---------------------------------------------------------------------------
// Labeled-block loop abort propagation (S2)
// ---------------------------------------------------------------------------

/// One labeled-block loop chain whose discarded result hides a dropped
/// callee-abort, together with every function that consumes it.
struct LabeledLoopChain {
    /// Labeled-block wrapper `P` (e.g. `find_validator.aborts.labeled_0`,
    /// a `Synthetic` whose body is just `Value(Call(L, ..))`).
    wrapper_fid: FunId,
    /// Loop body `L` (e.g. `..labeled_0.while_0`).
    loop_fid: FunId,
    /// Loop-after `A` (e.g. `..labeled_0.while_0.after`).
    after_fid: FunId,
    /// Every function hosting a DEAD `let v = P(args)` consumption.
    /// Only the FunId is carried: the generic callee-aborts splice finds
    /// its own trigger inside the host at whatever depth it sits, so a
    /// block path + stmt index would be dead weight.
    hosts: Vec<FunId>,
}

/// Phase 3a.5b (S2): propagate callee-aborts dropped from loops nested
/// inside EXTRACTED LABELED BLOCKS -- the sibling of the value-nested loop
/// gap fixed in phase 3b.6.
///
/// `loop_extract` types a `LoopBody`/`LoopAfter` by its parent's return
/// type. For a `while` inside a `find_index!`-style labeled block, the
/// parent is the `<f>.aborts.labeled_N` Synthetic wrapper -- NOT the
/// `Spec(Aborts)` fn -- and that wrapper carries the labeled block's
/// ACCUMULATOR return type (`Option<u64>`), not `AbortResult`. So the loop
/// chain is accumulator-typed, and `aborts_loop_propagate` (3a.5) /
/// `aborts_live_loop` (3b.5) skip it (they only group `LoopBody`s under a
/// direct `Spec(Aborts)` parent). The loop reaches the renderer
/// accumulator-typed with EVERY callee-abort dropped: `f.aborts` discards
/// the wrapper (`let _ := labeled_0(..); NoAbort`) and renders as
/// unconditionally NoAbort -- a soundness gap (true on-chain aborts
/// falsifiable in the model).
///
/// This pass, run right after `aborts_loop_propagate`, mirrors that pass
/// for the labeled indirection. For each labeled-loop wrapper `P` whose
/// loop actually drops a callee-abort and whose every consumption is a
/// DEAD `let v = P(args)`:
///   1. Retype `L` / `A` / `P` to `AbortResult`.
///   2. "Deaden" `L` and `A`: every accumulator value-leaf becomes
///      `NoAbort`, every value-carrying labeled exit (`Return(some(i))`)
///      becomes `Return(NoAbort)` (or `Return(g.aborts(..))` when it wraps
///      a callee), every callee-abort `Match` propagates its payload -- so
///      the bodies deliver `AbortResult` while preserving the loop
///      self-call and the exit-to-`A` call.
///   3. Splice the loop's callee-aborts into `L` (the same splice
///      phase 3a.6 runs on direct-parented loops), now that `L` is
///      `AbortResult`-typed.
///   4. Propagate `P`'s verdict through each host's dead consumption --
///      using the SAME generic callee-aborts splice every other abortable
///      callee goes through, not a bespoke matcher. `P` is now an
///      `AbortResult`-returning callee with a dead result, which is
///      exactly the shape that splice exists for.
/// `return_lift` (3b) then lifts the injected inner `Return(Aborted)`s.
///
/// Tightly gated: only fires on the dead-result labeled-wrapper shape whose
/// loop contains a real dropped callee-abort, so loops with no dropped
/// abort -- and every non-labeled-loop module -- stay byte-identical.
pub(super) fn retype_and_splice_labeled_block_loops(program: &mut Program, aborts_map: &AbortsMap) {
    let types = ensure_aborts_types(program);
    let abort_result_ty = types.option_abort_code_type();
    let chains = find_labeled_block_loop_chains(program, aborts_map, &abort_result_ty);
    for chain in chains {
        // 1. Retype the loop chain to AbortResult.
        for fid in [chain.loop_fid, chain.after_fid, chain.wrapper_fid] {
            program
                .functions
                .get_mut(&fid)
                .unwrap()
                .signature
                .return_type = abort_result_ty.clone();
        }
        // 2. Deaden L and A (value-leaves -> abort-propagating form).
        for fid in [chain.loop_fid, chain.after_fid] {
            let mut body = std::mem::replace(
                &mut program.functions.get_mut(&fid).unwrap().body,
                empty_block(),
            );
            retype_loop_accumulator_leaves(
                &mut body,
                chain.loop_fid,
                chain.after_fid,
                &types,
                aborts_map,
                &AccumulatorLeaf::Deaden,
                &mut 0,
            );
            program.functions.get_mut(&fid).unwrap().body = body;
        }
        // 3. Splice the loop's callee-aborts into L (now AbortResult-typed).
        splice_one_extracted_loop(program, chain.loop_fid, aborts_map);
        // 4. Propagate P's abort verdict through every host's dead
        //    consumption, via the GENERIC splice: `P` is now an
        //    `AbortResult`-returning callee, so a one-entry map `{P -> P}`
        //    makes it an abortable callee like any other and the shared
        //    walker emits the guard at whatever depth the consumption sits.
        let host_map: AbortsMap = std::iter::once((chain.wrapper_fid, chain.wrapper_fid)).collect();
        for host_fid in &chain.hosts {
            splice_wrapper_consumption(program, *host_fid, chain.wrapper_fid, &host_map, &types);
        }
    }
}

/// Run the GENERIC callee-aborts splice over one host body, restricted to
/// the labeled-block wrapper `P`.
///
/// Two details make a SECOND splice pass safe on a body `materialise`
/// already spliced once:
/// - `only_callee` narrows trigger detection to statement-position calls
///   to `P` alone, so neither a preserved `let x = g(args)` nor a
///   synthesised `Borrow` guard (which resolves through `program`, not
///   `aborts_map`) can fire a second time and be double-guarded;
/// - `next_var_suffix` starts past the highest `__c_N` already bound in
///   the body, so the injected binding cannot shadow one of the first
///   pass's.
fn splice_wrapper_consumption(
    program: &mut Program,
    host_fid: FunId,
    wrapper_fid: FunId,
    host_map: &AbortsMap,
    types: &AbortsTypeIds,
) {
    let func = program
        .functions
        .get(&host_fid)
        .expect("host present")
        .clone();
    let scope = collect_function_var_types(&func, program);
    let host_types = types.with_origin_tag(program.abort_provenance.tag_for_module(func.module));
    let mut body = func.body;
    // Drop whatever transitively-dead cone reads the wrapper's result, so
    // demoting its binding cannot leave a dangling reference.
    prune_dead_wrapper_cone(&mut body, wrapper_fid, program);
    // The bound temp is dead by construction (that IS the acceptance
    // predicate), so demote the `let` to a bare `Eval`: the splice then
    // drops the trigger statement instead of preserving a second,
    // now-redundant call to `P` in the NoAbort continuation.
    demote_dead_wrapper_lets(&mut body, wrapper_fid);
    let next_var_suffix = next_abort_var_suffix(&body);
    splice_callee_aborts_in_block(
        &mut body,
        &mut SpliceCtx {
            aborts_map: host_map,
            types: &host_types,
            program,
            next_var_suffix,
            inside_loop_body: false,
            scope,
            only_callee: Some(wrapper_fid),
        },
    );
    program.functions.get_mut(&host_fid).unwrap().body = body;
}

/// Every var bound by a single-binding `let v = Call(wrapper, ..)` in `b`.
fn wrapper_let_binders(b: &Block, wrapper_fid: FunId) -> Vec<crate::ir::VarId> {
    use crate::ir::visit::{walk_stmt_default, Visitor};
    struct Binders {
        wrapper: FunId,
        out: Vec<crate::ir::VarId>,
    }
    impl Visitor for Binders {
        fn visit_stmt(&mut self, s: &Stmt) {
            if let Stmt::Let {
                pattern,
                value: Expr::Call { fun, .. },
            } = s
            {
                if pattern.len() == 1 && *fun == self.wrapper {
                    if let Some(v) = pattern[0].clone() {
                        self.out.push(v);
                    }
                }
            }
            walk_stmt_default(self, s);
        }
    }
    let mut binders = Binders {
        wrapper: wrapper_fid,
        out: Vec::new(),
    };
    binders.visit_block(b);
    binders.out
}

/// Prune the transitively-dead cone hanging off the labeled-block
/// wrapper's own result.
///
/// The `no_pending_or_active_duplicates_*` family does not bind the
/// wrapper's result and stop there: it negates it, folds the negation into
/// an `if`, and only THEN returns `NoAbort`. The result is dead, but only
/// once the two derived bindings above it are seen to be dead as well --
/// which is the dead-let elimination stage 6 performs later anyway (the
/// rendered `.after` reads `let _ := <f>.aborts.labeled_0 ..`, the whole
/// cone already gone). Doing it here is what lets the acceptance predicate
/// see the consumption for what it is.
///
/// Deliberately narrow on both axes: only lets in the FORWARD CONE of the
/// wrapper's own result, and only pure-total values (never an effectful
/// computation, and never the wrapper call itself). A body with a directly
/// dead consumption -- every already-correct chain -- has an empty cone
/// and comes out untouched.
fn prune_dead_wrapper_cone(b: &mut Block, wrapper_fid: FunId, program: &Program) {
    let seeds = wrapper_let_binders(b, wrapper_fid);
    if seeds.is_empty() {
        return;
    }
    let cone = forward_cone(b, &seeds);
    loop {
        let uses = crate::stage_06_let_inline::use_count::count_uses(b);
        let mut pass = ConePrune {
            cone: &cone,
            uses: &uses,
            wrapper: wrapper_fid,
            program,
            removed: false,
        };
        crate::ir::visit::MutVisitor::visit_block_mut(&mut pass, b);
        if !pass.removed {
            break;
        }
    }
}

/// Vars whose value derives (transitively) from one of `seeds`.
fn forward_cone(b: &Block, seeds: &[crate::ir::VarId]) -> BTreeSet<crate::ir::VarId> {
    use crate::ir::visit::{walk_stmt_default, Visitor};
    struct Edges {
        out: Vec<(Vec<crate::ir::VarId>, BTreeSet<crate::ir::VarId>)>,
    }
    impl Visitor for Edges {
        fn visit_stmt(&mut self, s: &Stmt) {
            if let Stmt::Let { pattern, value } = s {
                let bound: Vec<crate::ir::VarId> = pattern.iter().flatten().cloned().collect();
                if !bound.is_empty() {
                    self.out.push((
                        bound,
                        crate::ir::analysis::free_vars::free_vars_of_expr(value),
                    ));
                }
            }
            walk_stmt_default(self, s);
        }
    }
    let mut edges = Edges { out: Vec::new() };
    edges.visit_block(b);
    let mut cone: BTreeSet<crate::ir::VarId> = seeds.iter().cloned().collect();
    loop {
        let mut grew = false;
        for (bound, used) in &edges.out {
            if used.iter().any(|u| cone.contains(u)) {
                for v in bound {
                    grew |= cone.insert(v.clone());
                }
            }
        }
        if !grew {
            break;
        }
    }
    cone
}

struct ConePrune<'a> {
    cone: &'a BTreeSet<crate::ir::VarId>,
    uses: &'a crate::stage_06_let_inline::use_count::UseCount,
    wrapper: FunId,
    program: &'a Program,
    removed: bool,
}

impl crate::ir::visit::MutVisitor for ConePrune<'_> {
    fn visit_block_mut(&mut self, b: &mut Block) {
        let old = std::mem::take(&mut b.stmts);
        for s in old {
            let drop_it = match &s {
                Stmt::Let { pattern, value } => {
                    let bound: Vec<&crate::ir::VarId> = pattern.iter().flatten().collect();
                    !bound.is_empty()
                        && !matches!(value, Expr::Call { fun, .. } if *fun == self.wrapper)
                        && bound.iter().all(|v| {
                            self.cone.contains(*v)
                                && self.uses.get(v) == 0
                                && !self.uses.has_borrow_use(v)
                        })
                        && crate::stage_06_let_inline::effects_predicate::is_pure_total(
                            value,
                            self.program,
                        )
                }
                Stmt::Eval(_) => false,
            };
            if drop_it {
                self.removed = true;
            } else {
                b.stmts.push(s);
            }
        }
        crate::ir::visit::walk_block_mut_default(self, b);
    }
}

/// `let v = P(args)` -> `Eval(P(args))` for every consumption of the
/// labeled-block wrapper. Only called on hosts whose every `P` binding was
/// proved dead by `find_labeled_block_loop_chains`.
fn demote_dead_wrapper_lets(b: &mut Block, wrapper_fid: FunId) {
    struct Demote {
        wrapper: FunId,
    }
    impl crate::ir::visit::MutVisitor for Demote {
        fn visit_stmt_mut(&mut self, s: &mut Stmt) {
            let hit = matches!(
                s,
                Stmt::Let {
                    pattern,
                    value: Expr::Call { fun, .. },
                } if pattern.len() == 1 && pattern[0].is_some() && *fun == self.wrapper
            );
            if hit {
                if let Stmt::Let { value, .. } = s {
                    *s = Stmt::Eval(std::mem::replace(value, Expr::Unit));
                }
            }
            crate::ir::visit::walk_stmt_mut_default(self, s);
        }
    }
    use crate::ir::visit::MutVisitor as _;
    Demote {
        wrapper: wrapper_fid,
    }
    .visit_block_mut(b);
}

/// One past the highest `__c_<n>` already bound in `b`. A second splice
/// pass over an already-spliced body restarts its own counter at 0, which
/// would mint a binding shadowing the first pass's -- the hosts this pass
/// fixes are precisely the ones that already carry a `__c_0`.
fn next_abort_var_suffix(b: &Block) -> u32 {
    use crate::ir::visit::Visitor;
    struct MaxSuffix {
        max: Option<u32>,
    }
    impl Visitor for MaxSuffix {
        fn visit_var(&mut self, v: &crate::ir::VarId) {
            if let Some(n) = v
                .as_ref()
                .strip_prefix("__c_")
                .and_then(|s| s.parse::<u32>().ok())
            {
                self.max = Some(self.max.map_or(n, |m: u32| m.max(n)));
            }
        }
    }
    let mut scan = MaxSuffix { max: None };
    scan.visit_block(b);
    scan.max.map_or(0, |n| n + 1)
}

fn empty_block() -> Block {
    Block {
        stmts: vec![],
        tail: BlockTail::Value(Expr::Unit),
    }
}

/// Discover labeled-block loop chains WRAPPER-first.
///
/// The original scan was consumer-first and keyed on one rigid shape: the
/// dead `let v = P(args)` had to be the LAST TOP-LEVEL statement of a
/// `Spec(Aborts)` body. That misses two whole classes. When an abortable
/// callee precedes the labeled block, `materialise` wraps the remainder in
/// `match <callee>.aborts { NoAbort => { .. } }` and the `let` lands one
/// level down inside that arm; and when the labeled block sits after an
/// extracted loop, the host is a Synthetic `LoopAfter`, not the
/// `Spec(Aborts)` fn at all. In both cases the pass declined and the
/// untransformed VALUE loop shipped under an `.aborts.` name.
///
/// So: enumerate the WRAPPERS by shape, then accept one only when EVERY
/// call site anywhere in the program is a dead single-binding
/// `let v = P(args)` inside an `AbortResult`-returning `.aborts`-family
/// function. A LIVE consumption (the result is read) needs the
/// accumulator threaded rather than deadened -- a different
/// transformation -- so it disqualifies the whole chain instead of
/// half-converting it.
///
/// Returns owned descriptors so the caller can mutate the program freely.
fn find_labeled_block_loop_chains(
    program: &Program,
    aborts_map: &AbortsMap,
    abort_result_ty: &Type,
) -> Vec<LabeledLoopChain> {
    // 1. Candidate wrappers, by shape alone.
    let mut candidates: BTreeMap<FunId, (FunId, FunId)> = BTreeMap::new();
    for (wrapper_fid, p_fn) in program.functions.iter() {
        if !matches!(p_fn.kind, FunctionKind::Synthetic) {
            continue;
        }
        if !p_fn.body.stmts.is_empty() {
            continue;
        }
        if !crate::ir::names::is_aborts_family_name(&p_fn.name) {
            continue;
        }
        // Already `AbortResult`-typed means either a chain a prior pass
        // converted or a labeled block whose value genuinely IS an abort
        // verdict. Deadening either one would destroy a correct result;
        // this pass exists only to convert ACCUMULATOR-typed chains.
        if p_fn.signature.return_type == *abort_result_ty {
            continue;
        }
        let BlockTail::Value(Expr::Call { fun: loop_fid, .. }) = &p_fn.body.tail else {
            continue;
        };
        let loop_fid = *loop_fid;
        let Some(l_fn) = program.functions.get(&loop_fid) else {
            continue;
        };
        let FunctionKind::LoopBody { parent, slot } = l_fn.kind else {
            continue;
        };
        if parent != *wrapper_fid {
            continue;
        }
        // Sibling LoopAfter A (same parent + slot).
        let Some(after_fid) = program.functions.iter().find_map(|(id, af)| {
            matches!(af.kind, FunctionKind::LoopAfter { parent: p, slot: s }
                if p == *wrapper_fid && s == slot)
            .then_some(*id)
        }) else {
            continue;
        };
        // Gate: only fire when the loop actually DROPS a callee-abort, so
        // abort-free labeled loops (already-correct NoAbort) stay untouched.
        if !loop_chain_has_dropped_abort(program, aborts_map, loop_fid, after_fid) {
            continue;
        }
        candidates.insert(*wrapper_fid, (loop_fid, after_fid));
    }
    if candidates.is_empty() {
        return Vec::new();
    }

    // 2. Every call site of every candidate, anywhere in the program.
    //    A chain is accepted only if `accepted == total`, so one live or
    //    otherwise unrecognised site vetoes the whole chain.
    let mut total: BTreeMap<FunId, usize> = BTreeMap::new();
    let mut accepted: BTreeMap<FunId, usize> = BTreeMap::new();
    let mut hosts: BTreeMap<FunId, BTreeSet<FunId>> = BTreeMap::new();
    let candidate_ids: BTreeSet<FunId> = candidates.keys().copied().collect();
    for (host_fid, h) in program.functions.iter() {
        let calls = count_calls_to(&h.body, &candidate_ids);
        if calls.is_empty() {
            continue;
        }
        for (wrapper, n) in &calls {
            *total.entry(*wrapper).or_default() += n;
        }
        // The splice injects `Return(Aborted ..)`, so a host that does not
        // already return `AbortResult` cannot host it -- and a function
        // outside the `.aborts` family has no abort verdict to propagate.
        let host_ok = crate::ir::names::is_aborts_family_name(&h.name)
            && h.signature.return_type == *abort_result_ty;
        if !host_ok {
            continue;
        }
        // Deadness is judged AFTER pruning the wrapper's own dead cone --
        // the `no_pending_or_active_duplicates_*` family reads the result
        // through two derived bindings that are themselves dead. The probe
        // runs on a clone; `splice_wrapper_consumption` re-runs the same
        // prune on the real body for every accepted chain.
        for wrapper in calls.keys() {
            let mut probe = h.body.clone();
            prune_dead_wrapper_cone(&mut probe, *wrapper, program);
            let uses = crate::stage_06_let_inline::use_count::count_uses(&probe);
            let sites = wrapper_let_binders(&probe, *wrapper);
            if sites.is_empty() {
                continue;
            }
            if sites
                .iter()
                .all(|v| uses.get(v) == 0 && !uses.has_borrow_use(v))
            {
                *accepted.entry(*wrapper).or_default() += sites.len();
                hosts.entry(*wrapper).or_default().insert(*host_fid);
            }
        }
    }

    candidates
        .into_iter()
        .filter_map(|(wrapper_fid, (loop_fid, after_fid))| {
            let n = *accepted.get(&wrapper_fid).unwrap_or(&0);
            if n == 0 || n != *total.get(&wrapper_fid).unwrap_or(&0) {
                return None;
            }
            Some(LabeledLoopChain {
                wrapper_fid,
                loop_fid,
                after_fid,
                hosts: hosts
                    .get(&wrapper_fid)
                    .map(|s| s.iter().copied().collect())
                    .unwrap_or_default(),
            })
        })
        .collect()
}

/// Count `Call(t, ..)` occurrences per target across a body, at any
/// depth and in any position.
pub(super) fn count_calls_to(b: &Block, targets: &BTreeSet<FunId>) -> BTreeMap<FunId, usize> {
    use crate::ir::visit::{walk_expr_default, Visitor};
    struct Count<'a> {
        targets: &'a BTreeSet<FunId>,
        out: BTreeMap<FunId, usize>,
    }
    impl Visitor for Count<'_> {
        fn visit_expr(&mut self, e: &Expr) {
            if let Expr::Call { fun, .. } = e {
                if self.targets.contains(fun) {
                    *self.out.entry(*fun).or_default() += 1;
                }
            }
            walk_expr_default(self, e);
        }
    }
    let mut c = Count {
        targets,
        out: BTreeMap::new(),
    };
    c.visit_block(b);
    c.out
}

/// True iff `L` or `A` calls any function with an `.aborts` companion
/// (an `aborts_map` KEY) -- a callee-abort that the accumulator typing
/// would otherwise drop. The wrapper/loop/after self-calls are Synthetic
/// helpers, never `aborts_map` keys, so they never false-trigger.
pub(super) fn loop_chain_has_dropped_abort(
    program: &Program,
    aborts_map: &AbortsMap,
    loop_fid: FunId,
    after_fid: FunId,
) -> bool {
    use crate::ir::visit::{walk_expr_default, Visitor};
    struct C<'a> {
        program: &'a Program,
        aborts_map: &'a AbortsMap,
        found: bool,
    }
    impl Visitor for C<'_> {
        fn visit_expr(&mut self, e: &Expr) {
            if let Expr::Call { fun, .. } = e {
                if self.aborts_map.contains_key(fun) && callee_can_abort(self.program, *fun) {
                    self.found = true;
                }
            }
            walk_expr_default(self, e);
        }
    }
    let mut c = C {
        program,
        aborts_map,
        found: false,
    };
    for fid in [loop_fid, after_fid] {
        if let Some(f) = program.functions.get(&fid) {
            c.visit_block(&f.body);
        }
    }
    c.found
}

/// What the ACCUMULATOR leaves of a retyped loop chain become.
///
/// Both phases that retype a labeled-block loop chain to `AbortResult`
/// walk the same shapes -- loop self-call, exit-to-`.after` call,
/// callee-abort `Match`, accumulator leaf -- and differ only in what a
/// leaf CARRYING the accumulator turns into. One walker, two leaf
/// actions: a second copy of the traversal is what let phase 3a.5b and
/// its siblings drift apart in the first place.
pub(super) enum AccumulatorLeaf<'a> {
    /// Phase 3a.5b: every consumption is dead, so a leaf carries no
    /// information -- it collapses to `NoAbort`, and a tail-position
    /// abortable call collapses to its own abort verdict.
    Deaden,
    /// Phase 3b.5b: the accumulator is consumed LIVE, so a leaf becomes
    /// `cont(prefix.., leaf)`.
    Continue {
        cont: FunId,
        type_args: &'a [Type],
        prefix: &'a [Expr],
        /// ANF-lift a tail-position abortable call into its own `let`
        /// before wrapping. Set only for a body the callee-aborts splice
        /// is about to run over: the splice detects triggers in STATEMENT
        /// position only, so the lift is what lets it guard a call whose
        /// VALUE the accumulator still needs (`Deaden` can just swap the
        /// callee for its `.aborts`; a live leaf cannot).
        anf_lift_abortable_call: bool,
    },
}

/// Convert a loop/after block to its `AbortResult`-propagating form.
/// Preserves the loop self-call (`self_fid`) and the exit-to-after call
/// (`after_fid`); rewrites every other leaf per `leaf` so the block
/// delivers `AbortResult`.
pub(super) fn retype_loop_accumulator_leaves(
    b: &mut Block,
    self_fid: FunId,
    after_fid: FunId,
    types: &AbortsTypeIds,
    aborts_map: &AbortsMap,
    leaf: &AccumulatorLeaf<'_>,
    next_tmp: &mut u32,
) {
    // Stmts are left untouched -- the callee-abort splice (run right after
    // this pass) threads their triggers.
    let value_tail_is_leaf = match &b.tail {
        BlockTail::Value(e) => {
            !matches!(e, Expr::If { .. } | Expr::Match { .. })
                && !matches!(e, Expr::Call { fun, .. } if *fun == self_fid || *fun == after_fid)
        }
        _ => false,
    };
    if value_tail_is_leaf {
        apply_value_leaf(b, types, aborts_map, leaf, next_tmp);
        return;
    }
    match &mut b.tail {
        BlockTail::Value(Expr::If {
            then_branch,
            else_branch,
            ..
        }) => {
            retype_loop_accumulator_leaves(
                then_branch,
                self_fid,
                after_fid,
                types,
                aborts_map,
                leaf,
                next_tmp,
            );
            retype_loop_accumulator_leaves(
                else_branch,
                self_fid,
                after_fid,
                types,
                aborts_map,
                leaf,
                next_tmp,
            );
        }
        BlockTail::Value(Expr::Match {
            struct_id, cases, ..
        }) if *struct_id == types.option => {
            // A callee-abort result match (`match g.aborts { NoAbort => cont,
            // Aborted p => exit }`). Rewrite the NoAbort continuation; make
            // the Aborted arm re-propagate its bound payload. Replacing the
            // Aborted arm WHOLESALE is also what discharges
            // `labeled_block_extract`'s fabricated `Abort { code: 0 }`
            // placeholder -- that arm only exists because the accumulator
            // typing had no way to express "aborted".
            for arm in cases.iter_mut() {
                if arm.variant == OPTION_NONE_TAG {
                    retype_loop_accumulator_leaves(
                        &mut arm.body,
                        self_fid,
                        after_fid,
                        types,
                        aborts_map,
                        leaf,
                        next_tmp,
                    );
                } else if arm.variant == OPTION_SOME_TAG {
                    let payload = arm.bindings.first().cloned();
                    arm.body = Box::new(Block {
                        stmts: vec![],
                        tail: BlockTail::Value(match payload {
                            Some(p) => aborted_of(types, p),
                            None => types.make_none(),
                        }),
                    });
                }
            }
        }
        BlockTail::Value(Expr::Match { cases, .. }) => {
            // A user-value match: every arm delivers the accumulator.
            for arm in cases.iter_mut() {
                retype_loop_accumulator_leaves(
                    &mut arm.body,
                    self_fid,
                    after_fid,
                    types,
                    aborts_map,
                    leaf,
                    next_tmp,
                );
            }
        }
        // Loop self-call (continue) or exit-to-after: both retyped to
        // AbortResult, so pass through unchanged.
        BlockTail::Value(_) => {}
        BlockTail::Return(_) => {
            // A value-carrying labeled exit (the `find_index!` "found"
            // path `Return(some(i))`), or -- at the function tail of an
            // `.after` -- the labeled block's natural exit value.
            apply_return_leaf(b, types, aborts_map, leaf, next_tmp);
        }
        BlockTail::Abort { code } => {
            let code_expr = std::mem::replace(code.as_mut(), Expr::Unit);
            b.tail = BlockTail::Value(types.make_some(code_expr));
        }
        // Break/Continue/ReturnFromBlock do not survive loop_extract in an
        // extracted loop body; leave any stray one untouched.
        _ => {}
    }
}

fn apply_value_leaf(
    b: &mut Block,
    types: &AbortsTypeIds,
    aborts_map: &AbortsMap,
    leaf: &AccumulatorLeaf<'_>,
    next_tmp: &mut u32,
) {
    match leaf {
        AccumulatorLeaf::Deaden => {
            let BlockTail::Value(e) = &mut b.tail else {
                unreachable!("caller classified this tail as a value leaf");
            };
            // A callee with an `.aborts` companion at a tail-value
            // position: propagate its abort verdict directly.
            if let Expr::Call { fun, .. } = e {
                if let Some(&aborts_fid) = aborts_map.get(fun) {
                    *fun = aborts_fid;
                    return;
                }
            }
            // Any other accumulator leaf (a pack/var/const value) is dead.
            *e = types.make_none();
        }
        AccumulatorLeaf::Continue { .. } => {
            let BlockTail::Value(acc) =
                std::mem::replace(&mut b.tail, BlockTail::Value(Expr::Unit))
            else {
                unreachable!("caller classified this tail as a value leaf");
            };
            let wrapped = continue_leaf(acc, &mut b.stmts, aborts_map, leaf, next_tmp);
            b.tail = BlockTail::Value(wrapped);
        }
    }
}

fn apply_return_leaf(
    b: &mut Block,
    types: &AbortsTypeIds,
    aborts_map: &AbortsMap,
    leaf: &AccumulatorLeaf<'_>,
    next_tmp: &mut u32,
) {
    match leaf {
        AccumulatorLeaf::Deaden => {
            let BlockTail::Return(value) = &mut b.tail else {
                unreachable!("caller matched a Return tail");
            };
            if let Expr::Call { fun, .. } = value.as_mut() {
                if let Some(&aborts_fid) = aborts_map.get(fun) {
                    *fun = aborts_fid;
                    return;
                }
            }
            *value = Box::new(types.make_none());
        }
        AccumulatorLeaf::Continue { .. } => {
            let BlockTail::Return(acc) =
                std::mem::replace(&mut b.tail, BlockTail::Value(Expr::Unit))
            else {
                unreachable!("caller matched a Return tail");
            };
            let wrapped = continue_leaf(*acc, &mut b.stmts, aborts_map, leaf, next_tmp);
            // Keep the early-exit form: in a nested arm a `Return` exits the
            // FUNCTION, and demoting it to a `Value` would instead hand the
            // continuation's verdict to the enclosing expression.
            b.tail = BlockTail::Return(Box::new(wrapped));
        }
    }
}

fn continue_leaf(
    acc: Expr,
    stmts: &mut Vec<Stmt>,
    aborts_map: &AbortsMap,
    leaf: &AccumulatorLeaf<'_>,
    next_tmp: &mut u32,
) -> Expr {
    let AccumulatorLeaf::Continue {
        cont,
        type_args,
        prefix,
        anf_lift_abortable_call,
    } = leaf
    else {
        unreachable!("caller selected the Continue action");
    };
    let acc = if *anf_lift_abortable_call
        && matches!(&acc, Expr::Call { fun, .. } if aborts_map.contains_key(fun))
    {
        let tmp: crate::ir::VarId = format!("__la_v{next_tmp}").into();
        *next_tmp += 1;
        stmts.push(Stmt::Let {
            pattern: vec![Some(tmp.clone())],
            value: acc,
        });
        Expr::Var(tmp)
    } else {
        acc
    };
    let mut args: Vec<Expr> = prefix.to_vec();
    args.push(acc);
    Expr::Call {
        fun: *cont,
        type_args: type_args.to_vec(),
        args,
    }
}

/// `Aborted(<payload>) : AbortResult` where `payload` already holds a
/// `MoveAbortCode` (the bound Some-arm value) -- so this re-wraps it in
/// `Some(..)` WITHOUT the extra `MoveAbortCode {..}` layer `make_some`
/// would add.
fn aborted_of(types: &AbortsTypeIds, payload: crate::ir::VarId) -> Expr {
    Expr::Pack {
        struct_id: types.option,
        type_args: vec![types.abort_code_type()],
        variant: Some(OPTION_SOME_TAG),
        fields: vec![Expr::Var(payload)],
    }
}

// ---------------------------------------------------------------------------
// Body walker
// ---------------------------------------------------------------------------

/// Walk a Block applying the per-tail rewrites.
fn rewrite_block(
    b: &mut Block,
    types: &AbortsTypeIds,
    aborts_map: &AbortsMap,
    is_function_tail: bool,
) {
    for s in b.stmts.iter_mut() {
        rewrite_stmt(s, types, aborts_map);
    }
    rewrite_tail(&mut b.tail, types, aborts_map, is_function_tail);
}

fn rewrite_stmt(s: &mut Stmt, types: &AbortsTypeIds, aborts_map: &AbortsMap) {
    match s {
        Stmt::Let { value, .. } => rewrite_expr(value, types, aborts_map),
        Stmt::Eval(e) => rewrite_expr(e, types, aborts_map),
    }
}

fn rewrite_tail(
    t: &mut BlockTail,
    types: &AbortsTypeIds,
    aborts_map: &AbortsMap,
    is_function_tail: bool,
) {
    match t {
        BlockTail::Value(e) => {
            if is_function_tail {
                rewrite_function_tail_value(e, types, aborts_map);
                if !is_if_or_match(e) {
                    *t = BlockTail::Value(types.make_none());
                }
            } else {
                rewrite_expr(e, types, aborts_map);
            }
        }
        BlockTail::Return(value) => {
            // Substitute Return(Call(g, args)) -> Return(Call(g.aborts, args))
            // when g has an .aborts companion. The Return now carries
            // AbortResult and downstream return_collapse converts it
            // to Value at function-tail position.
            if let Expr::Call { fun, .. } = value.as_mut() {
                if let Some(&aborts_fid) = aborts_map.get(fun) {
                    *fun = aborts_fid;
                    rewrite_expr(value, types, aborts_map);
                    return;
                }
            }
            if is_function_tail {
                rewrite_function_tail_value(value, types, aborts_map);
                if !is_if_or_match(value) {
                    *t = BlockTail::Return(Box::new(types.make_none()));
                }
            } else {
                rewrite_expr(value, types, aborts_map);
                *t = BlockTail::Return(Box::new(types.make_none()));
            }
        }
        BlockTail::Abort { code } => {
            // Recurse into the code expression for nested rewrites,
            // then lift the code into Some(...) and re-shape as
            // Return.
            rewrite_expr(code, types, aborts_map);
            let code_expr = std::mem::replace(code.as_mut(), Expr::Unit);
            *t = BlockTail::Return(Box::new(types.make_some(code_expr)));
        }
        BlockTail::Break { value, .. } | BlockTail::Continue { value, .. } => {
            rewrite_expr(value, types, aborts_map);
        }
        BlockTail::ReturnFromBlock { value, .. } => {
            // Substitute Return(Call(g, args)) -> Return(Call(g.aborts, args))
            // when g has an .aborts companion. The Return now carries
            // AbortResult and downstream return_collapse converts it
            // to Value at function-tail position.
            if let Expr::Call { fun, .. } = value.as_mut() {
                if let Some(&aborts_fid) = aborts_map.get(fun) {
                    *fun = aborts_fid;
                    rewrite_expr(value, types, aborts_map);
                    return;
                }
            }
            if is_function_tail {
                rewrite_function_tail_value(value, types, aborts_map);
                if !is_if_or_match(value) {
                    *t = BlockTail::Return(Box::new(types.make_none()));
                }
            } else {
                // RFB at inner-block level: preserve the RFB shape.
                // Exiting the labeled_block hands control back to the
                // code AFTER the labeled_block in the surrounding
                // function body, which still needs to run. Converting
                // to Return(None) would skip that post-labeled-block
                // code entirely.
                rewrite_expr(value, types, aborts_map);
            }
        }
    }
}

/// `true` iff `e` is an `Expr::If` or `Expr::Match`. Used by
/// `rewrite_tail` to decide whether the function-tail Value can be
/// preserved (its arm leaves rewritten to Option) or must be
/// collapsed to `Value(None)`.
fn is_if_or_match(e: &Expr) -> bool {
    matches!(e, Expr::If { .. } | Expr::Match { .. })
}

/// At function-tail position, recursively convert arm tails of an
/// If/Match (and nested If/Match within Value arms) so each arm
/// contributes an `Option<MoveAbortCode>` value. Stmt-level
/// rewrites (`rewrite_stmt`) are applied to each arm's stmts so
/// nested splices and assert lifts run on them.
///
/// - `Value(complex_T)` at an arm tail: if `complex_T` is itself
///   an If/Match, recurse into it. Otherwise replace with
///   `Value(None)` (this leaf path didn't abort).
/// - `Abort { code }` at an arm tail: replace with
///   `Value(Some(code))` (this leaf path aborted with `code`).
/// - `Return(_)` / `Break` / `Continue`: leave alone -- handled by
///   downstream passes.
fn rewrite_function_tail_value(e: &mut Expr, types: &AbortsTypeIds, aborts_map: &AbortsMap) {
    match e {
        Expr::If {
            cond: _,
            then_branch,
            else_branch,
        } => {
            rewrite_function_tail_block(then_branch, types, aborts_map);
            rewrite_function_tail_block(else_branch, types, aborts_map);
        }
        Expr::Match { cases, .. } => {
            for arm in cases.iter_mut() {
                rewrite_function_tail_block(&mut arm.body, types, aborts_map);
            }
        }
        // Anything else: treat as a leaf -- caller will collapse the
        // surrounding Value(_) to Value(None) instead.
        _ => {}
    }
}

fn rewrite_function_tail_block(b: &mut Block, types: &AbortsTypeIds, aborts_map: &AbortsMap) {
    for s in b.stmts.iter_mut() {
        rewrite_stmt(s, types, aborts_map);
    }
    match &mut b.tail {
        BlockTail::Value(inner) => {
            if is_if_or_match(inner) {
                rewrite_function_tail_value(inner, types, aborts_map);
            } else {
                rewrite_expr(inner, types, aborts_map);
                b.tail = BlockTail::Value(types.make_none());
            }
        }
        BlockTail::Abort { code } => {
            rewrite_expr(code, types, aborts_map);
            let code_expr = std::mem::replace(code.as_mut(), Expr::Unit);
            b.tail = BlockTail::Value(types.make_some(code_expr));
        }
        BlockTail::Return(value) => {
            // Same substitution as in `rewrite_tail`. Return(Var) is
            // also preserved (the var may already hold an AbortResult
            // from a splice).
            if let Expr::Call { fun, .. } = value.as_mut() {
                if let Some(&aborts_fid) = aborts_map.get(fun) {
                    *fun = aborts_fid;
                    rewrite_expr(value, types, aborts_map);
                    return;
                }
            }
            rewrite_expr(value, types, aborts_map);
            b.tail = BlockTail::Return(Box::new(types.make_none()));
        }
        BlockTail::Break { value, .. } | BlockTail::Continue { value, .. } => {
            rewrite_expr(value, types, aborts_map);
        }
        BlockTail::ReturnFromBlock { value, .. } => {
            // Same substitution as in `rewrite_tail`. Return(Var) is
            // also preserved (the var may already hold an AbortResult
            // from a splice).
            if let Expr::Call { fun, .. } = value.as_mut() {
                if let Some(&aborts_fid) = aborts_map.get(fun) {
                    *fun = aborts_fid;
                    rewrite_expr(value, types, aborts_map);
                    return;
                }
            }
            rewrite_expr(value, types, aborts_map);
            b.tail = BlockTail::Return(Box::new(types.make_none()));
        }
    }
}

fn rewrite_expr(e: &mut Expr, types: &AbortsTypeIds, aborts_map: &AbortsMap) {
    match e {
        Expr::Borrow { step, base } => {
            for __pe in step.exprs_mut() {
                rewrite_expr(__pe, types, aborts_map);
            }
            rewrite_expr(base, types, aborts_map);
        }
        Expr::Update { step, base, value } => {
            for __pe in step.exprs_mut() {
                rewrite_expr(__pe, types, aborts_map);
            }
            rewrite_expr(base, types, aborts_map);
            rewrite_expr(value, types, aborts_map);
        }
        Expr::Var(_)
        | Expr::Const(_)
        | Expr::Unit
        | Expr::BorrowLoc(_)
        | Expr::BorrowGlobal(_)
        | Expr::WriteBack { .. }
        | Expr::IsParent { .. } => {}
        Expr::BinOp { lhs, rhs, .. } => {
            rewrite_expr(lhs, types, aborts_map);
            rewrite_expr(rhs, types, aborts_map);
        }
        Expr::UnOp { operand, .. } => rewrite_expr(operand, types, aborts_map),
        Expr::BitOp(op) => match op {
            BitOp::Extract { operand, .. }
            | BitOp::ZeroExtend { operand, .. }
            | BitOp::SignExtend { operand, .. } => rewrite_expr(operand, types, aborts_map),
            BitOp::Concat { high, low } => {
                rewrite_expr(high, types, aborts_map);
                rewrite_expr(low, types, aborts_map);
            }
        },
        Expr::Call { args, .. } | Expr::Tuple(args) | Expr::Pack { fields: args, .. } => {
            for a in args {
                rewrite_expr(a, types, aborts_map);
            }
        }
        Expr::Unpack { value, .. }
        | Expr::Field { base: value, .. }
        | Expr::ReadRef(value)
        | Expr::ToProp(value)
        | Expr::ToBool(value) => rewrite_expr(value, types, aborts_map),
        Expr::If {
            cond,
            then_branch,
            else_branch,
        } => {
            rewrite_expr(cond, types, aborts_map);
            rewrite_block(
                then_branch,
                types,
                aborts_map,
                /* is_function_tail = */ false,
            );
            rewrite_block(
                else_branch,
                types,
                aborts_map,
                /* is_function_tail = */ false,
            );
        }
        Expr::Match {
            selector, cases, ..
        } => {
            rewrite_expr(selector, types, aborts_map);
            for arm in cases.iter_mut() {
                rewrite_block(
                    &mut arm.body,
                    types,
                    aborts_map,
                    /* is_function_tail = */ false,
                );
            }
        }
        Expr::While {
            header,
            cond,
            body,
            iter_locals,
            header_exit_locals: _,
            live_out: _,
        } => {
            for (_, init) in iter_locals.iter_mut() {
                rewrite_expr(init, types, aborts_map);
            }
            rewrite_block(
                header, types, aborts_map, /* is_function_tail = */ false,
            );
            rewrite_expr(cond, types, aborts_map);
            rewrite_block(body, types, aborts_map, /* is_function_tail = */ false);
        }
        Expr::WriteRef { reference, value } => {
            rewrite_expr(reference, types, aborts_map);
            rewrite_expr(value, types, aborts_map);
        }
        Expr::Quantifier { domain, body, .. } => {
            match domain {
                QuantDomain::Unbounded => {}
                QuantDomain::Range { start, end } => {
                    rewrite_expr(start, types, aborts_map);
                    rewrite_expr(end, types, aborts_map);
                }
                QuantDomain::Collection(c) => rewrite_expr(c, types, aborts_map),
                QuantDomain::VecRange { vec, start, end } => {
                    rewrite_expr(vec, types, aborts_map);
                    rewrite_expr(start, types, aborts_map);
                    rewrite_expr(end, types, aborts_map);
                }
            }
            rewrite_block(body, types, aborts_map, /* is_function_tail = */ false);
        }
        Expr::LabeledBlock { body, .. } => rewrite_block(body, types, aborts_map, false),
    }
}

// ---------------------------------------------------------------------------
// Slice 2: sub-expression splices
// ---------------------------------------------------------------------------

/// Per-splice mutable context. `next_var_suffix` produces unique
/// `__c_N` bindings so multiple splices in the same body don't
/// collide.
///
/// `inside_loop_body` is set while recursing into a `While`'s body
/// (via `splice_callee_aborts_in_expr`). When set, the splice
/// walker skips trigger detection — any abort triggers buried inside
/// the loop body are left alone. This preserves the iter-locals-
/// tuple shape that `loop_extract` requires at the loop body's
/// outermost tail; without it, the splice would rewrite the tail to
/// a `Match{...}` expression and arity-mismatch the loop helper's
/// recursive Call.
///
/// Abort precision is recovered later: phase 2's loop_extract
/// emits `LoopBody`/`LoopAfter` helper functions, and any
/// follow-up pass that materialises `.aborts` for those helpers
/// would catch the triggers there (the helper bodies don't have
/// the implicit-continue convention to preserve).
struct SpliceCtx<'a> {
    aborts_map: &'a AbortsMap,
    types: &'a AbortsTypeIds,
    program: &'a Program,
    next_var_suffix: u32,
    inside_loop_body: bool,
    /// Pre-computed var → type map for the source function body.
    /// Used by the `BorrowMapKey` trigger detection to resolve the
    /// `base` expression's parent type, which is required to
    /// construct the synthesised native abort-check call's type args.
    /// Under SSA every var is bound once so a single linear pass
    /// suffices; we don't reset across nested blocks.
    scope: BTreeMap<crate::ir::VarId, crate::ir::Type>,
    /// When set, the ONLY trigger the walker recognises is a
    /// statement-position `Call` to this exact callee.
    ///
    /// Used by phase 3a.5b, which re-runs this splice over a body
    /// `materialise` already spliced once. Without the restriction every
    /// preserved `let x = g(args)` would re-trigger, and so would every
    /// synthesised `Borrow` guard (those resolve through `program`, not
    /// `aborts_map`, so narrowing the map alone would not stop them) --
    /// double-guarding what is already guarded.
    only_callee: Option<FunId>,
}

impl<'a> SpliceCtx<'a> {
    fn fresh_abort_var(&mut self) -> crate::ir::VarId {
        let name = format!("__c_{}", self.next_var_suffix);
        self.next_var_suffix += 1;
        crate::ir::VarId::from(name)
    }
}

/// Pre-compute `var -> type` for every binding reachable from the
/// function body. Under SSA each var is bound exactly once so a
/// single linear walk records every entry. Used by the splice
/// walker to resolve `Expr::BorrowMapKey { base, .. }`'s base type
/// when synthesising the abort-check Call.
pub(super) fn collect_function_var_types(
    func: &Function,
    program: &Program,
) -> BTreeMap<crate::ir::VarId, crate::ir::Type> {
    use crate::ir::visit::Visitor;
    let mut out: BTreeMap<crate::ir::VarId, crate::ir::Type> = func
        .signature
        .params
        .iter()
        .map(|p| (p.var.clone(), p.ty.clone()))
        .collect();

    struct W<'a> {
        out: &'a mut BTreeMap<crate::ir::VarId, crate::ir::Type>,
        program: &'a Program,
    }
    impl Visitor for W<'_> {
        // Process a block's statements in SOURCE ORDER, typing each
        // `Stmt::Let` against the accumulator earlier statements
        // populated (forward-order SSA typing), binding its pattern,
        // then recursing the value for nested blocks. Mirrors the
        // hand-rolled `collect_var_types_in_block`.
        fn visit_block(&mut self, b: &Block) {
            for stmt in &b.stmts {
                match stmt {
                    Stmt::Let { pattern, value } => {
                        let val_ty =
                            crate::ir::analysis::type_of::type_of(value, self.out, self.program)
                                .unwrap_or(crate::ir::Type::Unit);
                        bind_pattern_var_types(pattern, &val_ty, self.out);
                        self.visit_expr(value);
                    }
                    Stmt::Eval(e) => self.visit_expr(e),
                }
            }
            self.visit_tail(&b.tail);
        }

        // SELECTIVE descent: recurse only into the nested blocks of
        // `If`/`Match`/`While`, exactly as the hand-rolled
        // `collect_var_types_in_expr` did. NOT `walk_expr_default`:
        // a full descent would reach blocks nested in operand
        // positions the original skipped. The `If`/`While` conditions
        // are deliberately NOT walked (the original recursed only the
        // branch/header/body blocks).
        fn visit_expr(&mut self, e: &Expr) {
            match e {
                Expr::If {
                    then_branch,
                    else_branch,
                    ..
                } => {
                    self.visit_block(then_branch);
                    self.visit_block(else_branch);
                }
                Expr::Match { cases, .. } => {
                    for arm in cases {
                        // Match-arm bindings -- defensively typed as Unit;
                        // BorrowMapKey trigger detection doesn't depend on
                        // arm-binding types, only on existing-binding lookups
                        // for `base`.
                        for binding in &arm.bindings {
                            self.out
                                .entry(binding.clone())
                                .or_insert(crate::ir::Type::Unit);
                        }
                        self.visit_block(&arm.body);
                    }
                }
                Expr::While {
                    header,
                    body,
                    iter_locals,
                    ..
                } => {
                    for (v, init) in iter_locals {
                        let init_ty =
                            crate::ir::analysis::type_of::type_of(init, self.out, self.program)
                                .unwrap_or(crate::ir::Type::Unit);
                        self.out.entry(v.clone()).or_insert(init_ty);
                    }
                    self.visit_block(header);
                    self.visit_block(body);
                }
                _ => {}
            }
        }

        // Every tail variant recurses into its carried expression
        // (including `Abort { code }`), matching the symmetric
        // `collect_var_types_in_tail`.
        fn visit_tail(&mut self, t: &BlockTail) {
            match t {
                BlockTail::Value(e) => self.visit_expr(e),
                BlockTail::Return(e) | BlockTail::Abort { code: e } => self.visit_expr(e.as_ref()),
                BlockTail::Break { value, .. } | BlockTail::Continue { value, .. } => {
                    self.visit_expr(value.as_ref())
                }
                BlockTail::ReturnFromBlock { value, .. } => self.visit_expr(value.as_ref()),
            }
        }
    }

    let mut w = W {
        out: &mut out,
        program,
    };
    w.visit_block(&func.body);
    out
}

fn bind_pattern_var_types(
    pattern: &[Option<crate::ir::VarId>],
    val_ty: &crate::ir::Type,
    out: &mut BTreeMap<crate::ir::VarId, crate::ir::Type>,
) {
    use crate::ir::Type;
    if pattern.len() == 1 {
        if let Some(v) = &pattern[0] {
            let bound = match val_ty {
                Type::Tuple(es) if es.len() == 1 => es[0].clone(),
                other => other.clone(),
            };
            out.entry(v.clone()).or_insert(bound);
        }
        return;
    }
    if let Type::Tuple(elems) = val_ty {
        if elems.len() == pattern.len() {
            for (slot, ty) in pattern.iter().zip(elems) {
                if let Some(v) = slot {
                    out.entry(v.clone()).or_insert(ty.clone());
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Value-position abortable-callee tripwire (latent ANF gap, S6)
// ---------------------------------------------------------------------------

/// Fail-loud check for the latent ANF gap: an abortable callee `g`
/// (`g ∈ aborts_map` and `g` can abort) must never appear in a VALUE /
/// ARGUMENT position of a compound expression in a spliced `.aborts`
/// body. The callee-aborts splice ([`splice_callee_aborts_in_block`])
/// only recognises `g` in STATEMENT position -- the direct RHS of a
/// `Stmt::Let` or a bare `Stmt::Eval`. A `g` nested inside a `Call`
/// argument, a `BinOp` operand, a `Pack` field, etc. is walked past
/// with its abort verdict silently dropped, so the enclosing companion
/// would render unsoundly total.
///
/// This never happens on well-formed input: stage_06 let-inline
/// (`single_use.rs`) only inlines `is_pure_total` values into use
/// sites, and an abortable `Call` is never pure-total, so `g` always
/// stays bound to its own `Stmt::Let`. This function is the tripwire
/// that fires (via [`Stage7Error::ValuePositionAbort`]) if that
/// invariant ever regresses -- turning a silent-soundness landmine
/// into a hard error.
///
/// "Value / argument position" means: reached by descending into an
/// operand slot of a compound expression. The direct RHS of a
/// `Stmt::Let`/`Stmt::Eval` and a `BlockTail`'s carried expression are
/// STATEMENT / tail positions (handled by the splice and by
/// `rewrite_block` / `return_lift`) and are NOT flagged; nested blocks
/// (`If`/`Match`/`While` arms, `LabeledBlock`/`Quantifier` bodies) are
/// re-entered as statement contexts.
fn check_no_value_position_aborts(
    b: &Block,
    program: &Program,
    aborts_map: &AbortsMap,
) -> Result<(), Stage7Error> {
    check_block_no_value_position_aborts(b, program, aborts_map)
        .map_err(|callee| Stage7Error::ValuePositionAbort { callee })
}

/// True iff `fun` resolves to a callee whose abort axis is `Partial`
/// (it can abort). Unknown callees are treated as abortable so the
/// tripwire errs on the side of firing rather than silently passing.
pub(super) fn callee_can_abort(program: &Program, fun: FunId) -> bool {
    use crate::ir::{AbortBit, CalleeRef};
    match program.lookup_callee(fun) {
        Some(CalleeRef::Translated(f)) => f.effects.aborts == AbortBit::Partial,
        Some(CalleeRef::Native(d)) => d.effects.aborts == AbortBit::Partial,
        None => true,
    }
}

fn check_block_no_value_position_aborts(
    b: &Block,
    program: &Program,
    aborts_map: &AbortsMap,
) -> Result<(), FunId> {
    for s in &b.stmts {
        // The RHS of a Let / the Eval expr is STATEMENT position: pass
        // `nested = false` so a bare `Call(g)` there is not flagged
        // (the splice guards it), while its sub-expressions are.
        let top = match s {
            Stmt::Let { value, .. } => value,
            Stmt::Eval(e) => e,
        };
        check_expr_no_value_position_aborts(top, false, program, aborts_map)?;
    }
    // A BlockTail's carried expression is tail position (handled by
    // rewrite_block / return_lift), also `nested = false`.
    let tail_expr: &Expr = match &b.tail {
        BlockTail::Value(e) => e,
        BlockTail::Abort { code: v } => v,
        BlockTail::Return(v)
        | BlockTail::Break { value: v, .. }
        | BlockTail::Continue { value: v, .. }
        | BlockTail::ReturnFromBlock { value: v, .. } => v,
    };
    check_expr_no_value_position_aborts(tail_expr, false, program, aborts_map)
}

/// Recurse over `e`. `nested` is true when `e` itself sits in a value /
/// argument position of an enclosing compound expression. When `nested`
/// and `e` is a `Call` to an abortable callee in `aborts_map`, return
/// that callee's `FunId` as the violation. Descents into operand slots
/// pass `nested = true`; descents into nested BLOCKS restart at
/// statement context via `check_block_no_value_position_aborts`.
fn check_expr_no_value_position_aborts(
    e: &Expr,
    nested: bool,
    program: &Program,
    aborts_map: &AbortsMap,
) -> Result<(), FunId> {
    if nested {
        if let Expr::Call { fun, .. } = e {
            if aborts_map.contains_key(fun) && callee_can_abort(program, *fun) {
                return Err(*fun);
            }
        }
    }
    let rec = |sub: &Expr| check_expr_no_value_position_aborts(sub, true, program, aborts_map);
    match e {
        Expr::Var(_)
        | Expr::Const(_)
        | Expr::Unit
        | Expr::BorrowLoc(_)
        | Expr::BorrowGlobal(_)
        | Expr::WriteBack { .. }
        | Expr::IsParent { .. } => {}
        Expr::BinOp { lhs, rhs, .. } => {
            rec(lhs)?;
            rec(rhs)?;
        }
        Expr::UnOp { operand, .. } => rec(operand)?,
        Expr::BitOp(op) => match op {
            BitOp::Extract { operand, .. }
            | BitOp::ZeroExtend { operand, .. }
            | BitOp::SignExtend { operand, .. } => rec(operand)?,
            BitOp::Concat { high, low } => {
                rec(high)?;
                rec(low)?;
            }
        },
        Expr::Call { args, .. } | Expr::Tuple(args) | Expr::Pack { fields: args, .. } => {
            for a in args {
                rec(a)?;
            }
        }
        Expr::Unpack { value, .. }
        | Expr::Field { base: value, .. }
        | Expr::ReadRef(value)
        | Expr::ToProp(value)
        | Expr::ToBool(value) => rec(value)?,
        Expr::Borrow { step, base } => {
            for pe in step.exprs() {
                rec(pe)?;
            }
            rec(base)?;
        }
        Expr::Update { step, base, value } => {
            for pe in step.exprs() {
                rec(pe)?;
            }
            rec(base)?;
            rec(value)?;
        }
        Expr::WriteRef { reference, value } => {
            rec(reference)?;
            rec(value)?;
        }
        Expr::If {
            cond,
            then_branch,
            else_branch,
        } => {
            rec(cond)?;
            check_block_no_value_position_aborts(then_branch, program, aborts_map)?;
            check_block_no_value_position_aborts(else_branch, program, aborts_map)?;
        }
        Expr::Match {
            selector, cases, ..
        } => {
            rec(selector)?;
            for arm in cases {
                check_block_no_value_position_aborts(&arm.body, program, aborts_map)?;
            }
        }
        Expr::While {
            header,
            cond,
            body,
            iter_locals,
            header_exit_locals: _,
            live_out: _,
        } => {
            for (_, init) in iter_locals {
                rec(init)?;
            }
            check_block_no_value_position_aborts(header, program, aborts_map)?;
            rec(cond)?;
            check_block_no_value_position_aborts(body, program, aborts_map)?;
        }
        Expr::LabeledBlock { body, .. } => {
            check_block_no_value_position_aborts(body, program, aborts_map)?;
        }
        Expr::Quantifier { domain, body, .. } => {
            match domain {
                QuantDomain::Unbounded => {}
                QuantDomain::Range { start, end } => {
                    rec(start)?;
                    rec(end)?;
                }
                QuantDomain::Collection(c) => rec(c)?,
                QuantDomain::VecRange { vec, start, end } => {
                    rec(vec)?;
                    rec(start)?;
                    rec(end)?;
                }
            }
            check_block_no_value_position_aborts(body, program, aborts_map)?;
        }
    }
    Ok(())
}

/// Walk `b` and splice callee-aborts at every trigger site.
///
/// Triggers (in order of detection):
/// - `Stmt::Eval(Expr::Call { fun: g, args, type_args })` where
///   `g ∈ aborts_map`.
/// - `Stmt::Let { value: Expr::Call { fun: g, args, type_args }, .. }`
///   where `g ∈ aborts_map`.
///
/// For each trigger at position `i` in `b.stmts`:
/// 1. Build `Stmt::Let { pat: [__c_N], value: Call(g.aborts, args) }`.
/// 2. Steal `b.stmts[i..]` into a continuation block. For Eval
///    triggers, drop the original Eval stmt from the continuation
///    (its Call's source-T value is unused in `.aborts`). For Let
///    triggers, keep the Let in the continuation (the bound var
///    may be referenced downstream).
/// 3. Replace `b.stmts[i..]` with just the new `Let __c_N`.
/// 4. Replace `b.tail` with a `Match` on `Var(__c_N)`:
///    - None arm body = continuation block.
///    - Some arm body = `Return(Var(__c_N))` (propagate abort).
/// 5. Recurse into the None arm to splice any further triggers in
///    the continuation.
///
/// Triggers nested inside If / Match / While / etc. sub-expressions
/// are reached via the recursive walk on the original `b.stmts` and
/// `b.tail` before splicing. ANF-lifting of value-position Calls
/// (e.g. inside `BinOp { lhs: Call(g), .. }`) is NOT yet implemented;
/// such Calls slip through with their abort propagation lost
/// (under-approximation).
fn splice_callee_aborts_in_block(b: &mut Block, ctx: &mut SpliceCtx) {
    splice_callee_aborts_in_block_from(b, 0, ctx)
}

/// Walk a block looking for callee-aborts splice triggers, starting
/// at stmt index `start`. The `start` parameter handles a subtle
/// case: when we splice a Let-position trigger, the continuation
/// block preserves the original `Let { value: Call(g, args), .. }`
/// (so any downstream var references stay live). If we recursed
/// into the continuation from index 0, the preserved Let would
/// trigger the splice again — infinite recursion. Starting from
/// index 1 in that case skips the just-spliced original.
fn splice_callee_aborts_in_block_from(b: &mut Block, start: usize, ctx: &mut SpliceCtx) {
    let mut i = start;
    while i < b.stmts.len() {
        // Inside a while body's structural region, skip trigger
        // detection (see SpliceCtx::inside_loop_body comment).
        let trigger = if ctx.inside_loop_body {
            None
        } else {
            detect_callee_aborts_trigger(&b.stmts[i], ctx)
        };
        if let Some(t) = trigger {
            let skip = match &t {
                CalleeAbortsTrigger::Eval => 0,
                CalleeAbortsTrigger::Let
                | CalleeAbortsTrigger::LetBorrowMapKey { .. }
                | CalleeAbortsTrigger::LetBorrowVecIndex { .. } => 1,
            };
            do_callee_aborts_splice(b, i, t, ctx);
            // After the splice, `b.tail` is the new Match. The None
            // arm's body contains the continuation; recurse into it
            // to handle any further triggers, skipping the preserved
            // original (for Let-triggers) so we don't re-splice it.
            if let BlockTail::Value(Expr::Match { cases, .. }) = &mut b.tail {
                for arm in cases.iter_mut() {
                    if arm.variant == OPTION_NONE_TAG {
                        splice_callee_aborts_in_block_from(&mut arm.body, skip, ctx);
                    }
                }
            }
            return;
        }
        // No trigger at this stmt — recurse into its sub-expression
        // (nested If / Match / While arms may contain triggers).
        splice_callee_aborts_in_stmt(&mut b.stmts[i], ctx);
        i += 1;
    }
    splice_callee_aborts_in_tail(&mut b.tail, ctx);
}

#[derive(Clone)]
enum CalleeAbortsTrigger {
    /// `Stmt::Eval(Call(g, ...))` where `g ∈ aborts_map`. The
    /// trigger stmt's Call gets dropped from the continuation (its
    /// source-T value is unused).
    Eval,
    /// `Stmt::Let { value: Call(g, ...) }` where `g ∈ aborts_map`.
    /// The trigger stmt's Let is kept in the continuation (the
    /// bound var may be referenced downstream).
    Let,
    /// `Stmt::Let { value: BorrowMapKey { ... } }` where the base's
    /// parent is a native map with a matching abort-check companion.
    /// The synthesized `Call(<native>.aborts, args)` shape comes from
    /// this variant's fields; the trigger stmt's Let is kept in the
    /// continuation just like the Let-Call case.
    LetBorrowMapKey {
        aborts_fid: FunId,
        type_args: Vec<crate::ir::Type>,
        args: Vec<Expr>,
    },
    /// `Stmt::Let { value: Borrow { step: VecIndex(idx), base } }` --
    /// a `vector::borrow_mut(v, i)` lowered by stage 2. Synthesizes
    /// `Call(MoveVector.borrow.aborts, [base, idx])`; handled identically
    /// to `LetBorrowMapKey` (the trigger stmt's Let is kept in the
    /// continuation). See `detect_borrow_vec_index_trigger` and §55c.
    LetBorrowVecIndex {
        aborts_fid: FunId,
        type_args: Vec<crate::ir::Type>,
        args: Vec<Expr>,
    },
}

fn detect_callee_aborts_trigger(s: &Stmt, ctx: &SpliceCtx<'_>) -> Option<CalleeAbortsTrigger> {
    if let Some(only) = ctx.only_callee {
        return match s {
            Stmt::Eval(Expr::Call { fun, .. }) if *fun == only => Some(CalleeAbortsTrigger::Eval),
            Stmt::Let {
                value: Expr::Call { fun, .. },
                ..
            } if *fun == only => Some(CalleeAbortsTrigger::Let),
            _ => None,
        };
    }
    match s {
        Stmt::Eval(Expr::Call { fun, .. }) if ctx.aborts_map.contains_key(fun) => {
            Some(CalleeAbortsTrigger::Eval)
        }
        Stmt::Let {
            value: Expr::Call { fun, .. },
            ..
        } if ctx.aborts_map.contains_key(fun) => Some(CalleeAbortsTrigger::Let),
        Stmt::Let {
            value:
                Expr::Borrow {
                    step: crate::ir::path::PathStep::MapKey { .. },
                    ..
                },
            ..
        } => detect_borrow_map_key_trigger(s, ctx),
        Stmt::Let {
            value:
                Expr::Borrow {
                    step: crate::ir::path::PathStep::VecIndex(..),
                    ..
                },
            ..
        } => detect_borrow_vec_index_trigger(s, ctx),
        _ => None,
    }
}

/// Detect a `Stmt::Let { value: BorrowMapKey { .. } }` and
/// synthesise the abort-check Call for Sui-native map structs.
///
/// - `sui::table::Table`: synthesize
///   `Call(Table.borrow_mut.aborts, [base, key])` with the table's
///   `[K, V]` type arguments.
/// - `sui::bag::Bag` / `sui::object_bag::ObjectBag`: synthesize
///   `Call(<bag>.borrow.aborts, [base, key])`. These natives do not
///   expose a Lean `borrow_mut` definition; mutation renders as typed
///   `borrow` plus total `set` writeback, so the precise abort guard is
///   the typed `borrow.aborts` predicate.
///
/// Returns `None` for any BorrowMapKey whose parent isn't one of these
/// shapes, or when the relevant aborts companion FunId isn't registered.
fn detect_borrow_map_key_trigger(s: &Stmt, ctx: &SpliceCtx<'_>) -> Option<CalleeAbortsTrigger> {
    use crate::ir::Type;
    let (base, key, key_type, value_type) = match s {
        Stmt::Let {
            value:
                Expr::Borrow {
                    step:
                        crate::ir::path::PathStep::MapKey {
                            key,
                            key_type,
                            value_type,
                            df_value: _,
                        },
                    base,
                },
            ..
        } => (base.as_ref(), key.as_ref(), key_type, value_type),
        _ => return None,
    };
    // Resolve parent inner type via the precomputed scope. Only
    // handle the common `Expr::Var` case; non-Var bases (after
    // SSA / mut-to-let this is rare for BorrowMapKey at top
    // position) fall through.
    let base_var = match base {
        Expr::Var(v) => v,
        _ => return None,
    };
    let base_ty = ctx.scope.get(base_var)?;
    let parent_inner_ty = match base_ty {
        Type::MutableRef { inner, .. } => (**inner).clone(),
        Type::Reference(inner) => (**inner).clone(),
        other => other.clone(),
    };
    let (parent_sid, parent_type_args) = match &parent_inner_ty {
        Type::Struct {
            struct_id,
            type_args,
        } => (*struct_id, type_args.clone()),
        _ => return None,
    };
    let parent_struct = ctx.program.structs.get(&parent_sid)?;

    let parent_module = ctx.program.modules.get(&parent_struct.module_id)?;

    let (aborts_name, type_args) = match (
        parent_module.package_name.as_str(),
        parent_module.name.as_str(),
        parent_struct.name.as_str(),
    ) {
        ("Sui", "table", "Table") => {
            if parent_type_args.first() != Some(key_type) {
                return None;
            }
            if parent_type_args.get(1) != Some(value_type) {
                return None;
            }
            ("borrow_mut.aborts", parent_type_args)
        }
        ("Sui", "bag", "Bag") | ("Sui", "object_bag", "ObjectBag") => {
            if !parent_type_args.is_empty() {
                return None;
            }
            ("borrow.aborts", vec![key_type.clone(), value_type.clone()])
        }
        _ => return None,
    };
    let aborts_fid = ctx.program.native_id_by_name(
        &parent_module.package_name,
        &parent_module.name,
        aborts_name,
    )?;
    let args = vec![base.clone(), key.clone()];
    Some(CalleeAbortsTrigger::LetBorrowMapKey {
        aborts_fid,
        type_args,
        args,
    })
}

/// Detect a `Stmt::Let { value: Borrow { step: VecIndex(idx), base } }`
/// (a `vector::borrow_mut(v, i)` lowered by stage 2 into
/// [`crate::stage_02_ir_cfg::translate_op::BorrowNativeKind::VecIndex`])
/// and synthesise the abort-check `Call(MoveVector.borrow.aborts,
/// [base, idx])` with the vector's element type as the single type arg.
///
/// Like `Sui::bag` / `Sui::object_bag` (see `detect_borrow_map_key_trigger`),
/// `MoveStdlib::vector` exposes no Lean `borrow_mut.aborts` companion: a
/// mutable index borrow renders as `Mutation.borrowVecIndex` plus a TOTAL
/// `List.set` writeback. The precise out-of-bounds guard is therefore the
/// same `borrow.aborts` predicate the immutable `vector::borrow` uses.
/// Without this trigger the mutable borrow renders TOTAL, so `¬aborts`
/// never entails `idx < v.length` anywhere in the model (PROOF-CONVENTIONS
/// §55c; e.g. the incentive v1 claim watermark `List.set` writeback
/// no-ops out of bounds).
///
/// Returns `None` when the base isn't a vector-typed `Expr::Var` in scope,
/// or when `vector::borrow.aborts` isn't registered (the base immutable
/// `vector::borrow` native was never lifted for this program).
fn detect_borrow_vec_index_trigger(s: &Stmt, ctx: &SpliceCtx<'_>) -> Option<CalleeAbortsTrigger> {
    use crate::ir::Type;
    let (base, idx) = match s {
        Stmt::Let {
            value:
                Expr::Borrow {
                    step: crate::ir::path::PathStep::VecIndex(idx),
                    base,
                },
            ..
        } => (base.as_ref(), idx.as_ref()),
        _ => return None,
    };
    // Only the common `Expr::Var` base resolves through the precomputed
    // scope; non-Var bases fall through (matching the map-key path).
    let base_var = match base {
        Expr::Var(v) => v,
        _ => return None,
    };
    let base_ty = ctx.scope.get(base_var)?;
    let inner_ty = match base_ty {
        Type::MutableRef { inner, .. } => (**inner).clone(),
        Type::Reference(inner) => (**inner).clone(),
        other => other.clone(),
    };
    let elem_ty = match &inner_ty {
        Type::Vector(elem) => (**elem).clone(),
        _ => return None,
    };
    let aborts_fid = ctx
        .program
        .native_id_by_name("MoveStdlib", "vector", "borrow.aborts")?;
    Some(CalleeAbortsTrigger::LetBorrowVecIndex {
        aborts_fid,
        type_args: vec![elem_ty],
        args: vec![base.clone(), idx.clone()],
    })
}

fn do_callee_aborts_splice(
    b: &mut Block,
    i: usize,
    trigger: CalleeAbortsTrigger,
    ctx: &mut SpliceCtx,
) {
    // Extract the trigger stmt + everything after it.
    let trailing: Vec<Stmt> = b.stmts.drain(i..).collect();
    let trailing_tail = std::mem::replace(&mut b.tail, BlockTail::Value(Expr::Unit));

    // Resolve (aborts_fid, type_args, args) for the synthesized
    // Call. For Call-triggers (`Eval` / `Let`) these come from the
    // trigger stmt itself; for `LetBorrowMapKey` they're carried
    // on the variant by `detect_borrow_map_key_trigger`.
    let (aborts_fid, type_args, args) = match &trigger {
        CalleeAbortsTrigger::Eval | CalleeAbortsTrigger::Let => {
            let stmt = &trailing[0];
            let (callee_fid, ta, a) = match stmt {
                Stmt::Eval(Expr::Call {
                    fun,
                    type_args,
                    args,
                }) => (*fun, type_args.clone(), args.clone()),
                Stmt::Let {
                    value:
                        Expr::Call {
                            fun,
                            type_args,
                            args,
                        },
                    ..
                } => (*fun, type_args.clone(), args.clone()),
                _ => unreachable!("trigger detection mismatch"),
            };
            (ctx.aborts_map[&callee_fid], ta, a)
        }
        CalleeAbortsTrigger::LetBorrowMapKey {
            aborts_fid,
            type_args,
            args,
        }
        | CalleeAbortsTrigger::LetBorrowVecIndex {
            aborts_fid,
            type_args,
            args,
        } => (*aborts_fid, type_args.clone(), args.clone()),
    };

    // Continuation: either drop the Eval, or keep the Let. Then append
    // the post-trigger stmts, with the original tail. BorrowMapKey
    // triggers always live on a Stmt::Let (its bound var is used
    // downstream), so the trigger stmt stays.
    let continuation_stmts: Vec<Stmt> = match &trigger {
        CalleeAbortsTrigger::Eval => trailing.into_iter().skip(1).collect(),
        CalleeAbortsTrigger::Let
        | CalleeAbortsTrigger::LetBorrowMapKey { .. }
        | CalleeAbortsTrigger::LetBorrowVecIndex { .. } => trailing,
    };
    let continuation_block = Block {
        stmts: continuation_stmts,
        tail: trailing_tail,
    };

    // Determine the .aborts callee's return type. Three cases:
    //   - Function entry (FunctionKind::Spec(Aborts)): always
    //     Option<MoveAbortCode> by construction in this module.
    //   - Native entry: stage 10 registers BoundedU{N}_<op>_aborts
    //     with Type::Bool (legacy prelude shape). Wrap the Bool
    //     into Option<MoveAbortCode> below.
    //   - Anything else: assume Option<MoveAbortCode> (defensive).
    // Detect if the aborts companion returns Bool (legacy native
    // shape). After stage 3's `augment_return_type` runs, natives
    // with `&mut` params get their return type wrapped in a Tuple
    // whose first element is the original return type. So a Bool-
    // returning .aborts companion with a single &mut param looks
    // like Tuple([Bool, MutableRef<...>]). We treat that shape as
    // Bool-returning for splice wrap purposes.
    let callee_returns_bool = match program_lookup_return_type(ctx, aborts_fid) {
        Some(Type::Bool) => true,
        Some(Type::Tuple(items)) => matches!(items.first(), Some(Type::Bool)),
        _ => false,
    };

    // Inject `let __c_N = Call(g.aborts, args)` at the end of b.stmts.
    // For Bool-returning natives, wrap into Option<MoveAbortCode>:
    //   let __c_bool = Call(g.aborts, args)
    //   let __c_N = if __c_bool then Some(MoveAbortCode { ... }) else None
    // Proof mode preserves the historical fixed code-0 payload. Observed-test
    // mode enriches known framework companions with concrete code/origin data.
    let abort_var = ctx.fresh_abort_var();
    if callee_returns_bool {
        let bool_var = ctx.fresh_abort_var();
        // Always single-slot pattern: the Lean target's .aborts
        // companion returns just Bool, even though the IR's return
        // type may be a Tuple (from stage 3's mut-param
        // augmentation — the renderer strips the mut wrappers
        // when emitting the Call). The single-slot pattern produces
        // `let __c_bool := pop_back.aborts(...)` which Lean
        // type-checks as `Bool := Bool`. Multi-slot destructure
        // would force `(__c_bool, _) := pop_back.aborts(...)` which
        // Lean rejects since the call returns Bool not a Tuple.
        b.stmts.push(Stmt::Let {
            pattern: vec![Some(bool_var.clone())],
            value: Expr::Call {
                fun: aborts_fid,
                type_args,
                args,
            },
        });
        // Wrap the legacy Bool result into the active abort payload shape.
        let some_branch = Block {
            stmts: Vec::new(),
            tail: BlockTail::Value(bool_native_abort_some(ctx, aborts_fid)),
        };
        let none_branch = Block {
            stmts: Vec::new(),
            tail: BlockTail::Value(ctx.types.make_none()),
        };
        b.stmts.push(Stmt::Let {
            pattern: vec![Some(abort_var.clone())],
            value: Expr::If {
                cond: Box::new(Expr::Var(bool_var)),
                then_branch: Box::new(some_branch),
                else_branch: Box::new(none_branch),
            },
        });
    } else if ctx.types.payload_mode == AbortPayloadMode::ObservedTest
        && native_full_abort_origin_tag(ctx.program, aborts_fid).is_some()
    {
        let raw_var = ctx.fresh_abort_var();
        b.stmts.push(Stmt::Let {
            pattern: vec![Some(raw_var.clone())],
            value: Expr::Call {
                fun: aborts_fid,
                type_args,
                args,
            },
        });
        let payload_var = ctx.fresh_abort_var();
        let origin_tag = native_full_abort_origin_tag(ctx.program, aborts_fid)
            .expect("observed full native descriptor was present");
        b.stmts.push(Stmt::Let {
            pattern: vec![Some(abort_var.clone())],
            value: Expr::Match {
                struct_id: ctx.types.option,
                selector: Box::new(Expr::Var(raw_var)),
                cases: vec![
                    MatchArm {
                        variant: OPTION_NONE_TAG,
                        bindings: Vec::new(),
                        body: Box::new(Block {
                            stmts: Vec::new(),
                            tail: BlockTail::Value(ctx.types.make_none()),
                        }),
                    },
                    MatchArm {
                        variant: OPTION_SOME_TAG,
                        bindings: vec![payload_var.clone()],
                        body: Box::new(Block {
                            stmts: Vec::new(),
                            tail: BlockTail::Value(ctx.types.make_error_at(
                                Expr::Field {
                                    struct_id: ctx.types.abort_code,
                                    field_index: 0,
                                    base: Box::new(Expr::Var(payload_var)),
                                },
                                origin_tag,
                                ObservedErrorKind::Abort,
                            )),
                        }),
                    },
                ],
            },
        });
    } else {
        b.stmts.push(Stmt::Let {
            pattern: vec![Some(abort_var.clone())],
            value: Expr::Call {
                fun: aborts_fid,
                type_args,
                args,
            },
        });
    }

    // Build the splice tail: Match on __c_N.
    let some_arm_payload_var = ctx.fresh_abort_var();
    let none_arm = MatchArm {
        variant: OPTION_NONE_TAG,
        bindings: Vec::new(),
        body: Box::new(continuation_block),
    };
    let some_arm = MatchArm {
        variant: OPTION_SOME_TAG,
        // The Aborted variant of AbortResult<AbortCode> has one
        // field (the wrapped AbortCode). The binding is unused — we
        // propagate Var(__c_N) directly — but the IR validator
        // requires bindings.len() == variant_fields.len(), so we
        // bind to a fresh placeholder var.
        bindings: vec![some_arm_payload_var.clone()],
        body: Box::new(Block {
            stmts: Vec::new(),
            // Return (early-exit terminator), NOT Value. The Return
            // doesn't contribute a value type to the Match -- the
            // Match's overall type is whatever the NoAbort arm
            // delivers (the source-T continuation). The surrounding
            // context preserves its source-T expectation; no type
            // propagation upstream. The Return's payload (__c) gets
            // propagated to the function tail by the inner-Return
            // lift pass (task #26). Rebuild the explicit Aborted value from
            // the arm payload instead of returning the selector variable.
            // After one lift iteration Return becomes Value; keeping that
            // Value as a syntactic Aborted pack lets subsequent nested lifts
            // recognize it as terminal abort propagation instead of routing
            // it through the normal NoAbort continuation.
            tail: BlockTail::Return(Box::new(aborted_of(ctx.types, some_arm_payload_var))),
        }),
    };
    b.tail = BlockTail::Value(Expr::Match {
        struct_id: ctx.types.option,
        selector: Box::new(Expr::Var(abort_var)),
        cases: vec![none_arm, some_arm],
    });
}

fn splice_callee_aborts_in_stmt(s: &mut Stmt, ctx: &mut SpliceCtx) {
    match s {
        Stmt::Let { value, .. } => splice_callee_aborts_in_expr(value, ctx),
        Stmt::Eval(e) => splice_callee_aborts_in_expr(e, ctx),
    }
}

fn splice_callee_aborts_in_tail(t: &mut BlockTail, ctx: &mut SpliceCtx) {
    match t {
        BlockTail::Value(e) => splice_callee_aborts_in_expr(e, ctx),
        BlockTail::Abort { code } => splice_callee_aborts_in_expr(code, ctx),
        BlockTail::Return(value)
        | BlockTail::Break { value, .. }
        | BlockTail::Continue { value, .. }
        | BlockTail::ReturnFromBlock { value, .. } => splice_callee_aborts_in_expr(value, ctx),
    }
}

fn splice_callee_aborts_in_expr(e: &mut Expr, ctx: &mut SpliceCtx) {
    match e {
        Expr::Borrow { step, base } => {
            for __pe in step.exprs_mut() {
                splice_callee_aborts_in_expr(__pe, ctx);
            }
            splice_callee_aborts_in_expr(base, ctx);
        }
        Expr::Update { step, base, value } => {
            for __pe in step.exprs_mut() {
                splice_callee_aborts_in_expr(__pe, ctx);
            }
            splice_callee_aborts_in_expr(base, ctx);
            splice_callee_aborts_in_expr(value, ctx);
        }
        Expr::Var(_)
        | Expr::Const(_)
        | Expr::Unit
        | Expr::BorrowLoc(_)
        | Expr::BorrowGlobal(_)
        | Expr::WriteBack { .. }
        | Expr::IsParent { .. } => {}
        Expr::BinOp { lhs, rhs, .. } => {
            splice_callee_aborts_in_expr(lhs, ctx);
            splice_callee_aborts_in_expr(rhs, ctx);
        }
        Expr::UnOp { operand, .. } => splice_callee_aborts_in_expr(operand, ctx),
        Expr::BitOp(op) => match op {
            BitOp::Extract { operand, .. }
            | BitOp::ZeroExtend { operand, .. }
            | BitOp::SignExtend { operand, .. } => splice_callee_aborts_in_expr(operand, ctx),
            BitOp::Concat { high, low } => {
                splice_callee_aborts_in_expr(high, ctx);
                splice_callee_aborts_in_expr(low, ctx);
            }
        },
        Expr::Call { args, .. } | Expr::Tuple(args) | Expr::Pack { fields: args, .. } => {
            for a in args {
                splice_callee_aborts_in_expr(a, ctx);
            }
        }
        Expr::Unpack { value, .. }
        | Expr::Field { base: value, .. }
        | Expr::ReadRef(value)
        | Expr::ToProp(value)
        | Expr::ToBool(value) => splice_callee_aborts_in_expr(value, ctx),
        Expr::If {
            cond,
            then_branch,
            else_branch,
        } => {
            splice_callee_aborts_in_expr(cond, ctx);
            splice_callee_aborts_in_block(then_branch, ctx);
            splice_callee_aborts_in_block(else_branch, ctx);
        }
        Expr::Match {
            selector, cases, ..
        } => {
            splice_callee_aborts_in_expr(selector, ctx);
            for arm in cases.iter_mut() {
                splice_callee_aborts_in_block(&mut arm.body, ctx);
            }
        }
        Expr::While {
            header,
            cond,
            body,
            iter_locals,
            header_exit_locals: _,
            live_out: _,
        } => {
            for (_, init) in iter_locals.iter_mut() {
                splice_callee_aborts_in_expr(init, ctx);
            }
            // Headers, conds, and bodies all run inside the loop's
            // scope -- splicing here would move stmts into a Match
            // arm and break references from the cond / loop body to
            // header-bound vars. Skip trigger detection in all three
            // (the abortable Calls inside will be handled by
            // post-loop checks or by the source's loop iteration
            // semantics).
            let was_in_loop = ctx.inside_loop_body;
            ctx.inside_loop_body = true;
            splice_callee_aborts_in_block(header, ctx);
            splice_callee_aborts_in_expr(cond, ctx);
            splice_callee_aborts_in_block(body, ctx);
            ctx.inside_loop_body = was_in_loop;
        }
        Expr::WriteRef { reference, value } => {
            splice_callee_aborts_in_expr(reference, ctx);
            splice_callee_aborts_in_expr(value, ctx);
        }
        Expr::Quantifier {
            domain, body: _, ..
        } => {
            match domain {
                QuantDomain::Unbounded => {}
                QuantDomain::Range { start, end } => {
                    splice_callee_aborts_in_expr(start, ctx);
                    splice_callee_aborts_in_expr(end, ctx);
                }
                QuantDomain::Collection(c) => splice_callee_aborts_in_expr(c, ctx),
                QuantDomain::VecRange { vec, start, end } => {
                    splice_callee_aborts_in_expr(vec, ctx);
                    splice_callee_aborts_in_expr(start, ctx);
                    splice_callee_aborts_in_expr(end, ctx);
                }
            }
            // Do NOT splice callee aborts inside the quantifier BODY: a
            // quantified predicate does not contribute abort conditions
            // (its evaluation over the domain is treated as total). A
            // world-threaded predicate call there is rendered as its
            // Bool value (stage 4 applied the fixed world); wrapping it
            // with `.aborts` would yield an `AbortResult` where the
            // predicate wants a `Bool`. Splicing would also move stmts
            // into a Match arm and break the quantifier binder's scope.
        }
        Expr::LabeledBlock { body, .. } => splice_callee_aborts_in_block(body, ctx),
    }
}

/// Splice a chain of early-exit guards INTO the body's tail, one per
/// `prover::asserts(p)` predicate. Each guard reads
/// `if !p_n { Return(Some(assert_code)) } else <prior-tail>`, with
/// the original body's stmts preserved in order.
///
/// Placement at the body's TAIL (rather than the start) is critical:
/// the predicate `p` may reference let-bindings from the body's stmts.
/// At the body's tail, all those lets are in scope. If we wrapped at
/// the start (above all the lets), the predicate's free vars would
/// dangle.
/// In-place lowering of `prover::{asserts,requires,ensures}` calls in an
/// `.aborts` body. Each `eval prover::asserts(p)` is replaced AT ITS
/// POSITION by `if !p { return Aborted } else { <rest-of-block> }`,
/// keeping the abort-check inside the control-flow branch where `p`'s
/// vars are in scope. `requires`/`ensures` calls are dropped (a
/// precondition is assumed; a postcondition is not an abort condition).
///
/// This replaces the old `wrap_with_asserts`, which COLLECTED every
/// assert predicate and appended them as one flat `if !p0 .. else if !p1
/// .. else <tail>` chain at the body tail. That is correct only when all
/// predicates are top-level; for BRANCH-CONDITIONAL asserts (e.g. the
/// spec wrote `if c { asserts(a) } else { asserts(b) }`) the tail chain
/// references `a`/`b` -- defined in mutually-exclusive branches -- on
/// paths where they were never computed, rendering as Lean "unbound
/// identifier" (`t_tXX_0`). Lowering in place keeps each check in its
/// branch; the inner `return Aborted` is lifted per-branch by
/// `return_lift`.
fn lower_prover_asserts_in_block(b: &mut Block, ids: &ProverFnIds, types: &AbortsTypeIds) {
    let mut i = 0;
    while i < b.stmts.len() {
        match prover_call_kind(&b.stmts[i], ids) {
            Some(ProverKind::Asserts(p)) => {
                // Split: the assert and everything after it become the
                // guarded `else` branch; the prefix stays put.
                let suffix: Vec<Stmt> = b.stmts.split_off(i + 1);
                let rest_tail = std::mem::replace(&mut b.tail, BlockTail::Value(Expr::Unit));
                b.stmts.truncate(i); // drop the assert stmt itself
                let mut rest = Block {
                    stmts: suffix,
                    tail: rest_tail,
                };
                lower_prover_asserts_in_block(&mut rest, ids, types);
                let guard = Expr::If {
                    cond: Box::new(Expr::UnOp {
                        op: crate::ir::ops::UnOp::Not,
                        operand: Box::new(p),
                    }),
                    then_branch: Box::new(Block {
                        stmts: Vec::new(),
                        tail: BlockTail::Return(Box::new(types.assert_abort_some())),
                    }),
                    else_branch: Box::new(rest),
                };
                b.tail = BlockTail::Value(guard);
                return;
            }
            Some(ProverKind::Drop) => {
                b.stmts.remove(i);
            }
            None => {
                lower_prover_asserts_in_expr(stmt_expr_mut(&mut b.stmts[i]), ids, types);
                i += 1;
            }
        }
    }
    if let BlockTail::Value(e) = &mut b.tail {
        lower_prover_asserts_in_expr(e, ids, types);
    }
}

enum ProverKind {
    Asserts(Expr),
    Drop,
}

fn prover_call_kind(s: &Stmt, ids: &ProverFnIds) -> Option<ProverKind> {
    // Spec calls only ever appear as `Stmt::Eval(Call(prover_fn, [p]))`
    // (a value-position prover call is rejected by collect_predicates).
    let Stmt::Eval(Expr::Call { fun, args, .. }) = s else {
        return None;
    };
    if Some(*fun) == ids.asserts {
        if let [p] = args.as_slice() {
            return Some(ProverKind::Asserts(p.clone()));
        }
    }
    if Some(*fun) == ids.requires || Some(*fun) == ids.ensures {
        return Some(ProverKind::Drop);
    }
    None
}

fn stmt_expr_mut(s: &mut Stmt) -> &mut Expr {
    match s {
        Stmt::Let { value, .. } => value,
        Stmt::Eval(e) => e,
    }
}

/// Recurse into control-flow branches (the only place asserts nest).
fn lower_prover_asserts_in_expr(e: &mut Expr, ids: &ProverFnIds, types: &AbortsTypeIds) {
    match e {
        Expr::If {
            then_branch,
            else_branch,
            ..
        } => {
            lower_prover_asserts_in_block(then_branch, ids, types);
            lower_prover_asserts_in_block(else_branch, ids, types);
        }
        Expr::Match { cases, .. } => {
            for arm in cases.iter_mut() {
                lower_prover_asserts_in_block(&mut arm.body, ids, types);
            }
        }
        _ => {}
    }
}

#[derive(Clone, Copy)]
struct NativeBoolAbortDescriptor {
    code: u64,
    error_kind: ObservedErrorKind,
    origin: NativeAbortOrigin,
}

#[derive(Clone, Copy)]
enum NativeAbortOrigin {
    Caller,
    Module(&'static str),
}

fn native_bool_abort_descriptor(
    program: &Program,
    aborts_fid: FunId,
) -> Option<NativeBoolAbortDescriptor> {
    let companion = program.natives.decls.get(&aborts_fid)?;
    let target = program.natives.decls.get(&companion.spec_target?)?;
    let module = program.modules.get(&target.module)?;

    if crate::stage_10_bounded_nat::prelude_fids::is_aborting_native_pair(target, companion) {
        return Some(NativeBoolAbortDescriptor {
            code: 0,
            error_kind: ObservedErrorKind::Arithmetic,
            origin: NativeAbortOrigin::Caller,
        });
    }

    if target.module != companion.module
        || !target.is_framework
        || !companion.is_framework
        || target.user_native.is_some()
        || companion.user_native.is_some()
        || companion.name.strip_suffix(".aborts") != Some(target.name.as_str())
    {
        return None;
    }

    let addressed_module = canonical_addressed_module(module)?;
    match (
        module.package_name.as_str(),
        addressed_module.as_str(),
        target.name.as_str(),
    ) {
        ("MoveStdlib", "0x1::vector", "borrow" | "swap") => Some(NativeBoolAbortDescriptor {
            code: 1,
            error_kind: ObservedErrorKind::VectorOperation,
            origin: NativeAbortOrigin::Caller,
        }),
        ("MoveStdlib", "0x1::vector", "pop_back") => Some(NativeBoolAbortDescriptor {
            code: 2,
            error_kind: ObservedErrorKind::VectorOperation,
            origin: NativeAbortOrigin::Caller,
        }),
        ("MoveStdlib", "0x1::vector", "destroy_empty") => Some(NativeBoolAbortDescriptor {
            code: 3,
            error_kind: ObservedErrorKind::VectorOperation,
            origin: NativeAbortOrigin::Caller,
        }),
        ("MoveStdlib", "0x1::vector", "remove" | "insert") => Some(NativeBoolAbortDescriptor {
            code: 0x20000,
            error_kind: ObservedErrorKind::Abort,
            origin: NativeAbortOrigin::Module("0x1::vector"),
        }),
        ("Sui", "0x2::dynamic_field", "borrow" | "borrow_mut" | "remove") => {
            Some(NativeBoolAbortDescriptor {
                code: 1,
                error_kind: ObservedErrorKind::Abort,
                origin: NativeAbortOrigin::Module("0x2::dynamic_field"),
            })
        }
        ("Sui", "0x2::dynamic_field", "add" | "store_bag_add") => Some(NativeBoolAbortDescriptor {
            code: 0,
            error_kind: ObservedErrorKind::Abort,
            origin: NativeAbortOrigin::Module("0x2::dynamic_field"),
        }),
        ("Sui", "0x2::table", "borrow" | "borrow_mut" | "remove") => {
            Some(NativeBoolAbortDescriptor {
                code: 1,
                error_kind: ObservedErrorKind::Abort,
                origin: NativeAbortOrigin::Module("0x2::dynamic_field"),
            })
        }
        ("Sui", "0x2::table", "add") => Some(NativeBoolAbortDescriptor {
            code: 0,
            error_kind: ObservedErrorKind::Abort,
            origin: NativeAbortOrigin::Module("0x2::dynamic_field"),
        }),
        ("Sui", "0x2::table", "destroy_empty") => Some(NativeBoolAbortDescriptor {
            code: 0,
            error_kind: ObservedErrorKind::Abort,
            origin: NativeAbortOrigin::Module("0x2::table"),
        }),
        ("Sui", "0x2::vec_set", "insert") => Some(NativeBoolAbortDescriptor {
            code: 0,
            error_kind: ObservedErrorKind::Abort,
            origin: NativeAbortOrigin::Module("0x2::vec_set"),
        }),
        ("Sui", "0x2::vec_set", "remove") => Some(NativeBoolAbortDescriptor {
            code: 1,
            error_kind: ObservedErrorKind::Abort,
            origin: NativeAbortOrigin::Module("0x2::vec_set"),
        }),
        ("Sui", "0x2::bag", "destroy_empty") => Some(NativeBoolAbortDescriptor {
            code: 0,
            error_kind: ObservedErrorKind::Abort,
            origin: NativeAbortOrigin::Module("0x2::bag"),
        }),
        ("Sui", "0x2::object_bag", "destroy_empty") => Some(NativeBoolAbortDescriptor {
            code: 0,
            error_kind: ObservedErrorKind::Abort,
            origin: NativeAbortOrigin::Module("0x2::object_bag"),
        }),
        _ => None,
    }
}

fn native_full_abort_origin_tag(program: &Program, aborts_fid: FunId) -> Option<u64> {
    let companion = program.natives.decls.get(&aborts_fid)?;
    let target = program.natives.decls.get(&companion.spec_target?)?;
    let module = program.modules.get(&target.module)?;
    if target.module != companion.module
        || !target.is_framework
        || !companion.is_framework
        || target.user_native.is_some()
        || companion.user_native.is_some()
        || companion.name.strip_suffix(".aborts") != Some(target.name.as_str())
        || module.package_name != "SuiSystem"
        || module.name != "validator"
        || target.name != "validate_metadata_bcs"
        || canonical_addressed_module(module).as_deref() != Some("0x3::validator")
    {
        return None;
    }
    Some(program.abort_provenance.tag_for_module(target.module))
}

fn bool_native_abort_some(ctx: &SpliceCtx, aborts_fid: FunId) -> Expr {
    if ctx.types.payload_mode == AbortPayloadMode::Proof {
        return ctx.types.assert_abort_some();
    }

    let Some(descriptor) = native_bool_abort_descriptor(ctx.program, aborts_fid) else {
        return ctx.types.make_error_at(
            Expr::Const(Const::UInt {
                bits: 64,
                value: ethnum::U256::ZERO,
            }),
            UNKNOWN_ABORT_ORIGIN_TAG,
            ObservedErrorKind::Unknown,
        );
    };
    let origin_tag = match descriptor.origin {
        NativeAbortOrigin::Caller => ctx.types.origin_tag,
        NativeAbortOrigin::Module(origin_module) => ctx
            .program
            .abort_provenance
            .tag_for_addressed_module(origin_module),
    };
    ctx.types.make_error_at(
        Expr::Const(Const::UInt {
            bits: 64,
            value: ethnum::U256::from(descriptor.code),
        }),
        origin_tag,
        descriptor.error_kind,
    )
}

// ---------------------------------------------------------------------------
// Utilities
// ---------------------------------------------------------------------------

/// Resolve a FunId's declared return type by consulting both
/// `program.functions` and `program.natives.decls`. Returns `None`
/// for unknown FunIds (defensive; the caller falls back to the
/// "Option<MoveAbortCode>" assumption).
fn program_lookup_return_type<'a>(ctx: &'a SpliceCtx<'a>, fid: FunId) -> Option<&'a Type> {
    ctx.program
        .lookup_callee(fid)
        .map(|callee| &callee.signature().return_type)
}
