//! Stage 7 phases 3b.5 / 3b.5b -- live-accumulator loop-abort folds.
//!
//! [`run`] is 3b.5, for a loop the `Spec(Aborts)` parent owns directly.
//! [`run_labeled_wrapper_loops`] is 3b.5b, for one nested in an extracted
//! labeled block, where the continuation does not exist yet and has to be
//! manufactured; see its own doc comment. Both share
//! [`fold_live_threading`].
//!
//! Counterpart to `aborts_loop_propagate` (phase 3a.5, the DEAD-accumulator
//! case). Handles a `.aborts`-variant loop whose accumulator is CONSUMED after
//! the loop by a continuation `cont(extra.., while_N(loop_args))` while
//! `while_N.after` itself holds post-loop abort checks -- e.g. cetus-dlmm
//! `bin::add_bin_if_absent`: a build loop whose vector feeds a
//! `skip_list::insert`, with leading `.aborts` checks nested above.
//!
//! Runs AFTER `return_lift` (phase 3b), which by now has extracted the inline
//! post-loop continuation into a function (`f.aborts.cont_0`). The dead-case
//! pass (3a.5) cannot handle this shape because there the continuation is
//! still inline. With `cont` a real function the fold is expressible:
//!   - `while_N` / `.after` are retyped to `AbortResult`.
//!   - `cont`'s extra args are threaded through `while_N -> .after` as fresh
//!     trailing params.
//!   - `.after`'s no-abort accumulator value-leaf becomes
//!     `cont(extra.., accumulator)` (the accumulator is in scope there).
//!   - the parent's `cont(extra.., while_N(loop_args))` collapses to
//!     `while_N(loop_args, extra..)`.
//! `.after`'s inner abort `Return(<AbortResult>)` arms then match the new
//! `AbortResult` return type and render correctly (no further lifting needed).
//!
//! An `.after` that carries a post-loop abort `Return` is the shape the nested
//! fold was written for, so it gets first refusal there; an `.after` that merely
//! returns the accumulator has no abort of its own but its chain is still a value
//! chain misfiled under an `.aborts.` name (sui-system
//! `sui_system_state_inner::store_execution_time_estimates_v2`), so the nested
//! fold runs as the fallback once the world-threaded variant has declined.
//!
//! Strictly guarded: a slot is folded only when (a) `while_N.after` still
//! returns the accumulator (not already AbortResult -- i.e. the dead-case
//! pass left it), and (b) the parent has EXACTLY
//! ONE tail-position `Call(cont, [Var.., Call(while_N, ..)])` whose last arg
//! is the while_N call. Any mismatch is a no-op.

use std::collections::{BTreeMap, BTreeSet};

use crate::ir::function::{Effects, Function, FunctionKind, Param, Signature, SpecKind};
use crate::ir::ty::Type;
use crate::ir::{Block, BlockTail, Expr, FunId, Program, Stmt, VarId};

use super::aborts_variant::AbortsMap;
use super::option_aborts::{ensure_aborts_types, AbortsTypeIds};
use super::{find_world_struct_id, Stage7Error};

pub fn run(program: &mut Program) -> Result<(), Stage7Error> {
    let types = ensure_aborts_types(program);
    let abort_result_ty = types.option_abort_code_type();

    let aborts_parents: Vec<FunId> = program
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

    for parent_fid in aborts_parents {
        let mut slots: BTreeMap<u32, (Option<FunId>, Option<FunId>)> = BTreeMap::new();
        for (fid, f) in program.functions.iter() {
            match f.kind {
                FunctionKind::LoopBody { parent, slot } if parent == parent_fid => {
                    slots.entry(slot).or_default().0 = Some(*fid);
                }
                FunctionKind::LoopAfter { parent, slot } if parent == parent_fid => {
                    slots.entry(slot).or_default().1 = Some(*fid);
                }
                _ => {}
            }
        }
        for (_slot, (while_opt, after_opt)) in slots {
            let (Some(while_fid), Some(after_fid)) = (while_opt, after_opt) else {
                continue;
            };
            // Skip if `.after` is already AbortResult (a prior pass folded it).
            if after_is_abort_result(program, after_fid, &abort_result_ty) {
                continue;
            }
            // An `.after` carrying a post-loop abort `Return` is the
            // single-value, directly-nested shape the nested fold was written
            // for, so it goes first there. Otherwise the world-threaded variant
            // gets first refusal, because its abort exits are value-position
            // `AbortResult` leaves rather than `Return`s.
            let nested_first = after_has_return(program, after_fid);
            if nested_first {
                try_fold_live(program, while_fid, after_fid, &abort_result_ty);
            }
            // A world-threaded df loop returns `(accumulator, World)`, so the
            // result is destructured (`let (val, world) := while_N(..)`) before
            // the continuation call -- a shape the nested matcher misses. If the
            // nested fold did not fire (`.after` still value-typed), try the
            // world-threaded variant. See cetus-dlmm `bin::add_bin_if_absent`.
            if !after_is_abort_result(program, after_fid, &abort_result_ty) {
                try_fold_live_world(program, while_fid, after_fid, &abort_result_ty);
            }
            // Fallback for an `.after` that only returns the accumulator: no
            // abort of its own, but the chain is still misfiled under an
            // `.aborts.` name and the nested fold is what retypes it. This is
            // the sui-system `store_execution_time_estimates_v2` shape, whose
            // two `.aborts.while_N` return `&mut SuiSystemStateInnerV2`;
            // retyping is what lets phase 3b.6 splice their dropped
            // callee-aborts.
            if !nested_first && !after_is_abort_result(program, after_fid, &abort_result_ty) {
                try_fold_live(program, while_fid, after_fid, &abort_result_ty);
            }
        }
    }
    Ok(())
}

fn loop_after(program: &Program, after_fid: FunId) -> &crate::ir::Function {
    program
        .functions
        .get(&after_fid)
        .expect("LoopAfter enumerated from program.functions")
}

fn after_is_abort_result(program: &Program, after_fid: FunId, abort_result_ty: &Type) -> bool {
    loop_after(program, after_fid).signature.return_type == *abort_result_ty
}

fn after_has_return(program: &Program, after_fid: FunId) -> bool {
    block_has_return(&loop_after(program, after_fid).body)
}

// ---------------------------------------------------------------------------
// Phase 3b.5b -- the manufactured continuation (labeled-block wrapper loops)
// ---------------------------------------------------------------------------

/// Phase 3b.5b: fold a labeled-block loop chain whose accumulator is
/// consumed LIVE.
///
/// Phase 3a.5b (`retype_and_splice_labeled_block_loops`) converts such a
/// chain only when EVERY consumption is dead; one live site vetoes the
/// whole chain, so the VALUE loop ships under an `.aborts.` name and every
/// callee-abort inside it is silently dropped. Measured on
/// `ascii::try_string`: `vector::borrow` out-of-bounds and
/// `BoundedU64_add` overflow, both modeled faces in the same tree.
///
/// [`run`] cannot reach it either, for two independent reasons: it
/// enumerates only `Spec(Aborts)` parents (here the `LoopBody`'s parent is
/// the Synthetic `<f>.aborts.labeled_N` wrapper), and `collect_sites` needs
/// the consumer to already hold a `Call(cont, [extra.., Call(while_N, ..)])`
/// -- but the consumer binds `let acc = labeled_N(args)` and there is no
/// `cont` to match at all.
///
/// So the continuation is MANUFACTURED: the host's post-consumption
/// remainder is lifted into a fresh `<host>.cont_K(captures.., acc)`, and
/// the captures are threaded through THREE functions -- `while_N`, `.after`
/// and the Synthetic wrapper, which the direct fold never has to touch.
/// Every accumulator leaf of `while_N` / `.after` then delivers
/// `cont(captures.., leaf)` instead of the raw accumulator, so all three
/// retype to `AbortResult` and the loop's callee-aborts can finally be
/// spliced.
pub fn run_labeled_wrapper_loops(
    program: &mut Program,
    aborts_map: &AbortsMap,
) -> Result<(), Stage7Error> {
    let types = ensure_aborts_types(program);
    let abort_result_ty = types.option_abort_code_type();
    // Two chains consumed by the SAME host would race: folding the first
    // moves that host's remainder -- including the second's consumption --
    // into a continuation, staling the second's recorded stmt index. Fold at
    // most one per host, then re-discover (the second's consumption is now a
    // top-level stmt of the continuation, itself an `AbortResult`-returning
    // `.aborts`-family host). Terminates: every fold retypes one wrapper out
    // of the candidate set.
    const MAX_ITER: usize = 64;
    for _ in 0..MAX_ITER {
        let chains = find_live_labeled_chains(program, aborts_map, &abort_result_ty);
        if chains.is_empty() {
            break;
        }
        let mut hosts: std::collections::BTreeSet<FunId> = std::collections::BTreeSet::new();
        for chain in &chains {
            if hosts.insert(chain.host_fid) {
                fold_live_labeled_chain(program, chain, aborts_map, &types, &abort_result_ty);
            }
        }
    }
    Ok(())
}

struct LiveLabeledChain {
    /// Labeled-block wrapper `P` (`<f>.aborts.labeled_N`, Synthetic, whose
    /// body is just `Value(Call(L, ..))`).
    wrapper_fid: FunId,
    /// Loop body `L` (`<f>.aborts.labeled_N.while_0`).
    loop_fid: FunId,
    /// Loop after `A` (`<f>.aborts.labeled_N.while_0.after`).
    after_fid: FunId,
    /// The one function holding `let acc = P(args)`.
    host_fid: FunId,
    /// Index of that `let` in the host's OWN top-level block.
    stmt_index: usize,
    acc: VarId,
    /// `P`'s pre-fold return type -- the labeled block's accumulator.
    acc_type: Type,
    call_type_args: Vec<Type>,
    call_args: Vec<Expr>,
}

fn find_live_labeled_chains(
    program: &Program,
    aborts_map: &AbortsMap,
    abort_result_ty: &Type,
) -> Vec<LiveLabeledChain> {
    let mut out: Vec<LiveLabeledChain> = Vec::new();
    for (wrapper_fid, p) in program.functions.iter() {
        if !matches!(p.kind, FunctionKind::Synthetic) || !p.body.stmts.is_empty() {
            continue;
        }
        if !crate::ir::names::is_aborts_family_name(&p.name) {
            continue;
        }
        // Already AbortResult means a prior pass converted this chain, or
        // the labeled block's value genuinely IS an abort verdict.
        if p.signature.return_type == *abort_result_ty {
            continue;
        }
        let BlockTail::Value(Expr::Call { fun: loop_fid, .. }) = &p.body.tail else {
            continue;
        };
        let loop_fid = *loop_fid;
        let Some(l) = program.functions.get(&loop_fid) else {
            continue;
        };
        let FunctionKind::LoopBody { parent, slot } = l.kind else {
            continue;
        };
        if parent != *wrapper_fid {
            continue;
        }
        let Some(after_fid) = program.functions.iter().find_map(|(id, af)| {
            matches!(af.kind, FunctionKind::LoopAfter { parent: q, slot: s }
                if q == *wrapper_fid && s == slot)
            .then_some(*id)
        }) else {
            continue;
        };
        // Only fire when the loop actually DROPS a callee-abort, so
        // abort-free labeled loops stay byte-identical.
        if !super::aborts_variant::loop_chain_has_dropped_abort(
            program, aborts_map, loop_fid, after_fid,
        ) {
            continue;
        }
        // `append_trailing_args` threads the fresh params only into the
        // wrapper's and the loop's own bodies, so any other caller would be
        // left short an argument.
        if !chain_calls_are_confined(program, *wrapper_fid, loop_fid, after_fid) {
            continue;
        }
        let Some((host_fid, stmt_index, acc, call_type_args, call_args)) =
            unique_live_consumption(program, *wrapper_fid, abort_result_ty)
        else {
            continue;
        };
        // The manufactured continuation is called from inside `L` / `A` with
        // the HOST's type parameters as arguments, so all four must agree.
        let host_type_params = &program.functions[&host_fid].signature.type_params;
        if [*wrapper_fid, loop_fid, after_fid]
            .iter()
            .any(|fid| program.functions[fid].signature.type_params != *host_type_params)
        {
            continue;
        }
        out.push(LiveLabeledChain {
            wrapper_fid: *wrapper_fid,
            loop_fid,
            after_fid,
            host_fid,
            stmt_index,
            acc,
            acc_type: p.signature.return_type.clone(),
            call_type_args,
            call_args,
        });
    }
    out
}

/// `L` is called only by the wrapper and by itself; `A` only by `L`.
fn chain_calls_are_confined(
    program: &Program,
    wrapper_fid: FunId,
    loop_fid: FunId,
    after_fid: FunId,
) -> bool {
    let targets: std::collections::BTreeSet<FunId> = [loop_fid, after_fid].into_iter().collect();
    program.functions.iter().all(|(fid, f)| {
        super::aborts_variant::count_calls_to(&f.body, &targets)
            .keys()
            .all(|callee| {
                if *callee == loop_fid {
                    *fid == wrapper_fid || *fid == loop_fid
                } else {
                    *fid == loop_fid
                }
            })
    })
}

/// The wrapper's single call site, when it is a LIVE top-level
/// `let acc = P(args)` in an `AbortResult`-returning `.aborts`-family host.
///
/// Deliberately narrow on both axes. A DEAD site belongs to phase 3a.5b,
/// which deadens rather than threads. A site BELOW the host's own top-level
/// block has no remainder to manufacture a continuation from: the
/// continuation is `stmts[i + 1..] ++ tail` of the block holding the `let`,
/// which is the function's whole continuation only at the top level.
fn unique_live_consumption(
    program: &Program,
    wrapper_fid: FunId,
    abort_result_ty: &Type,
) -> Option<(FunId, usize, VarId, Vec<Type>, Vec<Expr>)> {
    let targets: std::collections::BTreeSet<FunId> = std::iter::once(wrapper_fid).collect();
    let mut total = 0usize;
    let mut site: Option<(FunId, usize, VarId, Vec<Type>, Vec<Expr>)> = None;
    for (host_fid, h) in program.functions.iter() {
        let calls = super::aborts_variant::count_calls_to(&h.body, &targets);
        if calls.is_empty() {
            continue;
        }
        total += calls.values().sum::<usize>();
        if !crate::ir::names::is_aborts_family_name(&h.name)
            || h.signature.return_type != *abort_result_ty
        {
            continue;
        }
        for (i, s) in h.body.stmts.iter().enumerate() {
            let Stmt::Let {
                pattern,
                value:
                    Expr::Call {
                        fun,
                        type_args,
                        args,
                    },
            } = s
            else {
                continue;
            };
            if *fun != wrapper_fid || pattern.len() != 1 {
                continue;
            }
            let Some(acc) = &pattern[0] else { continue };
            let remainder = Block {
                stmts: h.body.stmts[i + 1..].to_vec(),
                tail: h.body.tail.clone(),
            };
            if !crate::ir::analysis::free_vars::free_vars(&remainder).contains(acc) {
                continue;
            }
            site = Some((*host_fid, i, acc.clone(), type_args.clone(), args.clone()));
        }
    }
    // One recognised site AND no unrecognised one: any other occurrence
    // would keep calling the wrapper at its old arity.
    site.filter(|_| total == 1)
}

struct Manufactured {
    cont_fid: FunId,
    cont_type_args: Vec<Type>,
    captures: Vec<VarId>,
    capture_types: Vec<Type>,
    lifecycle_extra: Option<usize>,
}

/// Lift the host's post-consumption remainder into a fresh
/// `<host>.cont_K(captures.., acc)`. The accumulator is the LAST parameter,
/// which is the shape [`fold_live_threading`]'s leaf wrapping already
/// expects (`cont(extra.., accumulator)`).
fn manufacture_continuation(program: &mut Program, chain: &LiveLabeledChain) -> Manufactured {
    let host = program
        .functions
        .get(&chain.host_fid)
        .expect("host function present");
    let remainder = Block {
        stmts: host.body.stmts[chain.stmt_index + 1..].to_vec(),
        tail: host.body.tail.clone(),
    };
    let captures: Vec<VarId> = crate::ir::analysis::free_vars::free_vars(&remainder)
        .into_iter()
        .filter(|v| *v != chain.acc)
        .collect();
    let scope = super::aborts_variant::collect_function_var_types(host, program);
    let capture_types: Vec<Type> = captures
        .iter()
        .map(|v| {
            scope
                .get(v)
                .cloned()
                .expect("continuation capture is bound in the host body")
        })
        .collect();
    let mut params: Vec<Param> = captures
        .iter()
        .zip(capture_types.iter())
        .map(|(v, ty)| Param {
            name: v.to_string(),
            var: v.clone(),
            ty: ty.clone(),
        })
        .collect();
    params.push(Param {
        name: chain.acc.to_string(),
        var: chain.acc.clone(),
        ty: chain.acc_type.clone(),
    });
    let type_params = host.signature.type_params.clone();
    let cont_type_args: Vec<Type> = (0..type_params.len())
        .map(|i| Type::TypeParam(i as u16))
        .collect();
    let host_name = host.name.clone();
    let host_module = host.module;
    let return_type = host.signature.return_type.clone();

    // `return_lift` may already have taken slots on this host, so claim the
    // first free one rather than assuming 0.
    let mut slot = 0u32;
    let mut cont_name = crate::ir::names::cont_name(&host_name, slot);
    while program.functions.values().any(|f| f.name == cont_name) {
        slot += 1;
        cont_name = crate::ir::names::cont_name(&host_name, slot);
    }
    let cont_fid = program.next_function_id();
    program.functions.insert(
        cont_fid,
        Function {
            module: host_module,
            name: cont_name,
            signature: Signature {
                type_params,
                params,
                return_type,
            },
            body: remainder,
            kind: FunctionKind::Synthetic,
            // Provisional; stage 8 closes world_writes over synthetic helpers.
            effects: Effects::PURE,
            explicit_pure: false,
        },
    );
    let lifecycle_extra = find_world_struct_id(program)
        .and_then(|world_id| {
            crate::stage_04_effects::common::function_lifecycle_world_position(
                &program.functions[&cont_fid],
                world_id,
            )
        })
        .filter(|index| *index < captures.len());
    Manufactured {
        cont_fid,
        cont_type_args,
        captures,
        capture_types,
        lifecycle_extra,
    }
}

fn fold_live_labeled_chain(
    program: &mut Program,
    chain: &LiveLabeledChain,
    aborts_map: &AbortsMap,
    types: &AbortsTypeIds,
    abort_result_ty: &Type,
) {
    let Manufactured {
        cont_fid,
        cont_type_args,
        captures,
        capture_types,
        lifecycle_extra,
    } = manufacture_continuation(program, chain);

    // The remainder now lives in `cont`, so the host tail-calls the wrapper
    // with the continuation's captures appended.
    {
        let host = program.functions.get_mut(&chain.host_fid).unwrap();
        host.body.stmts.truncate(chain.stmt_index);
        let mut args = chain.call_args.clone();
        args.extend(captures.iter().map(|v| Expr::Var(v.clone())));
        host.body.tail = BlockTail::Value(Expr::Call {
            fun: chain.wrapper_fid,
            type_args: chain.call_type_args.clone(),
            args,
        });
    }

    let (wp, ap) = fold_live_threading(
        program,
        Some(chain.wrapper_fid),
        chain.loop_fid,
        chain.after_fid,
        &capture_types,
        lifecycle_extra,
        abort_result_ty,
    );

    // Route every accumulator leaf into the continuation. `while_N` is
    // spliced immediately after, so its leaves MAY ANF-lift an abortable
    // call into the statement position the splice detects; `.after` is not
    // spliced -- its natural-exit callees were already guarded by
    // `materialise`, before `labeled_block_extract` split the block -- so a
    // lift there would strand an unguarded `let`.
    for (fid, prefix_vars, anf_lift_abortable_call) in
        [(chain.loop_fid, &wp, true), (chain.after_fid, &ap, false)]
    {
        let prefix: Vec<Expr> = prefix_vars.iter().map(|v| Expr::Var(v.clone())).collect();
        let leaf = super::aborts_variant::AccumulatorLeaf::Continue {
            cont: cont_fid,
            type_args: &cont_type_args,
            prefix: &prefix,
            anf_lift_abortable_call,
        };
        let mut body = std::mem::replace(
            &mut program.functions.get_mut(&fid).unwrap().body,
            Block {
                stmts: Vec::new(),
                tail: BlockTail::Value(Expr::Unit),
            },
        );
        super::aborts_variant::retype_loop_accumulator_leaves(
            &mut body,
            chain.loop_fid,
            chain.after_fid,
            types,
            aborts_map,
            &leaf,
            &mut 0,
        );
        program.functions.get_mut(&fid).unwrap().body = body;
    }

    // The loop is `AbortResult`-typed now, so the generic splice can finally
    // thread the callee-aborts `materialise` skipped inside the live `While`.
    super::aborts_variant::splice_one_extracted_loop(program, chain.loop_fid, aborts_map);
}

/// After `cont_inline` flattens loop continuations, a `.aborts` loop body's
/// "continue" path -- a call to a Synthetic continuation at fold time, which
/// `fold_live_threading`'s `append_trailing_args` (targeting only the
/// `while_N`/`.after` fids) therefore did NOT thread the `__la_*` extras into
/// -- becomes a DIRECT self-call `while_N(..)` in `while_N`'s own body, now
/// short the trailing `__la_*` params the fold added to `while_N`'s signature.
/// Re-thread them: for every `LoopBody` carrying trailing `__la_*` params,
/// append those params (by name -- they are the body's own loop-invariant
/// params, in scope) to any self-call that is short by exactly that many args.
/// Arity-guarded and idempotent: self-calls the fold already threaded at fold
/// time (the direct-recursion case) carry the extras and are left untouched.
/// Must run after `cont_inline`, when the direct self-calls exist.
pub fn rethread_loop_self_calls(program: &mut Program) -> Result<(), Stage7Error> {
    let mut targets: Vec<(FunId, Vec<VarId>, usize)> = Vec::new();
    for (fid, f) in program.functions.iter() {
        if !matches!(f.kind, FunctionKind::LoopBody { .. }) {
            continue;
        }
        let params = &f.signature.params;
        let mut la: Vec<VarId> = params
            .iter()
            .rev()
            .take_while(|p| p.name.starts_with("__la_"))
            .map(|p| p.var.clone())
            .collect();
        la.reverse();
        if !la.is_empty() {
            targets.push((*fid, la, params.len()));
        }
    }
    for (fid, la, nparams) in targets {
        let f = program.functions.get_mut(&fid).unwrap();
        rethread_self_call_args(&mut f.body, fid, &la, nparams);
    }
    Ok(())
}

fn rethread_self_call_args(b: &mut Block, self_fid: FunId, la: &[VarId], nparams: usize) {
    for s in b.stmts.iter_mut() {
        match s {
            Stmt::Let { value, .. } => rethread_self_call_args_expr(value, self_fid, la, nparams),
            Stmt::Eval(e) => rethread_self_call_args_expr(e, self_fid, la, nparams),
        }
    }
    match &mut b.tail {
        BlockTail::Value(e) => rethread_self_call_args_expr(e, self_fid, la, nparams),
        BlockTail::Return(e) => rethread_self_call_args_expr(e, self_fid, la, nparams),
        BlockTail::Break { value, .. }
        | BlockTail::Continue { value, .. }
        | BlockTail::ReturnFromBlock { value, .. } => {
            rethread_self_call_args_expr(value, self_fid, la, nparams)
        }
        BlockTail::Abort { code } => rethread_self_call_args_expr(code, self_fid, la, nparams),
    }
}

fn rethread_self_call_args_expr(e: &mut Expr, self_fid: FunId, la: &[VarId], nparams: usize) {
    match e {
        Expr::If {
            then_branch,
            else_branch,
            ..
        } => {
            rethread_self_call_args(then_branch, self_fid, la, nparams);
            rethread_self_call_args(else_branch, self_fid, la, nparams);
        }
        Expr::Match { cases, .. } => {
            for a in cases.iter_mut() {
                rethread_self_call_args(&mut a.body, self_fid, la, nparams);
            }
        }
        Expr::Call { fun, args, .. } => {
            for a in args.iter_mut() {
                rethread_self_call_args_expr(a, self_fid, la, nparams);
            }
            if *fun == self_fid && args.len() + la.len() == nparams {
                for v in la {
                    args.push(Expr::Var(v.clone()));
                }
            }
        }
        _ => {}
    }
}

struct LiveSite {
    cont_fid: FunId,
    cont_type_args: Vec<Type>,
    extra_vars: Vec<VarId>,
}

/// Shared threading for every live-accumulator fold. Generates the
/// `__la_w{i}` / `__la_a{i}` extra-param vars (one per `extra_types`
/// entry), with the selected lifecycle World named `__la_world_w` /
/// `__la_world_a`, and appends `wp` to `while_N` (threading them into its internal
/// `while_N`/`.after` calls and retyping it to AbortResult), and appends
/// `ap` to `.after` (retyping it too).
///
/// `entry_fid` is the function the CONSUMER calls to reach the loop. It
/// is the `while_N` itself for a loop the parent calls directly; for a
/// loop nested in an extracted labeled block it is the Synthetic
/// `<f>.aborts.labeled_N` wrapper, which then also needs its own copy of
/// the extras (`__la_p{i}`), threaded into its single `while_N` call, and
/// its own retype -- otherwise the chain stays accumulator-typed at the
/// only point the consumer can see.
///
/// Returns `(wp, ap)` so the caller can route the accumulator leaves of
/// `while_N` and `.after` into the continuation -- the one part that
/// differs between the nested, world-threaded and labeled-wrapper folds.
fn fold_live_threading(
    program: &mut Program,
    entry_fid: Option<FunId>,
    while_fid: FunId,
    after_fid: FunId,
    extra_types: &[Type],
    lifecycle_extra: Option<usize>,
    abort_result_ty: &Type,
) -> (Vec<VarId>, Vec<VarId>) {
    let n = extra_types.len();
    let wp = extra_param_vars(n, lifecycle_extra, "w");
    let ap = extra_param_vars(n, lifecycle_extra, "a");

    {
        let f = program.functions.get_mut(&while_fid).unwrap();
        for (v, ty) in wp.iter().zip(extra_types.iter()) {
            f.signature.params.push(Param {
                name: v.to_string(),
                var: v.clone(),
                ty: ty.clone(),
            });
        }
        append_trailing_args(&mut f.body, &[while_fid, after_fid], &wp);
        f.signature.return_type = abort_result_ty.clone();
    }

    {
        let f = program.functions.get_mut(&after_fid).unwrap();
        for (v, ty) in ap.iter().zip(extra_types.iter()) {
            f.signature.params.push(Param {
                name: v.to_string(),
                var: v.clone(),
                ty: ty.clone(),
            });
        }
        f.signature.return_type = abort_result_ty.clone();
    }

    if let Some(entry) = entry_fid.filter(|e| *e != while_fid) {
        let pp = extra_param_vars(n, lifecycle_extra, "p");
        let f = program.functions.get_mut(&entry).unwrap();
        for (v, ty) in pp.iter().zip(extra_types.iter()) {
            f.signature.params.push(Param {
                name: v.to_string(),
                var: v.clone(),
                ty: ty.clone(),
            });
        }
        append_trailing_args(&mut f.body, &[while_fid], &pp);
        f.signature.return_type = abort_result_ty.clone();
    }
    (wp, ap)
}

fn extra_param_vars(n: usize, lifecycle_extra: Option<usize>, tag: &str) -> Vec<VarId> {
    (0..n)
        .map(|i| {
            let name = if lifecycle_extra == Some(i) {
                format!("__la_world_{tag}")
            } else {
                format!("__la_{tag}{i}")
            };
            std::rc::Rc::from(name.as_str())
        })
        .collect()
}

fn try_fold_live(
    program: &mut Program,
    while_fid: FunId,
    after_fid: FunId,
    abort_result_ty: &Type,
) {
    // The loop result `while_N(..)` may be consumed in the parent body or in
    // any continuation `cont_N` that return_lift extracted from it. Search
    // every function for the unique `cont(.., while_N(..))` site.
    let mut holder: Option<(FunId, LiveSite)> = None;
    let mut total = 0usize;
    for (fid, f) in program.functions.iter() {
        let mut sites: Vec<LiveSite> = Vec::new();
        collect_sites(&f.body, while_fid, &mut sites);
        total += sites.len();
        if holder.is_none() {
            if let Some(s) = sites.into_iter().next() {
                holder = Some((*fid, s));
            }
        }
    }
    if total != 1 {
        return;
    }
    let (
        holder_fid,
        LiveSite {
            cont_fid,
            cont_type_args,
            extra_vars,
        },
    ) = holder.unwrap();
    if cont_fid == while_fid || cont_fid == after_fid {
        return;
    }

    let (extra_types, lifecycle_extra): (Vec<Type>, Option<usize>) = {
        let Some(cont) = program.functions.get(&cont_fid) else {
            return;
        };
        if cont.signature.params.len() != extra_vars.len() + 1 {
            return;
        }
        let lifecycle_extra = find_world_struct_id(program)
            .and_then(|world_id| {
                crate::stage_04_effects::common::function_lifecycle_world_position(cont, world_id)
            })
            .filter(|index| *index < extra_vars.len());
        let extra_types = cont
            .signature
            .params
            .iter()
            .take(extra_vars.len())
            .map(|p| p.ty.clone())
            .collect();
        (extra_types, lifecycle_extra)
    };

    // Taken before the retype below, so the chain's own (still
    // accumulator-typed) helpers are not mistaken for abort verdicts.
    let abort_result_fns: BTreeSet<FunId> = program
        .functions
        .iter()
        .filter(|(_, f)| f.signature.return_type == *abort_result_ty)
        .map(|(fid, _)| *fid)
        .collect();

    let (_wp, ap) = fold_live_threading(
        program,
        None,
        while_fid,
        after_fid,
        &extra_types,
        lifecycle_extra,
        abort_result_ty,
    );

    // .after: wrap accumulator value-leaves in `cont(ap.., leaf)`.
    {
        let f = program.functions.get_mut(&after_fid).unwrap();
        let prefix: Vec<Expr> = ap.iter().map(|v| Expr::Var(v.clone())).collect();
        let leaves = AbortVerdictLeaves {
            abort_result_ty,
            abort_result_fns: &abort_result_fns,
        };
        wrap_value_leaves_in_cont(&mut f.body, cont_fid, &cont_type_args, &prefix, &leaves);
    }

    // site holder: `Call(cont, [extra.., Call(while_N, loop_args)])`
    //          -> `Call(while_N, [loop_args.., extra..])`.
    {
        let f = program.functions.get_mut(&holder_fid).unwrap();
        rewrite_parent_site(&mut f.body, while_fid, cont_fid);
    }
}

/// World-threaded counterpart of [`try_fold_live`]. The loop helper returns
/// `(val.., World)` -- one or more accumulator values plus a trailing World --
/// so the parent destructures it (`let (val.., world) := while_N(loop_args)`)
/// and tail-calls `cont(extra.., val.., world)` -- the loop result occupies
/// cont's LAST `k+1` args (the `k` values + world), bound through a `let`,
/// rather than being a single nested `while_N(..)` call. The fold:
///   - retypes `while_N` / `.after` to AbortResult, threading the cont's
///     extra args through as fresh trailing params (as in the nested case);
///   - `.after`'s no-abort `(val.., world)` tuple leaf becomes
///     `cont(extra.., val.., world)` (the tuple is UNPACKED into cont's
///     last `k+1` args); non-tuple leaves (abort propagations, already
///     AbortResult) are left untouched;
///   - the parent's `let (val.., world) := while_N(loop_args); cont(extra..,
///     val.., world)` collapses to the tail `while_N(loop_args.., extra..)`.
fn try_fold_live_world(
    program: &mut Program,
    while_fid: FunId,
    after_fid: FunId,
    abort_result_ty: &Type,
) {
    let mut holder: Option<(FunId, WorldSite)> = None;
    let mut total = 0usize;
    for (fid, f) in program.functions.iter() {
        let mut sites: Vec<WorldSite> = Vec::new();
        collect_world_sites(&f.body, while_fid, &mut sites);
        total += sites.len();
        if holder.is_none() {
            if let Some(s) = sites.into_iter().next() {
                holder = Some((*fid, s));
            }
        }
    }
    if total != 1 {
        return;
    }
    let (
        holder_fid,
        WorldSite {
            cont_fid,
            cont_type_args,
            extra_vars,
            val_vars,
            world_var,
        },
    ) = holder.unwrap();
    if cont_fid == while_fid || cont_fid == after_fid {
        return;
    }

    // The loop helper returns `(val.., world)` -- `val_vars.len()` accumulator
    // values plus the trailing World. `k1` is that tuple arity.
    let k1 = val_vars.len() + 1;

    // cont consumes extra_vars + (val.., world): exactly extra_vars.len() + k1 params.
    let (extra_types, lifecycle_extra): (Vec<Type>, Option<usize>) = {
        let Some(cont) = program.functions.get(&cont_fid) else {
            return;
        };
        if cont.signature.params.len() != extra_vars.len() + k1 {
            return;
        }
        let lifecycle_extra = find_world_struct_id(program)
            .and_then(|world_id| {
                crate::stage_04_effects::common::function_lifecycle_world_position(cont, world_id)
            })
            .filter(|index| *index < extra_vars.len());
        let extra_types = cont
            .signature
            .params
            .iter()
            .take(extra_vars.len())
            .map(|p| p.ty.clone())
            .collect();
        (extra_types, lifecycle_extra)
    };

    let (_wp, ap) = fold_live_threading(
        program,
        None,
        while_fid,
        after_fid,
        &extra_types,
        lifecycle_extra,
        abort_result_ty,
    );

    // .after: unpack `(val.., world)` tuple leaves into
    // `cont(ap.., val.., world)` (arity k1, per the guard above).
    {
        let f = program.functions.get_mut(&after_fid).unwrap();
        let prefix: Vec<Expr> = ap.iter().map(|v| Expr::Var(v.clone())).collect();
        wrap_tuple_leaves_in_cont(&mut f.body, cont_fid, &cont_type_args, &prefix, k1);
    }

    // holder: drop `let (val.., world) := while_N(loop_args)` and replace the
    // tail `cont(extra.., val.., world)` with `while_N(loop_args.., extra..)`.
    {
        let f = program.functions.get_mut(&holder_fid).unwrap();
        rewrite_world_site(&mut f.body, while_fid, cont_fid, &val_vars, &world_var);
    }
}

struct WorldSite {
    cont_fid: FunId,
    cont_type_args: Vec<Type>,
    extra_vars: Vec<VarId>,
    val_vars: Vec<VarId>,
    world_var: VarId,
}

/// Collect every world-threaded live-accumulator site reachable from `b`: a
/// block that binds `let (val.., world) := while_fid(loop_args)` and whose tail
/// is `cont(extra.., val.., world)` (extra all plain Vars). Recurses into
/// If/Match arm blocks.
fn collect_world_sites(b: &Block, while_fid: FunId, out: &mut Vec<WorldSite>) {
    if let Some(site) = match_world_site(b, while_fid) {
        out.push(site);
    }
    match &b.tail {
        BlockTail::Value(e) => collect_world_sites_expr(e, while_fid, out),
        BlockTail::Return(e) => collect_world_sites_expr(e, while_fid, out),
        _ => {}
    }
}

fn collect_world_sites_expr(e: &Expr, while_fid: FunId, out: &mut Vec<WorldSite>) {
    match e {
        Expr::If {
            then_branch,
            else_branch,
            ..
        } => {
            collect_world_sites(then_branch, while_fid, out);
            collect_world_sites(else_branch, while_fid, out);
        }
        Expr::Match { cases, .. } => {
            for a in cases.iter() {
                collect_world_sites(&a.body, while_fid, out);
            }
        }
        _ => {}
    }
}

fn match_world_site(b: &Block, while_fid: FunId) -> Option<WorldSite> {
    // Find the `let (p_0, .., p_k) := while_fid(loop_args)` destructure in this
    // block. It binds `k >= 1` accumulator values plus a trailing World, so the
    // pattern has `>= 2` named slots. `loop_vars` is `[val_0, .., val_{k-1}, world]`.
    let loop_vars: Vec<VarId> = b.stmts.iter().find_map(|s| match s {
        Stmt::Let { pattern, value } => {
            if pattern.len() >= 2
                && pattern.iter().all(|p| p.is_some())
                && matches!(value, Expr::Call { fun, .. } if *fun == while_fid)
            {
                Some(pattern.iter().map(|p| p.clone().unwrap()).collect())
            } else {
                None
            }
        }
        _ => None,
    })?;
    let k1 = loop_vars.len();

    let tail_expr: &Expr = match &b.tail {
        BlockTail::Value(e) => e,
        BlockTail::Return(e) => &**e,
        _ => return None,
    };
    let (cont_fid, cont_type_args, args) = match tail_expr {
        Expr::Call {
            fun,
            type_args,
            args,
        } => (*fun, type_args.clone(), args),
        _ => return None,
    };
    if cont_fid == while_fid || args.len() < k1 {
        return None;
    }
    // The tail's last `k1` args must be exactly the destructured loop vars in
    // order (`val.., world`); the leading args are the extras (all plain Vars).
    let split = args.len() - k1;
    for (a, lv) in args[split..].iter().zip(loop_vars.iter()) {
        match a {
            Expr::Var(v) if &**v == &**lv => {}
            _ => return None,
        }
    }
    let mut extra_vars = Vec::new();
    for a in &args[..split] {
        match a {
            Expr::Var(v) => extra_vars.push(v.clone()),
            _ => return None,
        }
    }
    let world_var = loop_vars[k1 - 1].clone();
    let val_vars = loop_vars[..k1 - 1].to_vec();
    Some(WorldSite {
        cont_fid,
        cont_type_args,
        extra_vars,
        val_vars,
        world_var,
    })
}

/// Unpack every TUPLE value-leaf `(a, b, ..)` of `b` into
/// `Call(cont, [prefix.., a, b, ..])`. Non-tuple value-leaves (already-typed
/// abort propagations) and `Return` tails are left untouched.
fn wrap_tuple_leaves_in_cont(
    b: &mut Block,
    cont: FunId,
    type_args: &[Type],
    prefix: &[Expr],
    want_arity: usize,
) {
    if let BlockTail::Value(e) = &mut b.tail {
        wrap_leaf_expr(e, cont, type_args, prefix, want_arity);
    }
}

/// Descend a value-position expression to the accumulator leaf and wrap it.
///
/// The aborts-variant `.after` tail is `Tuple([ Match{ NoAbort => ... =>
/// Tuple([acc, world]), Aborted => Return } ])` -- the real `(acc, world)`
/// pair sits DEEP inside abort-conditional matches, itself wrapped in a
/// spurious singleton tuple (a 1-tuple is semantically its element). So:
///   - strip singleton `Tuple([x])` wrappers (when the accumulator arity is
///     not 1) to reach the control-flow / accumulator inside;
///   - recurse through `If` / `Match` arms;
///   - wrap a `Tuple` of EXACTLY `want_arity` elements (the `(acc, world)`
///     accumulator pair) into `cont(prefix.., acc, world)`;
///   - leave everything else (abort propagations -- non-tuple value leaves
///     and `Return` tails) untouched.
fn wrap_leaf_expr(
    e: &mut Expr,
    cont: FunId,
    type_args: &[Type],
    prefix: &[Expr],
    want_arity: usize,
) {
    // Peel spurious singleton tuples (`(x)` == `x`) so we descend into the
    // control-flow / accumulator they wrap. Never peel when the accumulator
    // itself is a 1-tuple.
    if want_arity != 1 {
        while matches!(e, Expr::Tuple(elems) if elems.len() == 1) {
            if let Expr::Tuple(elems) = e {
                let inner = elems.remove(0);
                *e = inner;
            }
        }
    }
    match e {
        Expr::If {
            then_branch,
            else_branch,
            ..
        } => {
            wrap_tuple_leaves_in_cont(then_branch, cont, type_args, prefix, want_arity);
            wrap_tuple_leaves_in_cont(else_branch, cont, type_args, prefix, want_arity);
        }
        Expr::Match { cases, .. } => {
            for a in cases.iter_mut() {
                wrap_tuple_leaves_in_cont(&mut a.body, cont, type_args, prefix, want_arity);
            }
        }
        Expr::Tuple(elems) if elems.len() == want_arity => {
            let acc = std::mem::replace(e, Expr::Unit);
            let elems = match acc {
                Expr::Tuple(elems) => elems,
                _ => unreachable!(),
            };
            let mut args: Vec<Expr> = prefix.to_vec();
            args.extend(elems);
            *e = Expr::Call {
                fun: cont,
                type_args: type_args.to_vec(),
                args,
            };
        }
        _ => {}
    }
}

/// Find the (unique) block whose tail is `cont(extra.., val, world)` and which
/// binds `let (val, world) := while_fid(loop_args)`; drop that let and replace
/// the tail with `while_fid(loop_args.., extra..)`. Recurses through If/Match.
fn rewrite_world_site(
    b: &mut Block,
    while_fid: FunId,
    cont_fid: FunId,
    val_vars: &[VarId],
    world_var: &VarId,
) -> bool {
    let k1 = val_vars.len() + 1;
    // Is THIS block's tail the `cont(extra.., val.., world)` call? (deref the
    // Box for a `Return` tail; `Value` holds the Expr directly.)
    let tail_info: Option<(bool, Vec<Expr>)> = {
        let tail_expr: Option<(&Expr, bool)> = match &b.tail {
            BlockTail::Value(e) => Some((e, false)),
            BlockTail::Return(e) => Some((&**e, true)),
            _ => None,
        };
        tail_expr.and_then(|(e, is_ret)| match e {
            Expr::Call { fun, args, .. }
                if *fun == cont_fid
                    && args.len() >= k1
                    && trailing_matches_loop_vars(args, val_vars, world_var) =>
            {
                Some((is_ret, args.clone()))
            }
            _ => None,
        })
    };
    if let Some((is_return, cont_args)) = tail_info {
        let mut found: Option<(usize, Vec<Expr>, Vec<Type>)> = None;
        for (i, s) in b.stmts.iter().enumerate() {
            if let Stmt::Let { pattern, value } = s {
                if pattern_matches_loop_vars(pattern, val_vars, world_var) {
                    if let Expr::Call {
                        fun,
                        args,
                        type_args,
                    } = value
                    {
                        if *fun == while_fid {
                            found = Some((i, args.clone(), type_args.clone()));
                            break;
                        }
                    }
                }
            }
        }
        if let Some((idx, loop_args, while_tas)) = found {
            let extra = cont_args[..cont_args.len() - k1].to_vec();
            b.stmts.remove(idx);
            let mut new_args = loop_args;
            new_args.extend(extra);
            let new_call = Expr::Call {
                fun: while_fid,
                type_args: while_tas,
                args: new_args,
            };
            b.tail = if is_return {
                BlockTail::Return(Box::new(new_call))
            } else {
                BlockTail::Value(new_call)
            };
            return true;
        }
    }
    match &mut b.tail {
        BlockTail::Value(e) => rewrite_world_site_expr(e, while_fid, cont_fid, val_vars, world_var),
        BlockTail::Return(e) => {
            rewrite_world_site_expr(e, while_fid, cont_fid, val_vars, world_var)
        }
        _ => false,
    }
}

/// The last `val_vars.len() + 1` of `args` are exactly `val.., world` as plain
/// `Var`s in order.
fn trailing_matches_loop_vars(args: &[Expr], val_vars: &[VarId], world_var: &VarId) -> bool {
    let k1 = val_vars.len() + 1;
    if args.len() < k1 {
        return false;
    }
    let split = args.len() - k1;
    for (a, lv) in args[split..]
        .iter()
        .zip(val_vars.iter().chain(std::iter::once(world_var)))
    {
        match a {
            Expr::Var(v) if &**v == &**lv => {}
            _ => return false,
        }
    }
    true
}

/// `pattern` binds exactly `val.., world` (length `val_vars.len() + 1`).
fn pattern_matches_loop_vars(
    pattern: &[Option<VarId>],
    val_vars: &[VarId],
    world_var: &VarId,
) -> bool {
    let k1 = val_vars.len() + 1;
    if pattern.len() != k1 {
        return false;
    }
    for (p, lv) in pattern
        .iter()
        .zip(val_vars.iter().chain(std::iter::once(world_var)))
    {
        if p.as_deref() != Some(&**lv) {
            return false;
        }
    }
    true
}

fn rewrite_world_site_expr(
    e: &mut Expr,
    while_fid: FunId,
    cont_fid: FunId,
    val_vars: &[VarId],
    world_var: &VarId,
) -> bool {
    match e {
        Expr::If {
            then_branch,
            else_branch,
            ..
        } => {
            rewrite_world_site(then_branch, while_fid, cont_fid, val_vars, world_var)
                || rewrite_world_site(else_branch, while_fid, cont_fid, val_vars, world_var)
        }
        Expr::Match { cases, .. } => {
            for a in cases.iter_mut() {
                if rewrite_world_site(&mut a.body, while_fid, cont_fid, val_vars, world_var) {
                    return true;
                }
            }
            false
        }
        _ => false,
    }
}

/// Collect every tail-position `Call(cont, [Var.., Call(while_fid, ..)])`
/// whose last arg is the while_fid call and whose other args are plain Vars.
fn collect_sites(b: &Block, while_fid: FunId, out: &mut Vec<LiveSite>) {
    match &b.tail {
        BlockTail::Value(e) => collect_sites_expr(e, while_fid, out),
        BlockTail::Return(e) => collect_sites_expr(e, while_fid, out),
        _ => {}
    }
}

fn collect_sites_expr(e: &Expr, while_fid: FunId, out: &mut Vec<LiveSite>) {
    match e {
        Expr::If {
            then_branch,
            else_branch,
            ..
        } => {
            collect_sites(then_branch, while_fid, out);
            collect_sites(else_branch, while_fid, out);
        }
        Expr::Match { cases, .. } => {
            for a in cases.iter() {
                collect_sites(&a.body, while_fid, out);
            }
        }
        Expr::Call {
            fun,
            type_args,
            args,
        } => {
            if *fun == while_fid {
                return;
            }
            let Some((last, head)) = args.split_last() else {
                return;
            };
            let last_is_while = matches!(last, Expr::Call { fun: f2, .. } if *f2 == while_fid);
            if !last_is_while || !head.iter().all(|a| matches!(a, Expr::Var(_))) {
                return;
            }
            let extra_vars = head
                .iter()
                .map(|a| match a {
                    Expr::Var(v) => v.clone(),
                    _ => unreachable!(),
                })
                .collect();
            out.push(LiveSite {
                cont_fid: *fun,
                cont_type_args: type_args.clone(),
                extra_vars,
            });
        }
        _ => {}
    }
}

/// Append `extra` (as `Var`s) to every `Call(f, ..)` with `f` in `targets`.
fn append_trailing_args(b: &mut Block, targets: &[FunId], extra: &[VarId]) {
    for s in b.stmts.iter_mut() {
        match s {
            Stmt::Let { value, .. } => append_trailing_args_expr(value, targets, extra),
            Stmt::Eval(e) => append_trailing_args_expr(e, targets, extra),
        }
    }
    match &mut b.tail {
        BlockTail::Value(e) => append_trailing_args_expr(e, targets, extra),
        BlockTail::Return(e) => append_trailing_args_expr(e, targets, extra),
        BlockTail::Break { value, .. }
        | BlockTail::Continue { value, .. }
        | BlockTail::ReturnFromBlock { value, .. } => {
            append_trailing_args_expr(value, targets, extra)
        }
        BlockTail::Abort { code } => append_trailing_args_expr(code, targets, extra),
    }
}

fn append_trailing_args_expr(e: &mut Expr, targets: &[FunId], extra: &[VarId]) {
    match e {
        Expr::If {
            then_branch,
            else_branch,
            ..
        } => {
            append_trailing_args(then_branch, targets, extra);
            append_trailing_args(else_branch, targets, extra);
        }
        Expr::Match { cases, .. } => {
            for a in cases.iter_mut() {
                append_trailing_args(&mut a.body, targets, extra);
            }
        }
        Expr::Call { fun, args, .. } => {
            for a in args.iter_mut() {
                append_trailing_args_expr(a, targets, extra);
            }
            if targets.contains(fun) {
                for v in extra {
                    args.push(Expr::Var(v.clone()));
                }
            }
        }
        _ => {}
    }
}

/// What already delivers an abort verdict in a still accumulator-typed
/// `.after`. `return_collapse` turns a function-tail `Return(Aborted c)` into
/// a plain value leaf, so "every value leaf is the accumulator" does not hold:
/// a post-loop callee-abort check leaves `Aborted(c) => Aborted c` next to the
/// accumulator arm (blast `allocation::add_protocol`, whose second `fold!`
/// ends in `vector::destroy_empty`).
struct AbortVerdictLeaves<'a> {
    abort_result_ty: &'a Type,
    abort_result_fns: &'a BTreeSet<FunId>,
}

impl AbortVerdictLeaves<'_> {
    fn contains(&self, leaf: &Expr) -> bool {
        match leaf {
            Expr::Pack {
                struct_id,
                type_args,
                ..
            } => {
                let packed = Type::Struct {
                    struct_id: *struct_id,
                    type_args: type_args.clone(),
                };
                packed == *self.abort_result_ty
            }
            Expr::Call { fun, .. } => self.abort_result_fns.contains(fun),
            _ => false,
        }
    }
}

/// Wrap every accumulator value-leaf of `b` in `Call(cont, [prefix.., leaf])`.
/// `Return` tails (the abort exits) and value leaves that already deliver an
/// abort verdict are left untouched: the latter are correct as they stand once
/// `.after` is retyped, and feeding one to `cont` would put an `AbortResult`
/// in the accumulator's parameter.
fn wrap_value_leaves_in_cont(
    b: &mut Block,
    cont: FunId,
    type_args: &[Type],
    prefix: &[Expr],
    verdicts: &AbortVerdictLeaves,
) {
    if let BlockTail::Value(e) = &mut b.tail {
        match e {
            Expr::If {
                then_branch,
                else_branch,
                ..
            } => {
                wrap_value_leaves_in_cont(then_branch, cont, type_args, prefix, verdicts);
                wrap_value_leaves_in_cont(else_branch, cont, type_args, prefix, verdicts);
            }
            Expr::Match { cases, .. } => {
                for a in cases.iter_mut() {
                    wrap_value_leaves_in_cont(&mut a.body, cont, type_args, prefix, verdicts);
                }
            }
            leaf if verdicts.contains(leaf) => {}
            leaf => {
                let acc = std::mem::replace(leaf, Expr::Unit);
                let mut args: Vec<Expr> = prefix.to_vec();
                args.push(acc);
                *leaf = Expr::Call {
                    fun: cont,
                    type_args: type_args.to_vec(),
                    args,
                };
            }
        }
    }
}

/// Replace the first tail-position
/// `Call(cont, [extra.., Call(while_fid, loop_args)])` with
/// `Call(while_fid, [loop_args.., extra..])`.
fn rewrite_parent_site(b: &mut Block, while_fid: FunId, cont_fid: FunId) -> bool {
    match &mut b.tail {
        BlockTail::Value(e) => rewrite_parent_site_expr(e, while_fid, cont_fid),
        BlockTail::Return(e) => rewrite_parent_site_expr(e, while_fid, cont_fid),
        _ => false,
    }
}

fn rewrite_parent_site_expr(e: &mut Expr, while_fid: FunId, cont_fid: FunId) -> bool {
    match e {
        Expr::If {
            then_branch,
            else_branch,
            ..
        } => {
            rewrite_parent_site(then_branch, while_fid, cont_fid)
                || rewrite_parent_site(else_branch, while_fid, cont_fid)
        }
        Expr::Match { cases, .. } => {
            for a in cases.iter_mut() {
                if rewrite_parent_site(&mut a.body, while_fid, cont_fid) {
                    return true;
                }
            }
            false
        }
        Expr::Call { fun, args, .. } if *fun == cont_fid => {
            let Some(last) = args.last() else {
                return false;
            };
            let Expr::Call {
                fun: wf,
                type_args: w_type_args,
                args: loop_args,
            } = last
            else {
                return false;
            };
            if *wf != while_fid {
                return false;
            }
            let w_type_args = w_type_args.clone();
            let mut new_args = loop_args.clone();
            for a in &args[..args.len() - 1] {
                new_args.push(a.clone());
            }
            *e = Expr::Call {
                fun: while_fid,
                type_args: w_type_args,
                args: new_args,
            };
            true
        }
        _ => false,
    }
}

fn block_has_return(b: &Block) -> bool {
    if matches!(b.tail, BlockTail::Return(_)) {
        return true;
    }
    for s in &b.stmts {
        let e = match s {
            Stmt::Let { value, .. } => value,
            Stmt::Eval(e) => e,
        };
        if expr_has_return(e) {
            return true;
        }
    }
    match &b.tail {
        BlockTail::Value(e) => expr_has_return(e),
        BlockTail::Return(e) => expr_has_return(e),
        _ => false,
    }
}

fn expr_has_return(e: &Expr) -> bool {
    match e {
        Expr::If {
            then_branch,
            else_branch,
            ..
        } => block_has_return(then_branch) || block_has_return(else_branch),
        Expr::Match { cases, .. } => cases.iter().any(|a| block_has_return(&a.body)),
        _ => false,
    }
}
