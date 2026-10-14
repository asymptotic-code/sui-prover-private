// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Frame lemmas (unified-backend design §5.4, Phase 4): per-function df-store
//! footprints and generator-proven frame theorems for world-mode packages.
//!
//! For every threaded value face `F` whose body the walk below can express,
//! the pass records a [`FrameLemmaSet`]; the renderer then emits, right after
//! the def (before any `attribute [irreducible]` line):
//!
//! * `@[reducible] def F.dfFootprint <params> : List (Prover.World.DfKey TyCode)`
//!   — the concrete key sources F writes, callee footprints composed by
//!   substitution (`Callee.dfFootprint args'` sublists — call-not-copy);
//! * `theorem F.frame_thm … : Prover.World.FrameDf __world ((F … __world).world)
//!   (F.dfFootprint …)` — a combinator tree over the `Prover.World.FrameDf`
//!   prelude vocabulary through the per-project wrapper leaves
//!   (`World.frame_setDf` / `frame_eraseDf` singletons, `frame_putOwned` /
//!   `frame_putShared` / `frame_putFrozen` / `frame_emitEvent` df-preserving
//!   `[]` leaves), callee `frame_thm`s at call sites, and `FrameDf.comp` /
//!   `FrameDf.bite` / `FrameDf.ite_pair` for sequencing and branches. The
//!   proof never unfolds callee bodies — footprints compose structurally,
//!   exactly like `AbortsProofNode` bundles.
//! * `theorem F.frame_df_out … (h : DfKey.mk p (.of k) ∉ F.dfFootprint …) :
//!   ((F …).world).getDf p k = __world.getDf p k` — the user-facing corollary
//!   (plus an unconditional `F.frame_df` when the footprint is empty).
//!
//! Render-sensitivity containment (§5.6 "WriteBack render sensitivity"):
//! world values and stored values are IMPLICIT in every leaf — the elaborator
//! recovers them from the goal by unfolding the `@[reducible]` def — so
//! `WriteBack`-tainted expressions are never copied into a rendered proof
//! term or statement. Only uid/key footprint sources and callee value
//! arguments are rendered, and any of those containing mutable-machinery
//! nodes (or an unsubstitutable / oversized form) DROPS the lemma LOUDLY
//! (a stderr warning naming the function); the system degrades to Phase-2/3
//! modularity. No unprovable or `sorry`'d lemma is ever emitted.
//!
//! Inert unless `Program::world_functions` is set (`world_mode` packages).

use super::decompose_aborts::{approx_size, bundle_subst, BundleSubst};
use crate::data::functions::Parameter;
use crate::data::types::{TempId, Type};
use crate::{FunctionID, IRNode, Program};
use std::collections::{BTreeMap, BTreeSet};

/// Cap on any stored substitution and on rendered footprint/argument
/// expressions (mirrors the bundle walk's `SUBST_MAX`).
const SUBST_MAX: usize = 6_000;

/// One generated frame-lemma set. The footprint expression is DERIVED from
/// the proof tree (each node contributes its own `S` shape), so statement and
/// proof can never drift.
#[derive(Debug, Clone)]
pub struct FrameLemmaSet {
    pub fn_id: FunctionID,
    pub proof: FrameProofNode,
    /// The world component of the result: `true` ⇒ `(F …).2`, `false` ⇒ the
    /// result itself (originally-unit functions return `World` alone).
    pub world_proj_snd: bool,
    /// Value-parameter subset (parent order) free in the footprint expression.
    pub footprint_params: Vec<Parameter>,
}

/// The df-preserving world natives.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DfPreserveOp {
    PutOwned,
    PutShared,
    PutFrozen,
    EmitEvent,
}

impl DfPreserveOp {
    pub fn wrapper_lemma(&self) -> &'static str {
        match self {
            DfPreserveOp::PutOwned => "World.frame_putOwned",
            DfPreserveOp::PutShared => "World.frame_putShared",
            DfPreserveOp::PutFrozen => "World.frame_putFrozen",
            DfPreserveOp::EmitEvent => "World.frame_emitEvent",
        }
    }
}

/// Structural frame proof, rendered as a direct term over the
/// `Prover.World.FrameDf` prelude combinators + the per-project
/// `World.frame_*` wrapper leaves. Leaf worlds/values are implicit (inferred
/// from the goal); only uid/key sources and callee value args are rendered.
#[derive(Debug, Clone)]
pub enum FrameProofNode {
    /// `Prover.World.FrameDf.refl __world` — the world passes through.
    Refl,
    /// `World.frame_setDf K V uid k` — footprint `[DfKey.mk (uidNat uid) (.of k)]`.
    SetDf {
        key_ty: Type,
        val_ty: Type,
        uid: IRNode,
        key: IRNode,
    },
    /// `World.frame_eraseDf K V uid k` — same singleton footprint.
    EraseDf {
        key_ty: Type,
        val_ty: Type,
        uid: IRNode,
        key: IRNode,
    },
    /// `World.frame_put*/frame_emitEvent T` — df-preserving, footprint `[]`.
    DfPreserve { op: DfPreserveOp, obj_ty: Type },
    /// `<Callee>.frame_thm <value args…> _` (trailing world inferred) —
    /// footprint `Callee.dfFootprint <args'>`.
    Callee {
        function: FunctionID,
        /// Call-site type args (rendered positionally — generated defs take
        /// their type params explicitly). May reference the CALLER's type
        /// params, which the lemma statement binds.
        type_args: Vec<Type>,
        /// Callee value args EXCLUDING the trailing `__world` argument.
        args: Vec<IRNode>,
    },
    /// `Prover.World.FrameDf.comp a b` — footprint `(S_a ++ S_b)`.
    Comp(Box<FrameProofNode>, Box<FrameProofNode>),
    /// `Prover.World.FrameDf.ite_pair t e` — branch split under the result
    /// pair projection; footprint `(S_t ++ S_e)`.
    ItePair(Box<FrameProofNode>, Box<FrameProofNode>),
    /// `Prover.World.FrameDf.bite t e` — branch split on a bare-World tail.
    BiteWorld(Box<FrameProofNode>, Box<FrameProofNode>),
}

impl FrameProofNode {
    /// Whether the footprint this node contributes is syntactically empty.
    pub fn footprint_is_empty(&self) -> bool {
        match self {
            FrameProofNode::Refl | FrameProofNode::DfPreserve { .. } => true,
            FrameProofNode::SetDf { .. } | FrameProofNode::EraseDf { .. } => false,
            FrameProofNode::Callee { .. } => false,
            FrameProofNode::Comp(a, b)
            | FrameProofNode::ItePair(a, b)
            | FrameProofNode::BiteWorld(a, b) => a.footprint_is_empty() && b.footprint_is_empty(),
        }
    }

    fn footprint_free_vars(&self, out: &mut BTreeSet<TempId>, program: &Program) {
        match self {
            FrameProofNode::Refl | FrameProofNode::DfPreserve { .. } => {}
            FrameProofNode::SetDf { uid, key, .. } | FrameProofNode::EraseDf { uid, key, .. } => {
                out.extend(uid.free_vars());
                out.extend(key.free_vars());
            }
            FrameProofNode::Callee { function, args, .. } => {
                let Some(set) = program.frame_lemmas.iter().find(|s| s.fn_id == *function) else {
                    panic!("frame_lemmas: callee {} has no recorded set", function);
                };
                let callee = program.functions.get(function);
                for fp in &set.footprint_params {
                    let idx = callee
                        .signature
                        .parameters
                        .iter()
                        .position(|p| p.ssa_value == fp.ssa_value)
                        .expect("footprint param is a callee param");
                    out.extend(args[idx].free_vars());
                }
            }
            FrameProofNode::Comp(a, b)
            | FrameProofNode::ItePair(a, b)
            | FrameProofNode::BiteWorld(a, b) => {
                a.footprint_free_vars(out, program);
                b.footprint_free_vars(out, program);
            }
        }
    }
}

fn world_var() -> TempId {
    super::world_threading::WORLD_VAR.into()
}

pub fn compute_frame_lemmas(program: &mut Program) {
    let Some(world) = program.world_functions.clone() else {
        return;
    };
    let world_ty = world.world_type();

    // Candidates: threaded, monomorphic, non-recursive value faces.
    let candidates: Vec<FunctionID> = program
        .functions
        .iter_ids()
        .filter(|id| {
            let f = program.functions.get(id);
            if f.is_native
                || f.theorem.is_some()
                || f.mutual_group_id.is_some()
                || !f.signature.proof_params.is_empty()
            {
                return false;
            }
            if !f
                .signature
                .parameters
                .iter()
                .any(|p| p.name == super::world_threading::WORLD_VAR)
            {
                return false;
            }
            // Immutable references render transparently as their inner type
            // (post-threading value faces never dereference-mutate them), so
            // only MutableReference params disqualify.
            if f.signature
                .parameters
                .iter()
                .any(|p| matches!(p.param_type, Type::MutableReference(_, _)))
            {
                return false;
            }
            world_proj(&f.signature.return_type, &world_ty).is_some()
        })
        .collect();

    // Callee frame theorems must exist before callers compose them: iterate
    // to a fixpoint, deferring functions whose candidate callees are pending.
    let candidate_set: BTreeSet<FunctionID> = candidates.iter().copied().collect();
    let mut dropped: BTreeSet<FunctionID> = BTreeSet::new();
    let mut done: BTreeSet<FunctionID> = BTreeSet::new();
    loop {
        let mut progressed = false;
        for &fid in &candidates {
            if done.contains(&fid) || dropped.contains(&fid) {
                continue;
            }
            match analyze_fn(program, fid, &world_ty, &candidate_set, &done, &dropped) {
                Ok(Some(set)) => {
                    program.frame_lemmas.push(set);
                    done.insert(fid);
                    progressed = true;
                }
                Ok(None) => {} // callee pending — retry next round
                Err(reason) => {
                    eprintln!(
                        "warning: frame lemma dropped for `{}`: {} (degrading to contract-only modularity)",
                        program.functions.get(&fid).name,
                        reason
                    );
                    dropped.insert(fid);
                    progressed = true;
                }
            }
        }
        if !progressed {
            break;
        }
    }
    for &fid in &candidates {
        if !done.contains(&fid) && !dropped.contains(&fid) {
            eprintln!(
                "warning: frame lemma dropped for `{}`: unresolved callee dependency cycle",
                program.functions.get(&fid).name
            );
        }
    }
}

/// `Some(true)` — world at `.2` of a pair; `Some(false)` — the result IS the
/// world; `None` — not a threaded value-face return shape.
fn world_proj(ret: &Type, world_ty: &Type) -> Option<bool> {
    if ret == world_ty {
        return Some(false);
    }
    if let Type::Tuple(elems) = ret {
        if elems.len() == 2 && &elems[1] == world_ty {
            return Some(true);
        }
    }
    None
}

struct WalkCtx<'a> {
    program: &'a Program,
    world: &'a super::world_threading::WorldFunctions,
    world_ty: &'a Type,
    candidate_set: &'a BTreeSet<FunctionID>,
    done: &'a BTreeSet<FunctionID>,
    dropped: &'a BTreeSet<FunctionID>,
}

#[derive(Clone)]
struct WalkState {
    subst: BundleSubst,
}

enum WalkErr {
    /// Hard drop, with reason.
    Drop(String),
    /// A candidate callee has no set yet — retry after it is processed.
    Pending,
}

/// `Ok(Some(set))` — recorded; `Ok(None)` — deferred; `Err` — dropped.
fn analyze_fn(
    program: &Program,
    fid: FunctionID,
    world_ty: &Type,
    candidate_set: &BTreeSet<FunctionID>,
    done: &BTreeSet<FunctionID>,
    dropped: &BTreeSet<FunctionID>,
) -> Result<Option<FrameLemmaSet>, String> {
    let f = program.functions.get(&fid);
    if f.body.calls().any(|c| c == fid) {
        return Err("self-recursive body".to_string());
    }
    let world = program.world_functions.as_ref().expect("world mode");
    let ctx = WalkCtx {
        program,
        world,
        world_ty,
        candidate_set,
        done,
        dropped,
    };
    let proj_snd = world_proj(&f.signature.return_type, world_ty).expect("candidate shape");
    let state = WalkState {
        subst: BTreeMap::new(),
    };
    match tail_proof(&ctx, &f.body, state, proj_snd) {
        Ok(proof) => {
            // Every footprint free var must be a parent value param.
            let mut free: BTreeSet<TempId> = BTreeSet::new();
            proof.footprint_free_vars(&mut free, program);
            let mut footprint_params: Vec<Parameter> = Vec::new();
            for p in &f.signature.parameters {
                if free.contains(&p.ssa_value) {
                    if p.name == super::world_threading::WORLD_VAR {
                        return Err("footprint mentions the world value".to_string());
                    }
                    footprint_params.push(p.clone());
                    free.remove(&p.ssa_value);
                }
            }
            if !free.is_empty() {
                return Err(format!(
                    "footprint mentions non-param temps {:?}",
                    free.iter().map(|v| v.to_string()).collect::<Vec<_>>()
                ));
            }
            Ok(Some(FrameLemmaSet {
                fn_id: fid,
                proof,
                world_proj_snd: proj_snd,
                footprint_params,
            }))
        }
        Err(WalkErr::Pending) => Ok(None),
        Err(WalkErr::Drop(reason)) => Err(reason),
    }
}

/// Mutable-machinery nodes render registry-type-sensitively (the documented
/// `WriteBack` hazard) — a rendered statement/argument must never carry one.
fn render_sensitive(expr: &IRNode) -> bool {
    expr.iter().any(|n| {
        matches!(
            n,
            IRNode::WriteBack { .. }
                | IRNode::MutableCompose { .. }
                | IRNode::MutableBorrow { .. }
                | IRNode::WriteRef { .. }
                | IRNode::ReadRef(_)
        )
    })
}

/// Substitute an expression that will be RENDERED (footprint source or callee
/// value argument): must be expressible over params, sized, and free of
/// render-sensitive nodes.
fn subst_rendered(expr: &IRNode, subst: &BundleSubst, what: &str) -> Result<IRNode, WalkErr> {
    match bundle_subst(expr, subst) {
        Some(e) if approx_size(&e) > SUBST_MAX => {
            Err(WalkErr::Drop(format!("{} expression oversized", what)))
        }
        Some(e) if render_sensitive(&e) => Err(WalkErr::Drop(format!(
            "{} expression carries mutable-writeback machinery",
            what
        ))),
        Some(e) => Ok(e),
        None => Err(WalkErr::Drop(format!(
            "{} expression not expressible over params",
            what
        ))),
    }
}

/// Chain `prev` and `step` (first step stands alone).
fn chain(acc: Option<FrameProofNode>, step: FrameProofNode) -> Option<FrameProofNode> {
    Some(match acc {
        None => step,
        Some(prev) => FrameProofNode::Comp(Box::new(prev), Box::new(step)),
    })
}

fn finish(acc: Option<FrameProofNode>) -> FrameProofNode {
    acc.unwrap_or(FrameProofNode::Refl)
}

/// The callee's frame-lemma set must exist; distinguishes pending candidates
/// from permanently unavailable callees.
fn callee_frame(ctx: &WalkCtx, callee: FunctionID) -> Result<(), WalkErr> {
    if ctx.done.contains(&callee) {
        return Ok(());
    }
    if ctx.candidate_set.contains(&callee) && !ctx.dropped.contains(&callee) {
        return Err(WalkErr::Pending);
    }
    Err(WalkErr::Drop(format!(
        "callee `{}` has no frame lemma",
        ctx.program.functions.get(&callee).name
    )))
}

/// A call to a world-threaded value-face function (candidate or not).
fn is_threaded_value_callee(ctx: &WalkCtx, function: FunctionID) -> bool {
    let f = ctx.program.functions.get(&function);
    if f.is_native {
        return false;
    }
    f.signature
        .parameters
        .iter()
        .any(|p| p.name == super::world_threading::WORLD_VAR)
        && world_proj(&f.signature.return_type, ctx.world_ty).is_some()
}

/// A world-MUTATING call (typed reads `getDf`/`hasDf` are fine anywhere).
fn touches_world(ctx: &WalkCtx, node: &IRNode) -> bool {
    node.calls().any(|c| {
        c == ctx.world.set_df
            || c == ctx.world.erase_df
            || c == ctx.world.put_owned
            || c == ctx.world.put_shared
            || c == ctx.world.put_frozen
            || c == ctx.world.emit_event
            || is_threaded_value_callee(ctx, c)
    })
}

fn df_preserve_op(ctx: &WalkCtx, function: FunctionID) -> Option<DfPreserveOp> {
    if function == ctx.world.put_owned {
        Some(DfPreserveOp::PutOwned)
    } else if function == ctx.world.put_shared {
        Some(DfPreserveOp::PutShared)
    } else if function == ctx.world.put_frozen {
        Some(DfPreserveOp::PutFrozen)
    } else if function == ctx.world.emit_event {
        Some(DfPreserveOp::EmitEvent)
    } else {
        None
    }
}

/// Build the callee step: substituted value args (the trailing `__world`
/// argument is elided — the leaf renders `_` there and the elaborator infers
/// it from the goal).
fn callee_step(
    ctx: &WalkCtx,
    function: FunctionID,
    type_args: &[Type],
    args: &[IRNode],
    st: &WalkState,
) -> Result<FrameProofNode, WalkErr> {
    callee_frame(ctx, function)?;
    let callee = ctx.program.functions.get(&function);
    assert_eq!(
        args.len(),
        callee.signature.parameters.len(),
        "threaded callee call arity"
    );
    assert_eq!(
        callee.signature.parameters.last().map(|p| p.name.as_str()),
        Some(super::world_threading::WORLD_VAR),
        "threaded callee's trailing param is __world"
    );
    let mut sargs = Vec::with_capacity(args.len() - 1);
    for a in &args[..args.len() - 1] {
        sargs.push(subst_rendered(a, &st.subst, "callee argument")?);
    }
    Ok(FrameProofNode::Callee {
        function,
        type_args: type_args.to_vec(),
        args: sargs,
    })
}

/// Build a SetDf/EraseDf leaf. Only uid/key are rendered.
fn df_op_step(
    ctx: &WalkCtx,
    function: FunctionID,
    type_args: &[Type],
    args: &[IRNode],
    st: &WalkState,
) -> Result<FrameProofNode, WalkErr> {
    assert!(
        type_args.len() == 2,
        "world df op carries K and V type args"
    );
    let uid = subst_rendered(&args[1], &st.subst, "parent uid")?;
    let key = subst_rendered(&args[2], &st.subst, "key")?;
    Ok(if function == ctx.world.set_df {
        FrameProofNode::SetDf {
            key_ty: type_args[0].clone(),
            val_ty: type_args[1].clone(),
            uid,
            key,
        }
    } else {
        FrameProofNode::EraseDf {
            key_ty: type_args[0].clone(),
            val_ty: type_args[1].clone(),
            uid,
            key,
        }
    })
}

/// Walk one tail subtree: consumes the `Let` spine (mutating a cloned state)
/// and returns a proof of `FrameDf <entry world> <subtree world> S`.
fn tail_proof(
    ctx: &WalkCtx,
    node: &IRNode,
    mut st: WalkState,
    proj_snd: bool,
) -> Result<FrameProofNode, WalkErr> {
    let mut acc: Option<FrameProofNode> = None;
    let mut cur = node;
    loop {
        match cur {
            IRNode::Let {
                pattern,
                value,
                body,
            } => {
                step_let(ctx, pattern, value, &mut st, &mut acc)?;
                cur = body;
            }
            IRNode::If {
                cond: _,
                then_branch,
                else_branch,
            } => {
                let t = tail_proof(ctx, then_branch, st.clone(), proj_snd)?;
                let e = tail_proof(ctx, else_branch, st.clone(), proj_snd)?;
                let branch = if proj_snd {
                    FrameProofNode::ItePair(Box::new(t), Box::new(e))
                } else {
                    FrameProofNode::BiteWorld(Box::new(t), Box::new(e))
                };
                return Ok(finish(chain(acc, branch)));
            }
            IRNode::Tuple(elems) if proj_snd => {
                let Some(last) = elems.last() else {
                    return Err(WalkErr::Drop("empty tuple tail".to_string()));
                };
                if !matches!(last, IRNode::Var(v) if *v == world_var()) {
                    return Err(WalkErr::Drop(
                        "tail world component is not the threaded __world variable".to_string(),
                    ));
                }
                return Ok(finish(acc));
            }
            IRNode::Var(v) if !proj_snd && *v == world_var() => {
                return Ok(finish(acc));
            }
            IRNode::Call {
                function,
                type_args,
                args,
            } => {
                // Tail call: a world native (identity faces) or a threaded
                // callee whose return shape matches the caller's.
                if let Some(op) = df_preserve_op(ctx, *function) {
                    if proj_snd {
                        return Err(WalkErr::Drop(
                            "world-native tail under a pair projection".to_string(),
                        ));
                    }
                    let step = FrameProofNode::DfPreserve {
                        op,
                        obj_ty: type_args
                            .first()
                            .cloned()
                            .expect("world native carries its object type arg"),
                    };
                    return Ok(finish(chain(acc, step)));
                }
                if *function == ctx.world.set_df || *function == ctx.world.erase_df {
                    if proj_snd {
                        return Err(WalkErr::Drop(
                            "df-op tail under a pair projection".to_string(),
                        ));
                    }
                    let step = df_op_step(ctx, *function, type_args, args, &st)?;
                    return Ok(finish(chain(acc, step)));
                }
                if is_threaded_value_callee(ctx, *function) {
                    let callee_snd = world_proj(
                        &ctx.program.functions.get(function).signature.return_type,
                        ctx.world_ty,
                    )
                    .expect("threaded callee shape");
                    if callee_snd != proj_snd {
                        return Err(WalkErr::Drop(
                            "tail-call projection shape mismatch".to_string(),
                        ));
                    }
                    let step = callee_step(ctx, *function, type_args, args, &st)?;
                    return Ok(finish(chain(acc, step)));
                }
                return Err(WalkErr::Drop(format!(
                    "unsupported tail call to `{}`",
                    ctx.program.functions.get(function).name
                )));
            }
            other => {
                return Err(WalkErr::Drop(format!(
                    "unsupported tail shape ({})",
                    ir_kind(other)
                )));
            }
        }
    }
}

fn ir_kind(node: &IRNode) -> &'static str {
    match node {
        IRNode::Match { .. } => "enum match",
        IRNode::MatchOption { .. } => "option match",
        IRNode::Var(_) => "variable",
        IRNode::Tuple(_) => "tuple",
        _ => "expression",
    }
}

fn step_let(
    ctx: &WalkCtx,
    pattern: &[TempId],
    value: &IRNode,
    st: &mut WalkState,
    acc: &mut Option<FrameProofNode>,
) -> Result<(), WalkErr> {
    let wv = world_var();
    // World rebind: `let __world := <world op>`.
    if pattern.len() == 1 && pattern[0] == wv {
        if let IRNode::Call {
            function,
            type_args,
            args,
        } = value
        {
            if *function == ctx.world.set_df || *function == ctx.world.erase_df {
                let step = df_op_step(ctx, *function, type_args, args, st)?;
                *acc = chain(acc.take(), step);
                // The world value is never rendered again: poison so any
                // later rendered expression reading the OLD `__world` drops.
                st.subst.insert(wv, None);
                return Ok(());
            }
            if let Some(op) = df_preserve_op(ctx, *function) {
                let step = FrameProofNode::DfPreserve {
                    op,
                    obj_ty: type_args
                        .first()
                        .cloned()
                        .expect("world native carries its object type arg"),
                };
                *acc = chain(acc.take(), step);
                st.subst.insert(wv, None);
                return Ok(());
            }
            if is_threaded_value_callee(ctx, *function) {
                // Unit-return callee: `let __world := callee … __world`.
                let step = callee_step(ctx, *function, type_args, args, st)?;
                *acc = chain(acc.take(), step);
                st.subst.insert(wv, None);
                return Ok(());
            }
        }
        return Err(WalkErr::Drop(
            "world rebound to a non-store-op value".to_string(),
        ));
    }

    // Pair destructure carrying the world: `let (x, __world) := callee …`
    // or the world-phi shape `let (x, __world) := if c then (…, w') else …`.
    if pattern.len() > 1 && pattern.last() == Some(&wv) {
        if let IRNode::If {
            cond: _,
            then_branch,
            else_branch,
        } = value
        {
            if pattern.len() != 2 {
                return Err(WalkErr::Drop("world phi over a non-pair tuple".to_string()));
            }
            let branch_st = WalkState {
                subst: st.subst.clone(),
            };
            let t = tail_proof(ctx, then_branch, branch_st.clone(), true)?;
            let e = tail_proof(ctx, else_branch, branch_st, true)?;
            let step = FrameProofNode::ItePair(Box::new(t), Box::new(e));
            *acc = chain(acc.take(), step);
            let subbed = bundle_subst(value, &st.subst).filter(|e| approx_size(e) <= SUBST_MAX);
            for p in pattern {
                if *p == wv {
                    st.subst.insert(p.clone(), None);
                    continue;
                }
                let entry = subbed.as_ref().map(|ve| IRNode::Let {
                    pattern: pattern.to_vec(),
                    value: Box::new(ve.clone()),
                    body: Box::new(IRNode::Var(p.clone())),
                });
                st.subst.insert(p.clone(), entry);
            }
            return Ok(());
        }
        let IRNode::Call {
            function,
            type_args,
            args,
        } = value
        else {
            return Err(WalkErr::Drop(
                "world destructured from a non-call value".to_string(),
            ));
        };
        if !is_threaded_value_callee(ctx, *function) {
            return Err(WalkErr::Drop(format!(
                "world destructured from unsupported callee `{}`",
                ctx.program.functions.get(function).name
            )));
        }
        let step = callee_step(ctx, *function, type_args, args, st)?;
        *acc = chain(acc.take(), step);
        // Non-world components become let-projections of the substituted
        // call (the definitional form the bundle machinery uses); the world
        // itself is poisoned — leaves never render it.
        let subbed = bundle_subst(value, &st.subst).filter(|e| approx_size(e) <= SUBST_MAX);
        for p in pattern {
            if *p == wv {
                st.subst.insert(p.clone(), None);
                continue;
            }
            let entry = subbed.as_ref().map(|ve| IRNode::Let {
                pattern: pattern.to_vec(),
                value: Box::new(ve.clone()),
                body: Box::new(IRNode::Var(p.clone())),
            });
            st.subst.insert(p.clone(), entry);
        }
        return Ok(());
    }

    // Ordinary bindings: no world effects allowed inside.
    if touches_world(ctx, value) {
        return Err(WalkErr::Drop(
            "state operation at an unsupported binding position".to_string(),
        ));
    }
    if pattern.is_empty() {
        // Sequencing let. A `WriteBack` here renders as a rebind of its
        // parent temp; the substitution keeps the parent's PRE-writeback
        // value. That is defeq-correct for the uid-accessor writebacks that
        // reach rendered positions (structure-eta identities), and any
        // genuinely-mutating case makes the generated theorem fail to
        // elaborate (a loud corpus build error, never a silent wrong lemma).
        return Ok(());
    }
    if pattern.len() == 1 {
        let sub = bundle_subst(value, &st.subst).filter(|e| approx_size(e) <= SUBST_MAX);
        st.subst.insert(pattern[0].clone(), sub);
        return Ok(());
    }
    match bundle_subst(value, &st.subst).filter(|e| approx_size(e) <= SUBST_MAX) {
        Some(ve) => {
            for p in pattern {
                st.subst.insert(
                    p.clone(),
                    Some(IRNode::Let {
                        pattern: pattern.to_vec(),
                        value: Box::new(ve.clone()),
                        body: Box::new(IRNode::Var(p.clone())),
                    }),
                );
            }
        }
        None => {
            for p in pattern {
                st.subst.insert(p.clone(), None);
            }
        }
    }
    Ok(())
}
