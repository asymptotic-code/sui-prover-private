// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Decomposition of oversized `.aborts` bodies into named segment functions.
//!
//! Very large `.aborts` companions (e.g. `advance_epoch.aborts`, ~1000 rendered
//! lines) are a proof wall: any whole-body `simp`/`rw` forces the kernel to
//! traverse the entire term (see CLAUDE.md "Kernel deep-recursion"). This pass
//! rewrites such a body into a chain of segment functions
//!
//!   `<fn>.aborts.seg_1` … `<fn>.aborts.seg_k`
//!
//! cutting along the abort-check spine (top-level `let`s and
//! `MoveAbort.orElse`-shaped checks) and recursing into oversized `orElse`
//! scrutinees and `if` branches, so each segment stays near a target size. The
//! parent `.aborts` becomes a thin call to its top segment (statement-level
//! consumers are unchanged), and the renderer emits a recomposition lemma
//!
//!   `theorem <fn>.aborts.decompose … : <fn>.aborts … = <fn>.aborts.seg_k … := rfl`
//!
//! (pairs recorded in [`Program::aborts_decompositions`]). Proofs rewrite with
//! the lemma and then discharge one small segment at a time — the flat,
//! named-goal ladder that was previously hand-built per function.
//!
//! Conservative by construction: only non-recursive, monomorphic `.aborts`
//! functions with plain value parameters are touched; a subtree is only
//! extracted when every free variable it needs can be typed at the cut, and an
//! `if` branch containing an `IRNode::Abort` proof placeholder is never
//! separated from its guard (the renderer's dependent-if machinery needs them
//! in one function). Runs after `materialize_proof_params` so segment
//! signatures (including copied `hpre` proof params) are final.

use crate::data::functions::{Function, FunctionSignature, Parameter, ProofParam, ProofParamType};
use crate::data::types::{TempId, Type};
use crate::{FunctionID, IRNode, Program};
use std::collections::{BTreeMap, BTreeSet};

/// Only decompose bodies whose approximate size exceeds this. Under the
/// per-package `contract_aborts` gate (unified-backend design §5.1/§10 Phase
/// 2.3) bundles become the default obligation form: smaller bodies are also
/// bundled when the walk yields either ≥ 2 leaves or ZERO leaves (a total
/// function — its `aborts_none_of` is hypothesis-free and rendered
/// `@[contract]`, auto-registering the callee contract).
const MIN_TOTAL: usize = 25_000;
/// Target approximate size per segment; also the threshold for recursing into
/// a check's scrutinee or an `if` branch.
const CHUNK: usize = 12_000;
/// Never cut if the remaining tail would be smaller than this.
const MIN_TAIL: usize = 6_000;
/// Cap on any single stored substitution / inlined-arithmetic form. Oversized
/// values are treated as opaque instead of being copied into every downstream
/// statement (which is multiplicative and can exhaust memory).
const SUBST_MAX: usize = 6_000;

/// Cap on a stored substitution whose temp is referenced MORE THAN ONCE
/// downstream. `SUBST_MAX` bounds one copy, but a modestly-sized value inlined
/// at many use sites still blows up multiplicatively — e.g. a test-scenario
/// `let runner := Test_runner.build (validators ...)` (~30 nodes) referenced by
/// every assertion, which inlined ~6000× into one sui-system test `.aborts`
/// (50k+ rendered lines, elaboration timeout). Above this size a multi-use temp
/// is poisoned into a shared segment param instead of inlined. Small multi-use
/// values (booleans, short arithmetic) stay inlined for the conv-localized
/// abort proof.
const MULTI_USE_SUBST_MAX: usize = 16;

/// One step of an abort spine. Cuts happen between steps.
enum Step {
    /// `let pattern := value; <rest>`
    Bind { pattern: Vec<TempId>, value: IRNode },
    /// `MoveAbort.orElse`-shaped check: `match scrutinee with | some binding =>
    /// some_branch | none => <rest>`
    Check {
        scrutinee: IRNode,
        binding: TempId,
        some_branch: IRNode,
    },
}

type Env = BTreeMap<TempId, Option<Type>>;

struct SegCtx {
    parent_name: String,
    module_id: crate::ModuleID,
    return_type: Type,
    proof_params: Vec<ProofParam>,
    proof_param_names: BTreeSet<TempId>,
    /// Per proof param: the parent value params its verbatim type mentions
    /// (those must be in scope wherever the proof param is copied).
    parent_param_mentions: Vec<(TempId, Vec<TempId>)>,
    counter: usize,
    created: Vec<FunctionID>,
    atom_counter: usize,
    /// Dedup of hoisted arithmetic atoms by structural (Debug) form — the
    /// duplicated `if`/`else` branches in generated bodies would otherwise
    /// hoist every tower twice.
    atom_cache: BTreeMap<String, FunctionID>,
    /// Opaque-subtree replacements recorded by the bundle walk: the parent
    /// body must CALL each opaque segment (single rendering) — `WriteBack`
    /// nodes render registry-type-sensitively, so a duplicated subtree can
    /// render differently in parent and segment, breaking the bundle proof's
    /// defeq. Keyed by the original subtree's Debug form; applied
    /// outermost-first.
    replacements: Vec<(String, IRNode)>,
}

/// The per-package `contract_aborts` gate: any scanned
/// `def <Module>.module_options` hook that lists `"contract_aborts"`.
/// Mode-independent (works with or without `world_mode`).
pub fn contract_aborts_enabled(program: &Program) -> bool {
    program
        .lean_termination_decls
        .module_options
        .values()
        .any(|opts| opts.contains("contract_aborts"))
}

/// The per-package `requires_leaves` gate (unified-backend design §5.2,
/// deferred item 2.2): a requires-slot `Abort` placeholder at a callee call
/// inside a bundled `.aborts` becomes a named precondition leaf
/// (`RequiresHolds`) feeding a ∀-bound callee-aborts leaf
/// (`CalleeNoneUnderRequires`) instead of escalating to an opaque segment
/// around the `sorry`-slotted call.
pub fn requires_leaves_enabled(program: &Program) -> bool {
    program
        .lean_termination_decls
        .module_options
        .values()
        .any(|opts| opts.contains("requires_leaves"))
}

pub fn decompose_aborts(program: &mut Program) {
    let debug = std::env::var("FOXY_DECOMPOSE_DEBUG").is_ok();
    let bundles_default = contract_aborts_enabled(program);
    // Worklist: initial `.aborts` candidates plus, recursively, any opaque
    // segments they spawn — re-bundling a segment dissolves it into finer
    // obligations of its own (`<seg>_none_of`), so escalation costs
    // granularity only until the next round. A processed-set plus a hard cap
    // bound the recursion; `decompose_one` refuses no-progress bundles.
    let mut queue: Vec<FunctionID> = program
        .functions
        .iter_ids()
        .filter(|id| program.functions.get(id).name.ends_with(".aborts"))
        .collect();
    let mut processed: BTreeSet<FunctionID> = BTreeSet::new();
    let mut steps = 0usize;
    while let Some(id) = queue.pop() {
        if !processed.insert(id) {
            continue;
        }
        steps += 1;
        if steps > 500 {
            break;
        }
        let f = program.functions.get(&id);
        if f.is_native
            || f.theorem.is_some()
            || f.mutual_group_id.is_some()
            || !f.signature.type_params.is_empty()
        {
            continue;
        }
        if f.body.calls().any(|c| c == id) {
            continue;
        }
        if f.signature.parameters.iter().any(|p| {
            matches!(
                p.param_type,
                Type::MutableReference(_, _) | Type::Reference(_)
            )
        }) {
            continue;
        }
        // Segment signatures re-apply proof-param types verbatim; a
        // LoopInvHook re-applies to the (different) segment param list, so
        // skip those. Fixed-text hypotheses ride into bundles: `Verbatim`,
        // and the world-mode `DataInvWorld` (its text mentions only value
        // params, copied alongside via `parent_param_mentions`). `DataInv`
        // (TypedMap) stays skipped to keep slot-mode output byte-identical.
        if f.signature.proof_params.iter().any(|pp| {
            !matches!(
                pp.param_type,
                ProofParamType::Verbatim(_) | ProofParamType::DataInvWorld { .. }
            )
        }) {
            continue;
        }
        // A literal-`none` `.aborts` needs no contract: callers' bundle walks
        // already collapse checks against it to `Rfl` inline (`bundle_expr`'s
        // `Call` arm), so a generated `@[contract]` rfl-theorem would be noise.
        if matches!(f.body, IRNode::OptionNone) {
            continue;
        }
        let sz = approx_size(&f.body);
        if debug && sz > 20_000 {
            eprintln!("[decompose] candidate {} size={}", f.name, sz);
        }
        let small = sz < MIN_TOTAL;
        if small && !bundles_default {
            continue;
        }
        queue.extend(decompose_one(program, id, debug, small));
    }
}

fn decompose_one(
    program: &mut Program,
    id: FunctionID,
    debug: bool,
    small: bool,
) -> Vec<FunctionID> {
    let parent = program.functions.get(&id).clone();

    let env: Env = parent
        .signature
        .parameters
        .iter()
        .map(|p| (p.ssa_value.clone(), Some(p.param_type.clone())))
        .collect();
    let order: Vec<TempId> = parent
        .signature
        .parameters
        .iter()
        .map(|p| p.ssa_value.clone())
        .collect();
    let parent_param_mentions = parent
        .signature
        .proof_params
        .iter()
        .map(|pp| {
            let mentions = match &pp.param_type {
                ProofParamType::Verbatim(text) => parent
                    .signature
                    .parameters
                    .iter()
                    .filter(|p| mentions_ident(text, &p.ssa_value))
                    .map(|p| p.ssa_value.clone())
                    .collect(),
                ProofParamType::DataInvWorld { parent_expr, .. } => parent
                    .signature
                    .parameters
                    .iter()
                    .filter(|p| {
                        mentions_ident(parent_expr, &p.ssa_value)
                            || p.name == super::world_threading::WORLD_VAR
                    })
                    .map(|p| p.ssa_value.clone())
                    .collect(),
                _ => Vec::new(),
            };
            (TempId::from(pp.name.as_str()), mentions)
        })
        .collect();

    let mut ctx = SegCtx {
        parent_name: parent.name.clone(),
        module_id: parent.module_id,
        return_type: parent.signature.return_type.clone(),
        proof_params: parent.signature.proof_params.clone(),
        proof_param_names: parent
            .signature
            .proof_params
            .iter()
            .map(|pp| TempId::from(pp.name.as_str()))
            .collect(),
        parent_param_mentions,
        counter: 0,
        created: Vec::new(),
        atom_counter: 0,
        atom_cache: BTreeMap::new(),
        replacements: Vec::new(),
    };

    // Hoist heavy arithmetic let-chains into named atom definitions first, so
    // segment bodies (and downstream proofs) reference one-line
    // `<fn>.atom_k a b c` patterns instead of materialized convert towers —
    // the mechanical form of the "prove leaves over abstract vars" discipline.
    let body = hoist_atoms(program, &mut ctx, parent.body.clone(), &env, &order);

    // Verification-condition bundle: try the fine-grained obligation walk
    // first. On success the body stays whole (post-hoist), the bundle is
    // recorded for the renderer (`<fn>.aborts.ob_k` defs + the
    // `<fn>.aborts_none_of` theorem with its structural proof), and proofs
    // never unfold the body at all. Falls back to segmentation when the walk
    // hits something it cannot express over parent params.
    {
        let parent_params: BTreeMap<TempId, Type> = parent
            .signature
            .parameters
            .iter()
            .map(|p| (p.ssa_value.clone(), p.param_type.clone()))
            .collect();
        let mut acc = BundleAcc::default();
        let subst: BundleSubst = BTreeMap::new();
        if let Some(proof) = bundle_spine(
            program,
            &mut ctx,
            &mut acc,
            &parent_params,
            &order,
            &body,
            &env,
            &order,
            &subst,
            &[],
        ) {
            // Prune obligations orphaned by tail escalation and renumber.
            let mut used: BTreeSet<usize> = BTreeSet::new();
            collect_used_obs(&proof, &mut used);
            let remap: BTreeMap<usize, usize> = used
                .iter()
                .enumerate()
                .map(|(new, old)| (*old, new))
                .collect();
            let obligations: Vec<AbortsObligation> = acc
                .obligations
                .into_iter()
                .enumerate()
                .filter(|(i, _)| used.contains(i))
                .map(|(i, mut ob)| {
                    ob.name = format!("ob_{}", remap[&i] + 1);
                    ob
                })
                .collect();
            let proof = remap_obs(proof, &remap);

            // No-progress guard: a bundle consisting of exactly one opaque
            // leaf over a fresh segment is the whole body wrapped in a name —
            // recursing on it would never terminate. Keep the parent as-is
            // (the created segment stays as dead code) and let the plain
            // segmentation path handle this function instead.
            let no_progress = obligations.len() == 1
                && matches!(proof, AbortsProofNode::Leaf { .. })
                && matches!(&obligations[0].leaf,
                    crate::data::AbortsLeaf::OptionNone(IRNode::Call { function, .. })
                        if ctx.created.contains(function));
            // Default-on bundles (`contract_aborts`, §10 Phase 2.3) accept a
            // small body only with ≥ 2 leaves — or ZERO leaves, the total-
            // callee case whose hypothesis-free `aborts_none_of` is rendered
            // `@[contract]` (the auto-registered contract). A 1-leaf bundle on
            // a small body is pure indirection; skip it (any segment created
            // during the walk stays as dead code, same as the no-progress
            // path).
            let small_skip = small && obligations.len() == 1;
            if no_progress || small_skip {
                if debug {
                    eprintln!(
                        "[decompose] {} bundle {} -> {}",
                        parent.name,
                        if no_progress {
                            "no-progress"
                        } else {
                            "1-leaf small"
                        },
                        if small { "skip" } else { "segmentation" }
                    );
                }
            } else {
                // Swap each opaque subtree in the parent for its segment call,
                // outermost-first (map_top_down), so exactly one rendering of the
                // subtree exists.
                let replacements = std::mem::take(&mut ctx.replacements);
                let body = body.map_top_down(&mut |n| {
                    let key = format!("{:?}", n);
                    for (k, call) in &replacements {
                        if *k == key {
                            return call.clone();
                        }
                    }
                    n
                });

                program.functions.get_mut(id).body = body;
                if program.callee_requires_precond_callers.contains(&id) {
                    for seg in &ctx.created {
                        program.callee_requires_precond_callers.insert(*seg);
                    }
                }
                if debug {
                    eprintln!(
                        "[decompose] {} -> bundle: {} obligations, {} opaque segments, {} atoms",
                        parent.name,
                        obligations.len(),
                        ctx.created.len(),
                        ctx.atom_counter
                    );
                }
                program.aborts_bundles.push(AbortsBundle {
                    fn_id: id,
                    obligations,
                    proof,
                });
                return ctx.created;
            }
        }
        // Small bodies exist as candidates only under `contract_aborts`
        // (bundles-by-default); segmentation is an anti-goal for them — the
        // body already fits in one proof-sized piece.
        if small {
            return Vec::new();
        }
        if debug {
            eprintln!("[decompose] {} bundle bail -> segmentation", parent.name);
        }
        // Segments are already chunk-sized: when their own bundle makes no
        // progress there is nothing to gain from re-segmenting them (doing so
        // recurses forever on a sliver-smaller tail).
        if parent.name.contains(".seg_") {
            return Vec::new();
        }
    }

    let Some(top) = segment_spine(program, &mut ctx, body, &env, &order) else {
        if debug {
            eprintln!("[decompose] {} bail: untypeable free variable", parent.name);
        }
        return Vec::new();
    };

    program.functions.get_mut(id).body = seg_call(program, top);
    if program.callee_requires_precond_callers.contains(&id) {
        for seg in &ctx.created {
            program.callee_requires_precond_callers.insert(*seg);
        }
    }
    if debug {
        eprintln!(
            "[decompose] {} -> {} segments, {} atoms",
            parent.name,
            ctx.created.len(),
            ctx.atom_counter
        );
    }
    program.aborts_decompositions.push((id, top));
    // Segmentation-path children are not re-queued (see above).
    Vec::new()
}

/// Only name an inlined arithmetic chain when it exceeds this approximate size
/// (single `convert`s and one-op expressions stay inline).
const ATOM_MIN: usize = 250;

/// Walk the body (iteratively along spines, recursively across nesting) and
/// replace each heavy arithmetic `let` value with a call to a named
/// `<fn>.atom_k` definition whose body is the value with its arithmetic
/// let-chain fully inlined. Semantics-preserving (the atom is `@[reducible]`
/// and delta+beta-reduces to the original); guards downstream then test small
/// named applications instead of towers.
fn hoist_atoms(
    program: &mut Program,
    ctx: &mut SegCtx,
    node: IRNode,
    env0: &Env,
    order0: &[TempId],
) -> IRNode {
    let (steps, terminal) = collect_spine(node);
    let mut env = env0.clone();
    let mut order = order0.to_vec();
    let mut arith: BTreeMap<TempId, IRNode> = BTreeMap::new();
    let mut new_steps = Vec::with_capacity(steps.len());
    for step in steps {
        match step {
            Step::Bind { pattern, value } => {
                let mut value = value;
                if pattern.len() == 1 && is_atomizable(&value) {
                    let inlined = subst_exprs(value.clone(), &arith);
                    if approx_size(&inlined) >= ATOM_MIN {
                        // An `If`-phi value keeps its guard (and the original,
                        // in-scope cond expression) at the use site — hiding the
                        // guard inside an atom makes the ite invisible to
                        // `split`/`reduceIte` in downstream proofs. Only the
                        // branches are hoisted (each when big enough alone).
                        if let IRNode::If {
                            cond,
                            then_branch,
                            else_branch,
                        } = value
                        {
                            let mut hoist_branch = |branch: Box<IRNode>| -> Box<IRNode> {
                                let inlined_branch = subst_exprs((*branch).clone(), &arith);
                                if approx_size(&inlined_branch) >= ATOM_MIN {
                                    if let Some(call) =
                                        make_atom(program, ctx, &inlined_branch, &env, &order)
                                    {
                                        return Box::new(call);
                                    }
                                }
                                branch
                            };
                            value = IRNode::If {
                                cond,
                                then_branch: hoist_branch(then_branch),
                                else_branch: hoist_branch(else_branch),
                            };
                        } else if let Some(call) = make_atom(program, ctx, &inlined, &env, &order) {
                            value = call;
                        }
                    }
                    if approx_size(&inlined) <= 4 * SUBST_MAX {
                        arith.insert(pattern[0].clone(), inlined);
                    }
                }
                let vt = try_type(&value, &env, program);
                register_pattern(&mut env, &mut order, &pattern, vt);
                new_steps.push(Step::Bind { pattern, value });
            }
            Step::Check {
                scrutinee,
                binding,
                some_branch,
            } => {
                let scrutinee = match scrutinee {
                    s @ (IRNode::Let { .. } | IRNode::MatchOption { .. } | IRNode::If { .. }) => {
                        hoist_atoms(program, ctx, s, &env, &order)
                    }
                    s => s,
                };
                new_steps.push(Step::Check {
                    scrutinee,
                    binding,
                    some_branch,
                });
            }
        }
    }
    let terminal = match terminal {
        IRNode::If {
            cond,
            then_branch,
            else_branch,
        } => IRNode::If {
            cond,
            then_branch: Box::new(hoist_atoms(program, ctx, *then_branch, &env, &order)),
            else_branch: Box::new(hoist_atoms(program, ctx, *else_branch, &env, &order)),
        },
        other => other,
    };
    rebuild(new_steps, terminal)
}

/// Values worth naming: any pure value expression (arithmetic chains,
/// branch-phi `if`s, packed/updated structs, call results with big chained
/// args) — every one of them inflates multiplicatively under
/// substitution/zeta. Subtrees carrying proof placeholders or mutable
/// writeback machinery stay put (their rendering is position-sensitive).
fn is_atomizable(node: &IRNode) -> bool {
    if is_arith(node) {
        return true;
    }
    matches!(node, IRNode::If { .. })
        && !node.iter().any(|n| {
            matches!(
                n,
                IRNode::Abort { .. } | IRNode::WriteBack { .. } | IRNode::MutableCompose { .. }
            )
        })
}

fn is_arith(node: &IRNode) -> bool {
    use crate::data::ir::{BinOp, UnOp};
    match node {
        IRNode::BinOp { op, .. } => matches!(
            op,
            BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Mod
        ),
        IRNode::UnOp { op, .. } => matches!(op, UnOp::Cast(_)),
        _ => false,
    }
}

fn subst_exprs(node: IRNode, map: &BTreeMap<TempId, IRNode>) -> IRNode {
    node.map(&mut |n| match n {
        IRNode::Var(name) => match map.get(&name) {
            Some(e) => e.clone(),
            None => IRNode::Var(name),
        },
        other => other,
    })
}

fn make_atom(
    program: &mut Program,
    ctx: &mut SegCtx,
    inlined: &IRNode,
    env: &Env,
    order: &[TempId],
) -> Option<IRNode> {
    let free = inlined.free_vars();
    let mut parameters: Vec<Parameter> = Vec::new();
    for name in order {
        if !free.contains(name) {
            continue;
        }
        match env.get(name) {
            Some(Some(ty)) => parameters.push(Parameter {
                name: name.to_string(),
                param_type: ty.clone(),
                ssa_value: name.clone(),
            }),
            _ => return None,
        }
    }
    for v in &free {
        if !parameters.iter().any(|p| &p.ssa_value == v) {
            return None;
        }
    }
    let ret = try_type(inlined, env, program)?;

    let key = format!(
        "{:?}|{:?}",
        inlined,
        parameters.iter().map(|p| &p.ssa_value).collect::<Vec<_>>()
    );
    let fid = match ctx.atom_cache.get(&key) {
        Some(fid) => *fid,
        None => {
            ctx.atom_counter += 1;
            let fid = program.functions.add(Function {
                module_id: ctx.module_id,
                name: format!("{}.atom_{}", ctx.parent_name, ctx.atom_counter),
                signature: FunctionSignature {
                    type_params: Vec::new(),
                    parameters: parameters.clone(),
                    proof_params: Vec::new(),
                    return_type: ret,
                },
                body: inlined.clone(),
                theorem: None,
                is_native: false,
                mutual_group_id: None,
                test_expectation: None,
                is_uninterpreted: false,
            });
            ctx.atom_cache.insert(key, fid);
            fid
        }
    };
    Some(IRNode::Call {
        function: fid,
        type_args: Vec::new(),
        args: parameters
            .iter()
            .map(|p| IRNode::Var(p.ssa_value.clone()))
            .collect(),
    })
}

/// Segment an `Option MoveAbort`-typed spine into one or more chained segment
/// functions; returns the top segment's id (its application to its own
/// parameters is definitionally the input node). Returns `None` — creating
/// nothing — when a free variable of the node cannot be typed here.
fn segment_spine(
    program: &mut Program,
    ctx: &mut SegCtx,
    node: IRNode,
    env0: &Env,
    order0: &[TempId],
) -> Option<FunctionID> {
    // Precheck: every free var of the whole node must be typeable here (or be
    // a proof param). Guarantees the top segment's creation below cannot fail,
    // so no orphan functions are ever left behind.
    for v in node.free_vars() {
        if ctx.proof_param_names.contains(&v) {
            continue;
        }
        match env0.get(&v) {
            Some(Some(_)) => {}
            _ => return None,
        }
    }

    let (mut steps, mut terminal) = collect_spine(node);
    if std::env::var("FOXY_DECOMPOSE_DEBUG").is_ok() {
        let checks: Vec<usize> = steps
            .iter()
            .filter_map(|s| match s {
                Step::Check { scrutinee, .. } => Some(approx_size(scrutinee)),
                _ => None,
            })
            .collect();
        eprintln!(
            "[decompose]   spine {}: {} steps, terminal={} ({}), check sizes {:?}",
            ctx.parent_name,
            steps.len(),
            approx_size(&terminal),
            match &terminal {
                IRNode::If { .. } => "If",
                IRNode::Call { .. } => "Call",
                _ => "other",
            },
            checks
        );
    }

    // Environment (and binding order) before each step and after the last.
    let mut env = env0.clone();
    let mut order: Vec<TempId> = order0.to_vec();
    let mut env_at: Vec<(Env, Vec<TempId>)> = Vec::with_capacity(steps.len() + 1);
    for step in &steps {
        env_at.push((env.clone(), order.clone()));
        if let Step::Bind { pattern, value } = step {
            let vt = try_type(value, &env, program);
            register_pattern(&mut env, &mut order, pattern, vt);
        }
    }
    env_at.push((env, order));

    // Recurse into oversized check scrutinees (they are themselves
    // `Option MoveAbort` spines).
    for (i, step) in steps.iter_mut().enumerate() {
        if let Step::Check { scrutinee, .. } = step {
            if approx_size(scrutinee) > CHUNK {
                let (e, o) = &env_at[i];
                if let Some(sub) = segment_spine(program, ctx, scrutinee.clone(), e, o) {
                    *scrutinee = seg_call(program, sub);
                }
            }
        }
    }

    // Recurse into oversized branches of a terminal `if` (also
    // `Option MoveAbort`-typed in these spine positions). A branch is movable
    // only when every `IRNode::Abort` proof placeholder inside it sits under a
    // deeper `if` within the branch — the renderer's dependent-if machinery
    // pairs a placeholder with its innermost guard, and that pair must stay in
    // one function.
    if let IRNode::If {
        cond,
        then_branch,
        else_branch,
    } = terminal
    {
        let (e, o) = env_at.last().unwrap().clone();
        let mut extract = |branch: Box<IRNode>| -> Box<IRNode> {
            if approx_size(&branch) > CHUNK && !abort_exposed(&branch) {
                if let Some(sub) = segment_spine(program, ctx, (*branch).clone(), &e, &o) {
                    return Box::new(seg_call(program, sub));
                }
            }
            branch
        };
        let then_branch = extract(then_branch);
        let else_branch = extract(else_branch);
        terminal = IRNode::If {
            cond,
            then_branch,
            else_branch,
        };
    }

    // Greedy cuts along the spine.
    let step_sizes: Vec<usize> = steps.iter().map(step_size).collect();
    let mut remaining: usize = step_sizes.iter().sum::<usize>() + approx_size(&terminal);
    let mut cuts: Vec<usize> = Vec::new();
    let mut acc = 0usize;
    for (i, sz) in step_sizes.iter().enumerate() {
        acc += sz;
        remaining -= sz;
        if acc >= CHUNK && remaining >= MIN_TAIL {
            cuts.push(i + 1);
            acc = 0;
        }
    }

    let mut boundaries = vec![0usize];
    boundaries.extend(cuts.iter().copied());
    boundaries.push(steps.len());
    let seg_count = boundaries.len() - 1;

    let mut chunks: Vec<Vec<Step>> = Vec::with_capacity(seg_count);
    let mut rest = steps;
    for w in boundaries.windows(2).rev() {
        chunks.push(rest.split_off(w[0]));
    }
    chunks.reverse();

    // Build back-to-front. A failed inner segment (untypeable cut variable)
    // merges into the segment above it instead of aborting; the outermost
    // segment cannot fail thanks to the precheck.
    let mut tail = terminal;
    let mut top: Option<FunctionID> = None;
    for j in (0..seg_count).rev() {
        let body = rebuild(std::mem::take(&mut chunks[j]), tail);
        if j == 0 {
            let fid = create_segment(program, ctx, &body, &env_at[0].0, &env_at[0].1)?;
            top = Some(fid);
            break;
        }
        match create_segment(
            program,
            ctx,
            &body,
            &env_at[boundaries[j]].0,
            &env_at[boundaries[j]].1,
        ) {
            Some(fid) => tail = seg_call(program, fid),
            // Untypeable cut: keep this chunk inline in the segment above.
            None => tail = body,
        }
    }
    top
}

fn create_segment(
    program: &mut Program,
    ctx: &mut SegCtx,
    body: &IRNode,
    env: &Env,
    order: &[TempId],
) -> Option<FunctionID> {
    let free = body.free_vars();

    let mut proof_params: Vec<ProofParam> = Vec::new();
    let mut forced: BTreeSet<TempId> = BTreeSet::new();
    for pp in &ctx.proof_params {
        if free.contains(pp.name.as_str()) {
            proof_params.push(pp.clone());
            if let Some((_, mentions)) = ctx
                .parent_param_mentions
                .iter()
                .find(|(n, _)| n.as_ref() == pp.name.as_str())
            {
                forced.extend(mentions.iter().cloned());
            }
        }
    }

    let mut parameters: Vec<Parameter> = Vec::new();
    for name in order {
        let needed =
            (free.contains(name) && !ctx.proof_param_names.contains(name)) || forced.contains(name);
        if !needed {
            continue;
        }
        match env.get(name) {
            Some(Some(ty)) => parameters.push(Parameter {
                name: name.to_string(),
                param_type: ty.clone(),
                ssa_value: name.clone(),
            }),
            _ => return None,
        }
    }
    for v in &free {
        if !parameters.iter().any(|p| &p.ssa_value == v) && !ctx.proof_param_names.contains(v) {
            return None;
        }
    }

    ctx.counter += 1;
    let fid = program.functions.add(Function {
        module_id: ctx.module_id,
        name: format!("{}.seg_{}", ctx.parent_name, ctx.counter),
        signature: FunctionSignature {
            type_params: Vec::new(),
            parameters,
            proof_params,
            return_type: ctx.return_type.clone(),
        },
        body: body.clone(),
        theorem: None,
        is_native: false,
        mutual_group_id: None,
        test_expectation: None,
        is_uninterpreted: false,
    });
    ctx.created.push(fid);
    Some(fid)
}

/// Build the application of a segment function to its own parameter names.
fn seg_call(program: &Program, fid: FunctionID) -> IRNode {
    let f = program.functions.get(&fid);
    IRNode::Call {
        function: fid,
        type_args: Vec::new(),
        args: f
            .signature
            .parameters
            .iter()
            .map(|p| IRNode::Var(p.ssa_value.clone()))
            .chain(
                f.signature
                    .proof_params
                    .iter()
                    .map(|pp| IRNode::Var(TempId::from(pp.name.as_str()))),
            )
            .collect(),
    }
}

/// An `IRNode::Abort` proof placeholder is "exposed" when it is reachable
/// without passing through an `if` — moving such a subtree would separate the
/// placeholder from the dependent-if guard that the renderer pairs it with.
/// Placeholders under an `if` inside the subtree move together with their
/// guard and are safe.
fn abort_exposed(node: &IRNode) -> bool {
    match node {
        IRNode::Abort { .. } => true,
        IRNode::If { cond, .. } => abort_exposed(cond),
        _ => node.iter_children().any(abort_exposed),
    }
}

/// Walk the top-level spine iteratively (bodies nest linearly and can be
/// thousands of nodes deep).
fn collect_spine(node: IRNode) -> (Vec<Step>, IRNode) {
    let mut steps = Vec::new();
    let mut cur = node;
    loop {
        match cur {
            IRNode::Let {
                pattern,
                value,
                body,
            } => {
                steps.push(Step::Bind {
                    pattern,
                    value: *value,
                });
                cur = *body;
            }
            IRNode::MatchOption {
                scrutinee,
                binding,
                some_branch,
                none_branch,
            } => {
                steps.push(Step::Check {
                    scrutinee: *scrutinee,
                    binding,
                    some_branch: *some_branch,
                });
                cur = *none_branch;
            }
            other => return (steps, other),
        }
    }
}

fn rebuild(steps: Vec<Step>, tail: IRNode) -> IRNode {
    steps.into_iter().rev().fold(tail, |acc, s| match s {
        Step::Bind { pattern, value } => IRNode::Let {
            pattern,
            value: Box::new(value),
            body: Box::new(acc),
        },
        Step::Check {
            scrutinee,
            binding,
            some_branch,
        } => IRNode::MatchOption {
            scrutinee: Box::new(scrutinee),
            binding,
            some_branch: Box::new(some_branch),
            none_branch: Box::new(acc),
        },
    })
}

fn step_size(s: &Step) -> usize {
    match s {
        Step::Bind { value, .. } => approx_size(value) + 8,
        Step::Check {
            scrutinee,
            some_branch,
            ..
        } => approx_size(scrutinee) + approx_size(some_branch) + 8,
    }
}

/// Cheap size proxy: length of the Debug representation. Only used to place
/// cut points, never for correctness.
pub(crate) fn approx_size(node: &IRNode) -> usize {
    format!("{:?}", node).len()
}

fn register_pattern(
    env: &mut Env,
    order: &mut Vec<TempId>,
    pattern: &[TempId],
    val_type: Option<Type>,
) {
    let mut push = |name: &TempId, ty: Option<Type>| {
        if !env.contains_key(name) {
            order.push(name.clone());
        }
        env.insert(name.clone(), ty);
    };
    if pattern.len() == 1 {
        push(&pattern[0], val_type);
    } else if let Some(Type::Tuple(elems)) = val_type {
        if elems.len() == pattern.len() {
            for (name, ty) in pattern.iter().zip(elems) {
                push(name, Some(ty));
            }
        } else {
            for name in pattern {
                push(name, None);
            }
        }
    } else {
        for name in pattern {
            push(name, None);
        }
    }
}

/// Fallible typing for the node shapes that actually appear as spine-`let`
/// values in `.aborts` bodies. Anything unhandled returns `None`, which only
/// restricts where cuts may happen.
/// `FunctionSignature::return_type` for a Mutable-returning "creator" function
/// (one whose body directly builds a `MutableBorrow`, e.g. `Test_runner::
/// scenario_mut`) is a stale PRE-threading placeholder: `mutable_threading`'s
/// `augmented_return` keeps whatever `MutableReference(inner, state)` the
/// translator originally guessed (typically `state == inner`, degenerate) and
/// only appends the plain inner types of the function's own erstwhile `&mut`
/// params — it never refreshes the Mutable half's `state` component from the
/// body. The renderer already knows this (`function_renderer.rs` skips
/// printing a MutableReference return-type annotation entirely and lets Lean
/// infer it from the body). `decompose_aborts` cannot rely on Lean inference,
/// so it recomputes the same answer on the Rust side: seed a registry from
/// the callee's own (post-threading, so never Mutable-typed) parameters and
/// evaluate the callee body's real type, exactly mirroring what Lean's
/// elaborator would derive. Nested calls inside that body still fall back to
/// their own callee's stored `return_type` (see `IRNode::get_type`'s `Call`
/// arm) — this only fixes the *direct* callee, which is what every call site
/// here needs.
fn concrete_callee_return_type(program: &Program, function: crate::FunctionID) -> Type {
    let callee = program.functions.get(&function);
    let declared = callee.signature.return_type.clone();
    if !declared.contains_mutable_ref() || callee.is_native {
        return declared;
    }
    let reg = callee.param_registry(program);
    callee.body.get_type(&reg)
}

fn try_type(node: &IRNode, env: &Env, program: &Program) -> Option<Type> {
    use crate::data::ir::{BinOp, Const, UnOp};
    match node {
        IRNode::Var(name) => env.get(name).cloned().flatten(),
        IRNode::Const(c) => Some(match c {
            Const::Bool(_) => Type::Bool,
            Const::UInt { bits, .. } => Type::UInt(*bits as u32),
            Const::Address(_) => Type::Address,
            Const::Vector { elem_type, .. } => Type::Vector(Box::new(elem_type.clone())),
        }),
        IRNode::BinOp { op, lhs, .. } => match op {
            BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge | BinOp::Eq | BinOp::Neq => {
                Some(Type::Bool)
            }
            BinOp::And | BinOp::Or => Some(Type::Bool),
            _ => try_type(lhs, env, program),
        },
        IRNode::UnOp { op, operand } => match op {
            UnOp::Cast(bits) => Some(Type::UInt(*bits)),
            UnOp::Not => Some(Type::Bool),
            UnOp::BitNot => try_type(operand, env, program),
        },
        IRNode::ArithOverflowCheck { .. } => Some(Type::Bool),
        IRNode::ToBool(_) => Some(Type::Bool),
        IRNode::ToProp(_) => Some(Type::Prop),
        IRNode::MoveAbortValue { .. } => Some(Type::MoveAbort),
        IRNode::OptionSome(inner) => Some(Type::Option(Box::new(try_type(inner, env, program)?))),
        IRNode::Call {
            function,
            type_args,
            ..
        } => {
            let ret = concrete_callee_return_type(program, *function);
            Some(if type_args.is_empty() {
                ret
            } else {
                ret.substitute_type_params(type_args)
            })
        }
        IRNode::Pack {
            struct_id,
            type_args,
            ..
        } => Some(Type::Struct {
            struct_id: *struct_id,
            type_args: type_args.clone(),
        }),
        IRNode::Field {
            struct_id,
            field_index,
            base,
        } => {
            let s = program.structs.get(*struct_id);
            let field_ty = s.fields.get(*field_index)?.field_type.clone();
            match try_type(base, env, program) {
                Some(Type::Struct { type_args, .. }) if !type_args.is_empty() => {
                    Some(field_ty.substitute_type_params(&type_args))
                }
                _ => {
                    if s.type_params.is_empty() {
                        Some(field_ty)
                    } else {
                        None
                    }
                }
            }
        }
        IRNode::UpdateField { base, .. } | IRNode::UpdateVec { base, .. } => {
            try_type(base, env, program)
        }
        IRNode::If { then_branch, .. } => try_type(then_branch, env, program),
        IRNode::Tuple(elems) => {
            let tys: Option<Vec<Type>> = elems.iter().map(|e| try_type(e, env, program)).collect();
            Some(Type::Tuple(tys?))
        }
        IRNode::Let {
            pattern,
            value,
            body,
        } => {
            let mut inner = env.clone();
            let vt = try_type(value, env, program);
            let mut dummy_order = Vec::new();
            register_pattern(&mut inner, &mut dummy_order, pattern, vt);
            try_type(body, &inner, program)
        }
        _ => None,
    }
}

/// Whole-word occurrence check for an identifier inside a verbatim Lean type
/// string (used to force referenced value params into segment signatures).
fn mentions_ident(text: &str, ident: &str) -> bool {
    let bytes = text.as_bytes();
    let mut start = 0;
    while let Some(pos) = text[start..].find(ident) {
        let abs = start + pos;
        let before_ok = abs == 0 || !is_ident_char(bytes[abs - 1]);
        let after = abs + ident.len();
        let after_ok = after >= bytes.len() || !is_ident_char(bytes[after]);
        if before_ok && after_ok {
            return true;
        }
        start = abs + 1;
    }
    false
}

fn is_ident_char(b: u8) -> bool {
    b.is_ascii_alphanumeric() || b == b'_' || b == b'\''
}

// ===========================================================================
// Obligation bundles (verification-condition form).
//
// For a bundled `.aborts` function the generator emits, instead of relying on
// proof-side unfolding: one small named obligation per abort check (with its
// path conditions as premises, stated over parent params + atoms via
// let-substitution with projection folding), plus a structural proof tree
// over the `MoveAbort.*_none_*` prelude combinators showing the obligations
// imply `.aborts = none`. Subtrees the fine-grained walk cannot handle
// (dependent-if entry machinery, enum matches, unsubstitutable temps) fall
// back to an opaque segment leaf: `path → <fn>.aborts.seg_k args = none`.
// ===========================================================================

use crate::data::{AbortsBundle, AbortsLeaf, AbortsObligation, AbortsProofNode};

fn collect_used_obs(pn: &AbortsProofNode, used: &mut BTreeSet<usize>) {
    match pn {
        AbortsProofNode::Rfl => {}
        AbortsProofNode::OrElse(a, b)
        | AbortsProofNode::BIte(a, b)
        | AbortsProofNode::DIte(a, b) => {
            collect_used_obs(a, used);
            collect_used_obs(b, used);
        }
        AbortsProofNode::GuardFalse { ob, rest } | AbortsProofNode::GuardTrue { ob, rest } => {
            used.insert(*ob);
            collect_used_obs(rest, used);
        }
        AbortsProofNode::Leaf { ob } => {
            used.insert(*ob);
        }
        AbortsProofNode::AndBool(a, b)
        | AbortsProofNode::PIte(a, b)
        | AbortsProofNode::BIteBool(a, b) => {
            collect_used_obs(a, used);
            collect_used_obs(b, used);
        }
        AbortsProofNode::RequiresApp { req_ob, call_ob } => {
            used.insert(*req_ob);
            used.insert(*call_ob);
        }
    }
}

fn remap_obs(pn: AbortsProofNode, remap: &BTreeMap<usize, usize>) -> AbortsProofNode {
    match pn {
        AbortsProofNode::Rfl => AbortsProofNode::Rfl,
        AbortsProofNode::OrElse(a, b) => AbortsProofNode::OrElse(
            Box::new(remap_obs(*a, remap)),
            Box::new(remap_obs(*b, remap)),
        ),
        AbortsProofNode::BIte(a, b) => AbortsProofNode::BIte(
            Box::new(remap_obs(*a, remap)),
            Box::new(remap_obs(*b, remap)),
        ),
        AbortsProofNode::DIte(a, b) => AbortsProofNode::DIte(
            Box::new(remap_obs(*a, remap)),
            Box::new(remap_obs(*b, remap)),
        ),
        AbortsProofNode::GuardFalse { ob, rest } => AbortsProofNode::GuardFalse {
            ob: remap[&ob],
            rest: Box::new(remap_obs(*rest, remap)),
        },
        AbortsProofNode::GuardTrue { ob, rest } => AbortsProofNode::GuardTrue {
            ob: remap[&ob],
            rest: Box::new(remap_obs(*rest, remap)),
        },
        AbortsProofNode::Leaf { ob } => AbortsProofNode::Leaf { ob: remap[&ob] },
        AbortsProofNode::AndBool(a, b) => AbortsProofNode::AndBool(
            Box::new(remap_obs(*a, remap)),
            Box::new(remap_obs(*b, remap)),
        ),
        AbortsProofNode::PIte(a, b) => AbortsProofNode::PIte(
            Box::new(remap_obs(*a, remap)),
            Box::new(remap_obs(*b, remap)),
        ),
        AbortsProofNode::BIteBool(a, b) => AbortsProofNode::BIteBool(
            Box::new(remap_obs(*a, remap)),
            Box::new(remap_obs(*b, remap)),
        ),
        AbortsProofNode::RequiresApp { req_ob, call_ob } => AbortsProofNode::RequiresApp {
            req_ob: remap[&req_ob],
            call_ob: remap[&call_ob],
        },
    }
}

fn bundle_dbg(msg: &str) {
    if std::env::var("FOXY_DECOMPOSE_DEBUG").is_ok() {
        eprintln!("[bundle] {}", msg);
    }
}

/// `None` marks a temp whose value cannot be expressed over parent params
/// (multi-pattern lets, untypeable values); obligations must not mention it.
pub(crate) type BundleSubst = BTreeMap<TempId, Option<IRNode>>;

#[derive(Default)]
struct BundleAcc {
    obligations: Vec<AbortsObligation>,
    cache: BTreeMap<String, usize>,
}

/// Substitute let-bound temps into `expr` and fold projections of struct
/// literals/updates, so obligation statements are compact and closed over
/// parent params. `None` when the expression mentions an opaque temp.
pub(crate) fn bundle_subst(expr: &IRNode, subst: &BundleSubst) -> Option<IRNode> {
    for v in expr.free_vars() {
        if let Some(None) = subst.get(&v) {
            return None;
        }
    }
    let out = expr.clone().map(&mut |n| match n {
        IRNode::Var(name) => match subst.get(&name) {
            Some(Some(e)) => e.clone(),
            _ => IRNode::Var(name),
        },
        other => fold_proj(other),
    });
    Some(fold_all_projs(out))
}

/// `{s with f_j := v}.f_i` → `v` (i = j) or `s.f_i`; `Pack{..}.f_i` → field i.
fn fold_proj(node: IRNode) -> IRNode {
    match node {
        IRNode::Field {
            struct_id,
            field_index,
            base,
        } => match *base {
            IRNode::UpdateField {
                base: inner,
                struct_id: sid2,
                field_index: j,
                value,
            } if sid2 == struct_id => {
                if j == field_index {
                    *value
                } else {
                    fold_proj(IRNode::Field {
                        struct_id,
                        field_index,
                        base: inner,
                    })
                }
            }
            IRNode::Pack {
                struct_id: sid2,
                fields,
                variant_index: None,
                ..
            } if sid2 == struct_id && field_index < fields.len() => {
                fields.into_iter().nth(field_index).unwrap()
            }
            other => IRNode::Field {
                struct_id,
                field_index,
                base: Box::new(other),
            },
        },
        other => other,
    }
}

fn fold_all_projs(node: IRNode) -> IRNode {
    node.map(&mut fold_proj)
}

/// Mirror of the renderer's `contains_entry_call`: a call carrying a proof
/// placeholder as its last argument forces the enclosing `if` to render as a
/// DEPENDENT `if h : (cond) = true` (render.rs). The bundle proof must use the
/// matching `dite` combinator there.
fn renderer_dep_if(program: &Program, then_branch: &IRNode, else_branch: &IRNode) -> bool {
    let has = |node: &IRNode| {
        node.iter().any(|n| {
            matches!(n, IRNode::Call { function, args, .. }
                if !program.functions.get(function).signature.proof_params.is_empty()
                    && matches!(args.last(), Some(IRNode::Abort { .. })))
        })
    };
    has(then_branch) || has(else_branch)
}

fn contains_abort_node(node: &IRNode) -> bool {
    node.iter().any(|n| matches!(n, IRNode::Abort { .. }))
}

fn is_abort_propagation(binding: &TempId, some_branch: &IRNode) -> bool {
    matches!(some_branch, IRNode::OptionSome(inner) if matches!(inner.as_ref(), IRNode::Var(v) if v == binding))
}

/// Terminal abort constructor (possibly under small lets).
fn is_some_abort(node: &IRNode) -> bool {
    match node {
        IRNode::OptionSome(_) => true,
        IRNode::Let { body, .. } => is_some_abort(body),
        _ => false,
    }
}

fn add_obligation(
    acc: &mut BundleAcc,
    ctx: &SegCtx,
    parent_params: &BTreeMap<TempId, Type>,
    param_order: &[TempId],
    path: &[(IRNode, bool)],
    leaf: AbortsLeaf,
) -> Option<usize> {
    let leaf_exprs: Vec<&IRNode> = match &leaf {
        AbortsLeaf::GuardFalse(e)
        | AbortsLeaf::GuardTrue(e)
        | AbortsLeaf::OptionNone(e)
        | AbortsLeaf::PropHolds(e) => vec![e],
        AbortsLeaf::RequiresHolds { args, .. }
        | AbortsLeaf::CalleeNoneUnderRequires { args, .. } => args.iter().collect(),
    };
    // Every free var must be a parent value param or a proof param.
    let mut free: BTreeSet<TempId> = BTreeSet::new();
    for e in &leaf_exprs {
        free.extend(e.free_vars());
    }
    for (c, _) in path {
        free.extend(c.free_vars());
    }
    for v in &free {
        if !parent_params.contains_key(v) && !ctx.proof_param_names.contains(v) {
            bundle_dbg(&format!(
                "{}: obligation references non-param temp {} (leaf {:?})",
                ctx.parent_name,
                v,
                format!("{:?}", leaf_exprs)
                    .chars()
                    .take(600)
                    .collect::<String>()
            ));
            return None;
        }
    }
    let key = format!("{:?}|{:?}", path, leaf);
    if let Some(&idx) = acc.cache.get(&key) {
        return Some(idx);
    }
    let parameters: Vec<Parameter> = param_order
        .iter()
        .filter(|p| free.contains(*p))
        .map(|p| Parameter {
            name: p.to_string(),
            param_type: parent_params[p].clone(),
            ssa_value: p.clone(),
        })
        .collect();
    let idx = acc.obligations.len();
    acc.obligations.push(AbortsObligation {
        name: format!("ob_{}", idx + 1),
        parameters,
        path: path.to_vec(),
        leaf,
    });
    acc.cache.insert(key, idx);
    Some(idx)
}

/// Opaque fallback: wrap the subtree in a segment function and emit a single
/// `path → seg args = none` obligation. `None` when the segment's arguments
/// cannot be expressed over parent params.
#[allow(clippy::too_many_arguments)]
fn bundle_opaque(
    program: &mut Program,
    ctx: &mut SegCtx,
    acc: &mut BundleAcc,
    parent_params: &BTreeMap<TempId, Type>,
    param_order: &[TempId],
    node: &IRNode,
    env: &Env,
    order: &[TempId],
    subst: &BundleSubst,
    path: &[(IRNode, bool)],
) -> Option<AbortsProofNode> {
    bundle_opaque_leaf(
        program,
        ctx,
        acc,
        parent_params,
        param_order,
        node,
        env,
        order,
        subst,
        path,
        false,
    )
}

/// Shared opaque-segment fallback. `as_prop` selects the ensures-bundle leaf
/// shape (`path → seg args` with a Prop-typed segment) over the aborts shape
/// (`path → seg args = none`).
#[allow(clippy::too_many_arguments)]
fn bundle_opaque_leaf(
    program: &mut Program,
    ctx: &mut SegCtx,
    acc: &mut BundleAcc,
    parent_params: &BTreeMap<TempId, Type>,
    param_order: &[TempId],
    node: &IRNode,
    env: &Env,
    order: &[TempId],
    subst: &BundleSubst,
    path: &[(IRNode, bool)],
    as_prop: bool,
) -> Option<AbortsProofNode> {
    // Pre-verify: every free var of the subtree must be typed here and
    // expressible over parent params, so create_segment cannot leave orphans.
    for v in node.free_vars() {
        if ctx.proof_param_names.contains(&v) {
            continue;
        }
        match env.get(&v) {
            Some(Some(_)) => {}
            _ => {
                bundle_dbg(&format!("opaque: untypeable free var {}", v));
                return None;
            }
        }
        match subst.get(&v) {
            Some(None) => {
                bundle_dbg(&format!("opaque: unsubstitutable free var {}", v));
                return None;
            }
            Some(Some(_)) | None => {}
        }
    }
    let fid = create_segment(program, ctx, node, env, order)?;
    let seg = program.functions.get(&fid).clone();
    let mut args: Vec<IRNode> = Vec::new();
    for p in &seg.signature.parameters {
        let arg = match subst.get(&p.ssa_value) {
            Some(Some(e)) => e.clone(),
            Some(None) => return None,
            None => IRNode::Var(p.ssa_value.clone()),
        };
        args.push(arg);
    }
    for pp in &seg.signature.proof_params {
        args.push(IRNode::Var(TempId::from(pp.name.as_str())));
    }
    let call = IRNode::Call {
        function: fid,
        type_args: Vec::new(),
        args,
    };
    // The parent body must call the segment instead of keeping the subtree
    // inline (single rendering — see `SegCtx::replacements`). The in-parent
    // call takes the segment's params as plain vars (in scope at the
    // subtree's position); the obligation's call uses substituted args.
    ctx.replacements
        .push((format!("{:?}", node), seg_call(program, fid)));
    let leaf = if as_prop {
        AbortsLeaf::PropHolds(call)
    } else {
        AbortsLeaf::OptionNone(call)
    };
    let ob = add_obligation(acc, ctx, parent_params, param_order, path, leaf)?;
    Some(AbortsProofNode::Leaf { ob })
}

/// Walk an `Option MoveAbort` spine collecting obligations; iterative along
/// the spine, recursive across nesting. `None` = this walk failed (caller
/// escalates to an opaque segment, or the whole bundle is abandoned).
#[allow(clippy::too_many_arguments)]
fn bundle_spine(
    program: &mut Program,
    ctx: &mut SegCtx,
    acc: &mut BundleAcc,
    parent_params: &BTreeMap<TempId, Type>,
    param_order: &[TempId],
    node: &IRNode,
    env0: &Env,
    order0: &[TempId],
    subst0: &BundleSubst,
    path: &[(IRNode, bool)],
) -> Option<AbortsProofNode> {
    let mut env = env0.clone();
    let mut order = order0.to_vec();
    let mut subst = subst0.clone();

    // Collect the spine of this subtree (by reference, iteratively).
    let mut spine: Vec<&IRNode> = Vec::new();
    let mut cur = node;
    loop {
        spine.push(cur);
        match cur {
            IRNode::Let { body, .. } => cur = body,
            IRNode::MatchOption {
                binding,
                some_branch,
                none_branch,
                ..
            } if is_abort_propagation(binding, some_branch) => cur = none_branch,
            _ => break,
        }
    }

    // Single forward pass — no per-step snapshots (they multiplied the
    // substitution map's memory by spine length). Each check's sub-proof is
    // built immediately with the current state; the proofs are folded into
    // the orElse chain at the end. Lets contribute nothing to the proof term
    // (the kernel zeta-reduces them during the final defeq check).
    //
    // Escalation: when a check (or the terminal) cannot be handled
    // fine-grained, the remaining tail of the spine becomes ONE opaque
    // segment leaf. Because `spine[i]` is itself the whole tail subtree at
    // step i, that is just a clone. If any earlier binding was poisoned
    // (unsubstitutable), the tail must start at the first poisoned binding so
    // the segment closes over it — one lazy snapshot of (env, order, subst)
    // taken at that point makes this cheap.
    let mut lefts: Vec<AbortsProofNode> = Vec::new();
    let mut poison: Option<(usize, Env, Vec<TempId>, BundleSubst)> = None;

    let escalate = |program: &mut Program,
                    ctx: &mut SegCtx,
                    acc: &mut BundleAcc,
                    poison: &Option<(usize, Env, Vec<TempId>, BundleSubst)>,
                    spine: &[&IRNode],
                    fail_i: usize,
                    env: &Env,
                    order: &[TempId],
                    subst: &BundleSubst,
                    lefts: &mut Vec<AbortsProofNode>|
     -> Option<AbortsProofNode> {
        let (tail_i, e, o, su, keep_lefts) = match poison {
            Some((pi, pe, po, ps)) if *pi <= fail_i => {
                // Count checks strictly before the poison point.
                let kept = spine[..*pi]
                    .iter()
                    .filter(|n| {
                        matches!(n, IRNode::MatchOption { binding, some_branch, .. }
                            if is_abort_propagation(binding, some_branch))
                    })
                    .count();
                (*pi, pe.clone(), po.clone(), ps.clone(), kept)
            }
            _ => (
                fail_i,
                env.clone(),
                order.to_vec(),
                subst.clone(),
                lefts.len(),
            ),
        };
        lefts.truncate(keep_lefts);
        let tail: IRNode = (*spine[tail_i]).clone();
        bundle_opaque(
            program,
            ctx,
            acc,
            parent_params,
            param_order,
            &tail,
            &e,
            &o,
            &su,
            path,
        )
    };

    for (i, step) in spine.iter().enumerate() {
        match step {
            IRNode::Let { pattern, value, .. } => {
                if pattern.is_empty() {
                    // Sequencing let. In `.aborts`-family bodies the renderer
                    // DISCARDS `WriteBack` reconstructions (`let _ := …` — see
                    // render.rs, the `.aborts` receiver-type note), so they
                    // bind nothing and downstream reads see the original
                    // binding — exactly what the substitution assumes.
                    // `MutableCompose` has no such discard form; poison it.
                    if poison.is_none()
                        && value
                            .iter()
                            .any(|n| matches!(n, IRNode::MutableCompose { .. }))
                    {
                        bundle_dbg(&format!(
                            "{}: poison at step {} (mutable compose)",
                            ctx.parent_name, i
                        ));
                        poison = Some((i, env.clone(), order.clone(), subst.clone()));
                    }
                } else if pattern.len() == 1 {
                    // Cap stored substitutions: an oversized value poisons its
                    // temp instead of ballooning every downstream statement
                    // (uses escalate to opaque segment leaves). ALSO poison a
                    // non-trivial value whose temp is referenced more than once
                    // downstream — inlining it duplicates it at every use
                    // (multiplicative blowup); poisoning shares it via a segment.
                    let downstream_uses = node
                        .iter()
                        .filter(|d| matches!(d, IRNode::Var(v) if v == &pattern[0]))
                        .count();
                    let sub = bundle_subst(value, &subst).filter(|e| {
                        approx_size(e) <= SUBST_MAX
                            && !(downstream_uses > 1 && approx_size(e) > MULTI_USE_SUBST_MAX)
                    });
                    if sub.is_none() && poison.is_none() {
                        bundle_dbg(&format!(
                            "{}: poison at step {} (value of {} unsubstitutable/oversized)",
                            ctx.parent_name, i, pattern[0]
                        ));
                        poison = Some((i, env.clone(), order.clone(), subst.clone()));
                    }
                    subst.insert(pattern[0].clone(), sub);
                } else {
                    // Tuple destructure: each component is expressible as a
                    // let-projection of the tuple value — `let (a, b) := e; a`
                    // — which Lean reduces definitionally (structure eta), so
                    // obligations stay closed over parent params. World-mode
                    // uses single-line `World.pfst`/`World.psnd` projection
                    // chains instead: destructures of world-threaded callee
                    // results are pervasive there, and a multi-line `let` in a
                    // NON-TRAILING application argument position is a Lean
                    // parse error (see `Mutable.mkFlip`).
                    match bundle_subst(value, &subst).filter(|e| approx_size(e) <= SUBST_MAX) {
                        Some(ve) => {
                            if let Some(world) = &program.world_functions {
                                let n = pattern.len();
                                for (i, p) in pattern.iter().enumerate() {
                                    let mut e = ve.clone();
                                    for _ in 0..i.min(n - 1) {
                                        e = IRNode::Call {
                                            function: world.psnd,
                                            type_args: vec![],
                                            args: vec![e],
                                        };
                                    }
                                    if i < n - 1 {
                                        e = IRNode::Call {
                                            function: world.pfst,
                                            type_args: vec![],
                                            args: vec![e],
                                        };
                                    }
                                    subst.insert(p.clone(), Some(e));
                                }
                            } else {
                                for p in pattern.iter() {
                                    subst.insert(
                                        p.clone(),
                                        Some(IRNode::Let {
                                            pattern: pattern.clone(),
                                            value: Box::new(ve.clone()),
                                            body: Box::new(IRNode::Var(p.clone())),
                                        }),
                                    );
                                }
                            }
                        }
                        None => {
                            if poison.is_none() {
                                bundle_dbg(&format!(
                                    "{}: poison at step {} (tuple value unsubstitutable)",
                                    ctx.parent_name, i
                                ));
                                poison = Some((i, env.clone(), order.clone(), subst.clone()));
                            }
                            for p in pattern.iter() {
                                subst.insert(p.clone(), None);
                            }
                        }
                    }
                }
                let vt = try_type(value, &env, program);
                register_pattern(&mut env, &mut order, pattern, vt);
            }
            IRNode::MatchOption {
                scrutinee,
                binding,
                some_branch,
                ..
            } if is_abort_propagation(binding, some_branch) => {
                match bundle_expr(
                    program,
                    ctx,
                    acc,
                    parent_params,
                    param_order,
                    scrutinee,
                    &env,
                    &order,
                    &subst,
                    path,
                ) {
                    Some(pn) => lefts.push(pn),
                    None => {
                        let tail = escalate(
                            program, ctx, acc, &poison, &spine, i, &env, &order, &subst, &mut lefts,
                        )?;
                        let mut proof = tail;
                        for left in lefts.drain(..).rev() {
                            proof = AbortsProofNode::OrElse(Box::new(left), Box::new(proof));
                        }
                        return Some(proof);
                    }
                }
            }
            _ => {}
        }
    }

    let last_i = spine.len() - 1;
    let last = *spine.last().unwrap();
    let mut proof = match bundle_expr(
        program,
        ctx,
        acc,
        parent_params,
        param_order,
        last,
        &env,
        &order,
        &subst,
        path,
    ) {
        Some(pn) => pn,
        None => escalate(
            program, ctx, acc, &poison, &spine, last_i, &env, &order, &subst, &mut lefts,
        )?,
    };
    for left in lefts.into_iter().rev() {
        proof = AbortsProofNode::OrElse(Box::new(left), Box::new(proof));
    }
    Some(proof)
}

/// One `Option MoveAbort` expression (a check scrutinee, branch, or terminal).
#[allow(clippy::too_many_arguments)]
fn bundle_expr(
    program: &mut Program,
    ctx: &mut SegCtx,
    acc: &mut BundleAcc,
    parent_params: &BTreeMap<TempId, Type>,
    param_order: &[TempId],
    node: &IRNode,
    env: &Env,
    order: &[TempId],
    subst: &BundleSubst,
    path: &[(IRNode, bool)],
) -> Option<AbortsProofNode> {
    match node {
        IRNode::OptionNone => Some(AbortsProofNode::Rfl),
        IRNode::Let { .. } => bundle_spine(
            program,
            ctx,
            acc,
            parent_params,
            param_order,
            node,
            env,
            order,
            subst,
            path,
        ),
        IRNode::MatchOption {
            binding,
            some_branch,
            ..
        } if is_abort_propagation(binding, some_branch) => bundle_spine(
            program,
            ctx,
            acc,
            parent_params,
            param_order,
            node,
            env,
            order,
            subst,
            path,
        ),
        IRNode::If {
            cond,
            then_branch,
            else_branch,
        } => {
            // Dependent if (renders as `if h : (cond) = true`): nothing moves,
            // so walk straight through with the dite combinator — entry-call
            // leaves resolve to `Rfl` (their callees' bodies are literal
            // `none`), and the branch facts land as obligation premises.
            if renderer_dep_if(program, then_branch, else_branch) {
                let Some(sc) = bundle_subst(cond, subst) else {
                    return bundle_opaque(
                        program,
                        ctx,
                        acc,
                        parent_params,
                        param_order,
                        node,
                        env,
                        order,
                        subst,
                        path,
                    );
                };
                let mut pt = path.to_vec();
                pt.push((sc.clone(), true));
                let t = bundle_expr(
                    program,
                    ctx,
                    acc,
                    parent_params,
                    param_order,
                    then_branch,
                    env,
                    order,
                    subst,
                    &pt,
                )?;
                let mut pe = path.to_vec();
                pe.push((sc, false));
                let e = bundle_expr(
                    program,
                    ctx,
                    acc,
                    parent_params,
                    param_order,
                    else_branch,
                    env,
                    order,
                    subst,
                    &pe,
                )?;
                return Some(AbortsProofNode::DIte(Box::new(t), Box::new(e)));
            }
            // Other proof placeholders (raw abort paths) stay in one function.
            if contains_abort_node(node) {
                return bundle_opaque(
                    program,
                    ctx,
                    acc,
                    parent_params,
                    param_order,
                    node,
                    env,
                    order,
                    subst,
                    path,
                );
            }
            let Some(sc) = bundle_subst(cond, subst) else {
                let bad: Vec<String> = cond
                    .free_vars()
                    .iter()
                    .filter(|v| matches!(subst.get(*v), Some(None)))
                    .map(|v| v.to_string())
                    .collect();
                bundle_dbg(&format!("if-cond not substitutable, opaque vars {:?}", bad));
                return None;
            };
            if is_some_abort(then_branch) {
                let ob = add_obligation(
                    acc,
                    ctx,
                    parent_params,
                    param_order,
                    path,
                    AbortsLeaf::GuardFalse(sc),
                )?;
                let rest = bundle_expr(
                    program,
                    ctx,
                    acc,
                    parent_params,
                    param_order,
                    else_branch,
                    env,
                    order,
                    subst,
                    path,
                )?;
                Some(AbortsProofNode::GuardFalse {
                    ob,
                    rest: Box::new(rest),
                })
            } else if is_some_abort(else_branch) {
                let ob = add_obligation(
                    acc,
                    ctx,
                    parent_params,
                    param_order,
                    path,
                    AbortsLeaf::GuardTrue(sc),
                )?;
                let rest = bundle_expr(
                    program,
                    ctx,
                    acc,
                    parent_params,
                    param_order,
                    then_branch,
                    env,
                    order,
                    subst,
                    path,
                )?;
                Some(AbortsProofNode::GuardTrue {
                    ob,
                    rest: Box::new(rest),
                })
            } else {
                let mut pt = path.to_vec();
                pt.push((sc.clone(), true));
                let t = bundle_expr(
                    program,
                    ctx,
                    acc,
                    parent_params,
                    param_order,
                    then_branch,
                    env,
                    order,
                    subst,
                    &pt,
                )?;
                let mut pe = path.to_vec();
                pe.push((sc, false));
                let e = bundle_expr(
                    program,
                    ctx,
                    acc,
                    parent_params,
                    param_order,
                    else_branch,
                    env,
                    order,
                    subst,
                    &pe,
                )?;
                Some(AbortsProofNode::BIte(Box::new(t), Box::new(e)))
            }
        }
        IRNode::Call { function, args, .. } => {
            let callee = program.functions.get(function);
            if !callee.is_native && matches!(callee.body, IRNode::OptionNone) {
                return Some(AbortsProofNode::Rfl);
            }
            // Requires-slot leaf (§5.2, `requires_leaves` gate): a callee
            // whose single verbatim proof param is filled by an `Abort`
            // placeholder gets a named precondition leaf + a ∀-bound
            // callee-aborts leaf instead of an opaque segment around the
            // `sorry`-slotted call.
            if requires_leaves_enabled(program)
                && program.callee_requires_impls.contains(function)
                && callee.signature.proof_params.len() == 1
                && matches!(
                    callee.signature.proof_params[0].param_type,
                    ProofParamType::Verbatim(_)
                )
                && args.len() == callee.signature.parameters.len() + 1
                && matches!(args.last(), Some(IRNode::Abort { .. }))
            {
                let vargs: Option<Vec<IRNode>> = args[..args.len() - 1]
                    .iter()
                    .map(|a| bundle_subst(a, subst).filter(|e| approx_size(e) <= SUBST_MAX))
                    .collect();
                if let Some(vargs) = vargs {
                    let function = *function;
                    let req_ob = add_obligation(
                        acc,
                        ctx,
                        parent_params,
                        param_order,
                        path,
                        AbortsLeaf::RequiresHolds {
                            callee: function,
                            args: vargs.clone(),
                        },
                    );
                    let call_ob = add_obligation(
                        acc,
                        ctx,
                        parent_params,
                        param_order,
                        path,
                        AbortsLeaf::CalleeNoneUnderRequires {
                            callee: function,
                            args: vargs,
                        },
                    );
                    if let (Some(req_ob), Some(call_ob)) = (req_ob, call_ob) {
                        return Some(AbortsProofNode::RequiresApp { req_ob, call_ob });
                    }
                }
                // Fall through to the opaque fallback below.
            }
            if contains_abort_node(node) {
                return bundle_opaque(
                    program,
                    ctx,
                    acc,
                    parent_params,
                    param_order,
                    node,
                    env,
                    order,
                    subst,
                    path,
                );
            }
            let e = bundle_subst(node, subst)?;
            let ob = add_obligation(
                acc,
                ctx,
                parent_params,
                param_order,
                path,
                AbortsLeaf::OptionNone(e),
            )?;
            Some(AbortsProofNode::Leaf { ob })
        }
        IRNode::Var(_) => {
            let e = bundle_subst(node, subst)?;
            if matches!(e, IRNode::OptionNone) {
                return Some(AbortsProofNode::Rfl);
            }
            let ob = add_obligation(
                acc,
                ctx,
                parent_params,
                param_order,
                path,
                AbortsLeaf::OptionNone(e),
            )?;
            Some(AbortsProofNode::Leaf { ob })
        }
        other => bundle_opaque(
            program,
            ctx,
            acc,
            parent_params,
            param_order,
            other,
            env,
            order,
            subst,
            path,
        ),
    }
}

// ===========================================================================
// Ensures bundles (unified-backend design §5.1, Phase 3.1).
//
// The `.aborts` bundle machinery generalized to `.ensures` companions: the
// ensures spine is a `Let` chain ending in a Prop terminal built from
// `ToProp` leaves, Bool conjunctions (`(a && b) = true`, split via
// `SpecEnsures.and_of`), and Prop-branched `ite`s (split via
// `SpecEnsures.ite_of`). Anything the walk cannot express over parent params
// (quantified subtrees with poisoned temps, dependent ifs, enum matches)
// falls back to an opaque Prop segment leaf — never silently dropped. The
// generator emits `<fn>.ob_k` defs plus a `<fn>_of` theorem whose structural
// proof recomposes the leaves into `<fn> args`.
// ===========================================================================

/// The per-package `ensures_bundles` gate: any scanned
/// `def <Module>.module_options` hook that lists `"ensures_bundles"`.
pub fn ensures_bundles_enabled(program: &Program) -> bool {
    program
        .lean_termination_decls
        .module_options
        .values()
        .any(|opts| opts.contains("ensures_bundles"))
}

/// `<fn>.ensures` or `<fn>.ensures_<n>`.
fn is_ensures_name(name: &str) -> bool {
    let Some(i) = name.rfind(".ensures") else {
        return false;
    };
    let rest = &name[i + ".ensures".len()..];
    rest.is_empty()
        || (rest.len() > 1
            && rest.starts_with('_')
            && rest[1..].chars().all(|c| c.is_ascii_digit()))
}

pub fn decompose_ensures(program: &mut Program) {
    if !ensures_bundles_enabled(program) {
        return;
    }
    let debug = std::env::var("FOXY_DECOMPOSE_DEBUG").is_ok();
    let candidates: Vec<FunctionID> = program
        .functions
        .iter_ids()
        .filter(|id| is_ensures_name(&program.functions.get(id).name))
        .collect();
    for id in candidates {
        let f = program.functions.get(&id);
        if f.is_native
            || f.theorem.is_some()
            || f.mutual_group_id.is_some()
            || !f.signature.type_params.is_empty()
            || f.signature.return_type != Type::Prop
        {
            continue;
        }
        if f.body.calls().any(|c| c == id) {
            continue;
        }
        if f.signature.parameters.iter().any(|p| {
            matches!(
                p.param_type,
                Type::MutableReference(_, _) | Type::Reference(_)
            )
        }) {
            continue;
        }
        if f.signature.proof_params.iter().any(|pp| {
            !matches!(
                pp.param_type,
                ProofParamType::Verbatim(_) | ProofParamType::DataInvWorld { .. }
            )
        }) {
            continue;
        }
        ensures_one(program, id, debug);
    }
}

fn ensures_one(program: &mut Program, id: FunctionID, debug: bool) {
    let parent = program.functions.get(&id).clone();

    let env: Env = parent
        .signature
        .parameters
        .iter()
        .map(|p| (p.ssa_value.clone(), Some(p.param_type.clone())))
        .collect();
    let order: Vec<TempId> = parent
        .signature
        .parameters
        .iter()
        .map(|p| p.ssa_value.clone())
        .collect();
    let parent_param_mentions = parent
        .signature
        .proof_params
        .iter()
        .map(|pp| {
            let mentions = match &pp.param_type {
                ProofParamType::Verbatim(text) => parent
                    .signature
                    .parameters
                    .iter()
                    .filter(|p| mentions_ident(text, &p.ssa_value))
                    .map(|p| p.ssa_value.clone())
                    .collect(),
                ProofParamType::DataInvWorld { parent_expr, .. } => parent
                    .signature
                    .parameters
                    .iter()
                    .filter(|p| {
                        mentions_ident(parent_expr, &p.ssa_value)
                            || p.name == super::world_threading::WORLD_VAR
                    })
                    .map(|p| p.ssa_value.clone())
                    .collect(),
                _ => Vec::new(),
            };
            (TempId::from(pp.name.as_str()), mentions)
        })
        .collect();

    let mut ctx = SegCtx {
        parent_name: parent.name.clone(),
        module_id: parent.module_id,
        // Opaque fallbacks are Prop-typed segments on the ensures side.
        return_type: Type::Prop,
        proof_params: parent.signature.proof_params.clone(),
        proof_param_names: parent
            .signature
            .proof_params
            .iter()
            .map(|pp| TempId::from(pp.name.as_str()))
            .collect(),
        parent_param_mentions,
        counter: 0,
        created: Vec::new(),
        atom_counter: 0,
        atom_cache: BTreeMap::new(),
        replacements: Vec::new(),
    };

    // No atom hoisting on the ensures side: ensures-face atoms would render
    // without `@[reducible]` (the name-based suppression keys on `.ensures`),
    // and the SUBST_MAX cap already bounds leaf statements — oversized
    // subtrees escalate to opaque Prop segments instead.
    let body = parent.body.clone();

    let parent_params: BTreeMap<TempId, Type> = parent
        .signature
        .parameters
        .iter()
        .map(|p| (p.ssa_value.clone(), p.param_type.clone()))
        .collect();
    let mut acc = BundleAcc::default();
    let subst: BundleSubst = BTreeMap::new();
    let Some(proof) = ensures_spine(
        program,
        &mut ctx,
        &mut acc,
        &parent_params,
        &order,
        &body,
        &env,
        &order,
        &subst,
        &[],
    ) else {
        if debug {
            eprintln!("[decompose] {} ensures bundle bail", parent.name);
        }
        return;
    };

    let mut used: BTreeSet<usize> = BTreeSet::new();
    collect_used_obs(&proof, &mut used);
    let remap: BTreeMap<usize, usize> = used
        .iter()
        .enumerate()
        .map(|(new, old)| (*old, new))
        .collect();
    let obligations: Vec<AbortsObligation> = acc
        .obligations
        .into_iter()
        .enumerate()
        .filter(|(i, _)| used.contains(i))
        .map(|(i, mut ob)| {
            ob.name = format!("ob_{}", remap[&i] + 1);
            ob
        })
        .collect();
    let proof = remap_obs(proof, &remap);

    // A 0-leaf ensures bundle is a trivially-true face (`ensures(true)`), a
    // 1-leaf bundle is pure indirection: skip both — the ensures form only
    // pays for itself when it SPLITS the postcondition into ≥ 2 leaves.
    // (Any segment/atom created during a skipped walk stays as dead code,
    // same as the aborts small-skip path.)
    if obligations.len() < 2 {
        if debug {
            eprintln!(
                "[decompose] {} ensures bundle skip ({} leaves)",
                parent.name,
                obligations.len()
            );
        }
        return;
    }

    let replacements = std::mem::take(&mut ctx.replacements);
    let body = body.map_top_down(&mut |n| {
        let key = format!("{:?}", n);
        for (k, call) in &replacements {
            if *k == key {
                return call.clone();
            }
        }
        n
    });
    program.functions.get_mut(id).body = body;
    if program.callee_requires_precond_callers.contains(&id) {
        for seg in &ctx.created {
            program.callee_requires_precond_callers.insert(*seg);
        }
    }
    if debug {
        eprintln!(
            "[decompose] {} -> ensures bundle: {} obligations, {} opaque segments, {} atoms",
            parent.name,
            obligations.len(),
            ctx.created.len(),
            ctx.atom_counter
        );
    }
    program.ensures_bundles.push(AbortsBundle {
        fn_id: id,
        obligations,
        proof,
    });
}

/// Walk an ensures `Let` spine (no abort checks on this side) collecting the
/// substitution, then hand the terminal to [`ensures_expr`]. Poisoned
/// bindings escalate the remaining tail to one opaque Prop segment.
#[allow(clippy::too_many_arguments)]
fn ensures_spine(
    program: &mut Program,
    ctx: &mut SegCtx,
    acc: &mut BundleAcc,
    parent_params: &BTreeMap<TempId, Type>,
    param_order: &[TempId],
    node: &IRNode,
    env0: &Env,
    order0: &[TempId],
    subst0: &BundleSubst,
    path: &[(IRNode, bool)],
) -> Option<AbortsProofNode> {
    let mut env = env0.clone();
    let mut order = order0.to_vec();
    let mut subst = subst0.clone();

    let mut spine: Vec<&IRNode> = Vec::new();
    let mut cur = node;
    loop {
        spine.push(cur);
        match cur {
            IRNode::Let { body, .. } => cur = body,
            _ => break,
        }
    }

    let mut poison: Option<(usize, Env, Vec<TempId>, BundleSubst)> = None;
    for (i, step) in spine.iter().enumerate() {
        if let IRNode::Let { pattern, value, .. } = step {
            if pattern.is_empty() {
                if poison.is_none()
                    && value
                        .iter()
                        .any(|n| matches!(n, IRNode::MutableCompose { .. }))
                {
                    poison = Some((i, env.clone(), order.clone(), subst.clone()));
                }
            } else if pattern.len() == 1 {
                let sub = bundle_subst(value, &subst).filter(|e| approx_size(e) <= SUBST_MAX);
                if sub.is_none() && poison.is_none() {
                    bundle_dbg(&format!(
                        "{}: ensures poison at step {} (value of {} unsubstitutable/oversized)",
                        ctx.parent_name, i, pattern[0]
                    ));
                    poison = Some((i, env.clone(), order.clone(), subst.clone()));
                }
                subst.insert(pattern[0].clone(), sub);
            } else {
                match bundle_subst(value, &subst).filter(|e| approx_size(e) <= SUBST_MAX) {
                    Some(ve) => {
                        // See the aborts-side arm: world-mode uses single-line
                        // projection chains (parse + defeq behavior).
                        if let Some(world) = &program.world_functions {
                            let n = pattern.len();
                            for (i, p) in pattern.iter().enumerate() {
                                let mut e = ve.clone();
                                for _ in 0..i.min(n - 1) {
                                    e = IRNode::Call {
                                        function: world.psnd,
                                        type_args: vec![],
                                        args: vec![e],
                                    };
                                }
                                if i < n - 1 {
                                    e = IRNode::Call {
                                        function: world.pfst,
                                        type_args: vec![],
                                        args: vec![e],
                                    };
                                }
                                subst.insert(p.clone(), Some(e));
                            }
                        } else {
                            for p in pattern.iter() {
                                subst.insert(
                                    p.clone(),
                                    Some(IRNode::Let {
                                        pattern: pattern.clone(),
                                        value: Box::new(ve.clone()),
                                        body: Box::new(IRNode::Var(p.clone())),
                                    }),
                                );
                            }
                        }
                    }
                    None => {
                        if poison.is_none() {
                            poison = Some((i, env.clone(), order.clone(), subst.clone()));
                        }
                        for p in pattern.iter() {
                            subst.insert(p.clone(), None);
                        }
                    }
                }
            }
            let vt = try_type(value, &env, program);
            register_pattern(&mut env, &mut order, pattern, vt);
        }
    }

    let last_i = spine.len() - 1;
    let last = *spine.last().unwrap();
    match ensures_expr(
        program,
        ctx,
        acc,
        parent_params,
        param_order,
        last,
        &env,
        &order,
        &subst,
        path,
    ) {
        Some(pn) => Some(pn),
        None => {
            // Escalate: the tail from the first poisoned binding (or the
            // terminal) becomes one opaque Prop segment leaf.
            let (tail_i, e, o, su) = match &poison {
                Some((pi, pe, po, ps)) if *pi <= last_i => {
                    (*pi, pe.clone(), po.clone(), ps.clone())
                }
                _ => (last_i, env.clone(), order.clone(), subst.clone()),
            };
            let tail: IRNode = (*spine[tail_i]).clone();
            bundle_opaque_leaf(
                program,
                ctx,
                acc,
                parent_params,
                param_order,
                &tail,
                &e,
                &o,
                &su,
                path,
                true,
            )
        }
    }
}

/// Flatten the top-level single-binding `let` chain of a closed Bool
/// expression by substitution (small, SUBST_MAX-capped inputs), exposing the
/// `&&`/`ite` split shapes to the dispatch below. Multi-binding lets stop the
/// walk (the remaining chain stays a single leaf).
fn strip_bool_lets(e: IRNode) -> IRNode {
    let mut map: BTreeMap<TempId, IRNode> = BTreeMap::new();
    let mut cur = e;
    loop {
        match cur {
            IRNode::Let {
                pattern,
                value,
                body,
            } if pattern.len() == 1 => {
                let v = subst_exprs(*value, &map);
                map.insert(pattern[0].clone(), v);
                cur = *body;
            }
            other => return fold_all_projs(subst_exprs(other, &map)),
        }
    }
}

/// One Prop-typed ensures expression (a terminal, conjunct, or ite branch).
#[allow(clippy::too_many_arguments)]
fn ensures_expr(
    program: &mut Program,
    ctx: &mut SegCtx,
    acc: &mut BundleAcc,
    parent_params: &BTreeMap<TempId, Type>,
    param_order: &[TempId],
    node: &IRNode,
    env: &Env,
    order: &[TempId],
    subst: &BundleSubst,
    path: &[(IRNode, bool)],
) -> Option<AbortsProofNode> {
    use crate::data::ir::{BinOp, Const};
    let opaque = |program: &mut Program, ctx: &mut SegCtx, acc: &mut BundleAcc| {
        bundle_opaque_leaf(
            program,
            ctx,
            acc,
            parent_params,
            param_order,
            node,
            env,
            order,
            subst,
            path,
            true,
        )
    };
    match node {
        IRNode::Let { .. } => ensures_spine(
            program,
            ctx,
            acc,
            parent_params,
            param_order,
            node,
            env,
            order,
            subst,
            path,
        ),
        IRNode::ToProp(inner) => {
            if contains_abort_node(node) {
                return opaque(program, ctx, acc);
            }
            // Substitute FIRST, then dispatch on the closed Bool expression:
            // ensures faces let-bind their conjunctions/ites
            // (`let tmp := a && b; (tmp = true)`), so the split shapes only
            // surface after substitution + top-level let flattening.
            let Some(sub) = bundle_subst(inner, subst) else {
                return opaque(program, ctx, acc);
            };
            let sub = strip_bool_lets(sub);
            match sub {
                IRNode::Const(Const::Bool(true)) => Some(AbortsProofNode::Rfl),
                IRNode::BinOp {
                    op: BinOp::And,
                    lhs,
                    rhs,
                } => {
                    let l = ensures_expr(
                        program,
                        ctx,
                        acc,
                        parent_params,
                        param_order,
                        &IRNode::ToProp(lhs),
                        env,
                        order,
                        subst,
                        path,
                    )?;
                    let r = ensures_expr(
                        program,
                        ctx,
                        acc,
                        parent_params,
                        param_order,
                        &IRNode::ToProp(rhs),
                        env,
                        order,
                        subst,
                        path,
                    )?;
                    Some(AbortsProofNode::AndBool(Box::new(l), Box::new(r)))
                }
                IRNode::If {
                    cond,
                    then_branch,
                    else_branch,
                } => {
                    // Bool-valued ite under `= true`: split with
                    // `SpecEnsures.bite_eq_true_of`.
                    let mut pt = path.to_vec();
                    pt.push(((*cond).clone(), true));
                    let t = ensures_expr(
                        program,
                        ctx,
                        acc,
                        parent_params,
                        param_order,
                        &IRNode::ToProp(then_branch),
                        env,
                        order,
                        subst,
                        &pt,
                    )?;
                    let mut pe = path.to_vec();
                    pe.push(((*cond).clone(), false));
                    let e = ensures_expr(
                        program,
                        ctx,
                        acc,
                        parent_params,
                        param_order,
                        &IRNode::ToProp(else_branch),
                        env,
                        order,
                        subst,
                        &pe,
                    )?;
                    Some(AbortsProofNode::BIteBool(Box::new(t), Box::new(e)))
                }
                other => {
                    let ob = add_obligation(
                        acc,
                        ctx,
                        parent_params,
                        param_order,
                        path,
                        AbortsLeaf::PropHolds(IRNode::ToProp(Box::new(other))),
                    )?;
                    Some(AbortsProofNode::Leaf { ob })
                }
            }
        }
        IRNode::If {
            cond,
            then_branch,
            else_branch,
        } => {
            // Dependent ifs and raw abort placeholders stay in one function —
            // the opaque Prop segment keeps guard + placeholder paired.
            if renderer_dep_if(program, then_branch, else_branch) || contains_abort_node(node) {
                return opaque(program, ctx, acc);
            }
            // The `SpecEnsures.ite_of` combinator splits on a Bool guard.
            if !matches!(try_type(cond, env, program), Some(Type::Bool)) {
                return opaque(program, ctx, acc);
            }
            let Some(sc) = bundle_subst(cond, subst) else {
                return opaque(program, ctx, acc);
            };
            let mut pt = path.to_vec();
            pt.push((sc.clone(), true));
            let t = ensures_expr(
                program,
                ctx,
                acc,
                parent_params,
                param_order,
                then_branch,
                env,
                order,
                subst,
                &pt,
            )?;
            let mut pe = path.to_vec();
            pe.push((sc, false));
            let e = ensures_expr(
                program,
                ctx,
                acc,
                parent_params,
                param_order,
                else_branch,
                env,
                order,
                subst,
                &pe,
            )?;
            Some(AbortsProofNode::PIte(Box::new(t), Box::new(e)))
        }
        // Any other Prop-typed expression (quantifiers, Prop-returning calls,
        // spec-variable reads) is a direct leaf when statable over parent
        // params; otherwise the opaque fallback covers it.
        other => {
            if contains_abort_node(other) {
                return opaque(program, ctx, acc);
            }
            match bundle_subst(other, subst) {
                Some(e) => {
                    let ob = add_obligation(
                        acc,
                        ctx,
                        parent_params,
                        param_order,
                        path,
                        AbortsLeaf::PropHolds(e),
                    )?;
                    Some(AbortsProofNode::Leaf { ob })
                }
                None => opaque(program, ctx, acc),
            }
        }
    }
}
