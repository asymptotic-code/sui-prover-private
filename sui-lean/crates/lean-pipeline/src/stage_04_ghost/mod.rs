//! Stage 4g -- ghost-variable threading + op lowering (spec-only).
//!
//! A standalone stage, independent of world/effects: it threads the
//! per-function SPEC-ONLY ghost variables recorded in
//! [`crate::ir::Program::ghost_vars`] and lowers the ghost ops
//! (`global` / `borrow_mut` reads, `set` / `*borrow_mut()=` writes) onto
//! those threaded variables.
//!
//! The threading mirrors the world transforms
//! (`stage_04_effects::{signatures, call_augment, body_tail}`) but
//! appends the ghost slots *after* the trailing `world` slot in params,
//! return tuples, call args, and tails. So this stage runs AFTER stage 4
//! (world threading -- the `world` slot must already be in place) and
//! BEFORE stage 5 (SSA -- which then versions the rebinds the op-lowering
//! introduces, so a post-write `global` read resolves to the written
//! value).
//!
//! Ghost is spec-only: these variables are NEVER materialised in
//! `World`/`TyCode`. Each ghost var `(K, V)` threads as a value of type
//! `V` under a deterministic local id `__ghost_<struct_id(K)>`, so a
//! caller passes its var straight into a callee's matching slot (identity
//! match; order follows `ghost_vars[fid]`, the upstream-`Type` sort, so
//! caller/callee agree positionally). The analysis is transitive, so a
//! caller's ghost set is a superset of every callee's -- the var is
//! always in scope.
//!
//! Raw natives (`NativeDecl`) are not in `ghost_vars` from the upstream
//! analysis (they have no bytecode to analyse). Stage 2's
//! `ProgramBuilder::derive_native_ghost_seed` instead reads each native's
//! `#[spec(target=...)]` spec from the Move model and records the markers
//! it declares in [`crate::ir::Program::ghost_native_seed`]; this stage
//! folds that into `ghost_vars`, and the callee->caller fixpoint
//! propagates the set to every (spec-shadowed) caller. Each writing
//! native's Lean def (`lemmas/natives/...`) threads + RETURNS the written
//! values as positional typed slots, so the static native files never
//! name a spec-package marker.

use std::collections::{BTreeMap, BTreeSet, HashMap};

use crate::ir::analysis::type_of::substitute_type_params;
use crate::ir::borrow::BorrowNode;
use crate::ir::visit::{walk_expr_default, walk_expr_mut_default, MutVisitor, Visitor};
use crate::ir::{
    Block, BlockTail, Expr, FunId, MatchArm, Param, Program, Signature, Stmt, StructId, Type, VarId,
};

/// Run the ghost stage end-to-end: seed the native writers, complete the
/// threading set (callee->caller fixpoint), thread the vars through
/// signatures / call sites / body tails (mirroring world), then lower the
/// ghost ops onto the threaded vars (`global`/`borrow_mut` call -> the
/// var; `set` / the `SpecGlobalRoot` writeback -> rebind the var).
pub fn run(program: &mut Program) {
    // Datatype name tags, resolved once. The stage mutates
    // `program.ghost_vars` while it needs the tags, so carrying a map
    // rather than re-reading `&Program` keeps the borrows disjoint.
    let tags = build_struct_tags(program);
    seed_native_ghost_vars(program, &tags);
    ghost_vars_fixpoint(program, &tags);
    let opaque_plan = plan_opaque_ghost_outputs(program, &tags);
    if !opaque_plan.is_empty() {
        // The planned (K, V)s were added to `ghost_vars[impl]`; propagate
        // them to every (transitive) caller so call sites thread them.
        ghost_vars_fixpoint(program, &tags);
    }
    augment_signatures(program, &tags);
    augment_call_sites(program, &tags);
    materialize_opaque_ghost_outputs(program, opaque_plan, &tags);
    augment_body_tails(program, &tags);
    lower_ghost_ops(program, &tags);
}

/// Datatype `StructId` -> stable NAME tag, for every datatype in the
/// program. See [`crate::render::struct_idx`].
pub(crate) type StructTags = HashMap<StructId, String>;

fn build_struct_tags(program: &Program) -> StructTags {
    program
        .structs
        .keys()
        .map(|sid| {
            (
                *sid,
                crate::render::struct_idx::struct_tag_name(*sid, program),
            )
        })
        .collect()
}

/// The threaded-variable id for a ghost marker `K` (the marker struct,
/// e.g. `SpecTransferAddress`).
///
/// The name is derived from the marker datatype's NAME, never its
/// `StructId`. The id is positional -- `Program::next_struct_id` hands
/// it out in module-name walk order -- so a `__ghost_<struct_id>`
/// binder was renamed by any module rename anywhere in the program,
/// which moved every obligation fingerprint that mentions it. See
/// `render::struct_idx`.
fn ghost_varid(k: &Type, tags: &StructTags) -> VarId {
    VarId::from(format!("__ghost_{}", ghost_marker_tag(k, tags)).as_str())
}

/// Identifier-safe tag for a ghost marker type. A marker is always a
/// datatype (the `K` of `ghost::global<K, V>`); anything else never had
/// a valid Lean spelling here (a `Debug`-formatted `Type` is not an
/// identifier), so it is a bug, not a case to fall back on.
fn ghost_marker_tag<'a>(k: &Type, tags: &'a StructTags) -> &'a str {
    match k {
        Type::Struct { struct_id, .. } => tags
            .get(struct_id)
            .unwrap_or_else(|| panic!("ghost marker names unknown StructId {struct_id}"))
            .as_str(),
        other => panic!("ghost marker is not a datatype: {other:?}"),
    }
}

/// Sort a ghost-var set by the marker's NAME tag -- the deterministic
/// order used everywhere (`Type` isn't `Ord`). Name order rather than
/// `StructId` order because the slots are POSITIONAL in the generated
/// `<fn>__ghost` signature: sorting by the positional id let a module
/// rename permute the slots of an untouched function.
fn sort_ghost_set(set: &mut [(Type, Type)], tags: &StructTags) {
    set.sort_by(|(a, _), (b, _)| ghost_marker_tag(a, tags).cmp(ghost_marker_tag(b, tags)));
}

/// Seed `program.ghost_vars` for the ghost-writing natives from the
/// model-derived [`crate::ir::Program::ghost_native_seed`] (built in
/// stage 2 by `ProgramBuilder::derive_native_ghost_seed` from each
/// native's `#[spec(target=...)]` spec). Each seeded native's
/// `<name>__ghost` Lean def threads + RETURNS these markers as positional
/// typed slots, sorted by struct_id; the renderer routes a threaded call
/// to that variant (`render::expr::call`).
fn seed_native_ghost_vars(program: &mut Program, tags: &StructTags) {
    let seed = std::mem::take(&mut program.ghost_native_seed);
    for (native_fid, mut markers) in seed {
        sort_ghost_set(&mut markers, tags);
        program.ghost_vars.insert(native_fid, markers);
    }
}

/// Ensures-published ghosts (the `SpecBalanceValue` pattern): a TRUSTED
/// spec whose ensures constrain a ghost `(K, V)` that the target impl's
/// body never realises (`(K, V) ∈ ghost_vars[spec] \ ghost_vars[impl]`
/// after the native-seeded fixpoint). Boogie realises the value by
/// havoc-and-assume at the opaque call; threading it as a passthrough
/// instead makes the stage-12 trusted axiom quantify over a free input
/// and become INCONSISTENT (derivably false -- ghost-support.md Part 4).
///
/// Plan: for each such pair, add the `(K, V)` to `ghost_vars[impl]` (so
/// the normal augmentation threads it) and return the plan; after
/// signature/call augmentation, [`materialize_opaque_ghost_outputs`]
/// synthesises one OPAQUE native per `(impl, K, V)` and rebinds the
/// threaded var to it at the impl's entry, so the impl's ghost output is
/// an underspecified-but-fixed function of its inputs that the trusted
/// axiom then constrains -- exactly assume-callee-ensures.
///
/// Over-approximation note: `ghost_vars[spec]` doesn't distinguish
/// ensures-reads from pre-call reads (bytecode temp-binds everything), so
/// a trusted spec that only PRE-reads an unrealised ghost also gets an
/// opaque output. That direction is sound (a caller obligation may become
/// unprovable, never an inconsistent axiom); the precise trigger would
/// need a backward slice into the ensures args.
///
/// Prove pairs are never opacified: their ghost ensures must be PROVEN,
/// which requires a realised callee chain -- an unrealised published
/// ghost there is an honestly unprovable obligation, not a hole to paper
/// over.
fn plan_opaque_ghost_outputs(program: &mut Program, tags: &StructTags) -> Vec<(FunId, Type, Type)> {
    let mut planned: Vec<(FunId, Type, Type)> = Vec::new();
    for (&spec_fid, &(impl_fid, _)) in &program.trusted_spec_to_impl {
        // Native impls are handled by the native seed + hand-written
        // `<name>__ghost` variants; only translated impls need synthesis.
        if !program.functions.contains_key(&impl_fid) {
            continue;
        }
        let Some(spec_set) = program.ghost_vars.get(&spec_fid) else {
            continue;
        };
        let realized = program
            .ghost_vars
            .get(&impl_fid)
            .cloned()
            .unwrap_or_default();
        for (k, v) in spec_set.clone() {
            if !matches!(k, Type::Struct { .. }) {
                continue;
            }
            if realized.contains(&(k.clone(), v.clone())) {
                continue;
            }
            if planned
                .iter()
                .any(|(f, pk, pv)| *f == impl_fid && *pk == k && *pv == v)
            {
                continue;
            }
            planned.push((impl_fid, k, v));
        }
    }
    for (impl_fid, k, v) in &planned {
        let entry = program.ghost_vars.entry(*impl_fid).or_default();
        if !entry.contains(&(k.clone(), v.clone())) {
            entry.push((k.clone(), v.clone()));
        }
        sort_ghost_set(entry, tags);
    }
    planned
}

/// Materialise the [`plan_opaque_ghost_outputs`] plan. Runs AFTER
/// `augment_signatures` / `augment_call_sites` so the impl's signature
/// already carries every ghost slot: the opaque symbol takes the FULL
/// augmented param list (originals + world + ghost inputs -- the ghost
/// inputs matter for relational publishes like `ghost' == ghost + x`) and
/// returns `V`. The impl's entry gains
/// `let __ghost_<sid(K)> := <impl>__ghost_out_<sid(K)>(params...)`,
/// shadowing the passthrough param; SSA later versions the rebind and the
/// existing tail augmentation returns the rebound value. The renderer
/// emits each recorded native as a generated Lean `opaque` declaration in
/// the impl's module.
fn materialize_opaque_ghost_outputs(
    program: &mut Program,
    plan: Vec<(FunId, Type, Type)>,
    tags: &StructTags,
) {
    use crate::ir::natives::NativeDecl;
    for (impl_fid, k, v) in plan {
        let func = program
            .functions
            .get(&impl_fid)
            .expect("opaque ghost plan targets a translated impl");
        // Stub bodies render as sorry -- nothing to rebind or constrain.
        let is_stub =
            func.body.stmts.is_empty() && matches!(&func.body.tail, BlockTail::Value(Expr::Unit));
        if is_stub {
            continue;
        }
        // NAME tag, not `StructId`: this declaration name is rendered
        // verbatim into the generated Lean, so a positional id here
        // reintroduced the rename hazard `render::struct_idx` removes.
        let tag = ghost_marker_tag(&k, tags);
        let name = format!("{}__ghost_out_{}", func.name, tag);
        // Native callees receive VALUE form regardless of the IR
        // signature (the renderer unwraps Mutation args with `.val` --
        // see `callee_expects_mut` in `render/expr/call.rs`), so the
        // opaque's params peel `MutableRef` to the inner value type.
        let params: Vec<Param> = func
            .signature
            .params
            .iter()
            .map(|p| {
                let ty = match &p.ty {
                    Type::MutableRef { inner, .. } => (**inner).clone(),
                    other => other.clone(),
                };
                Param {
                    name: p.name.clone(),
                    var: p.var.clone(),
                    ty,
                }
            })
            .collect();
        let signature = Signature {
            type_params: func.signature.type_params.clone(),
            params,
            return_type: v.clone(),
        };
        let type_args: Vec<Type> = (0..signature.type_params.len())
            .map(|i| Type::TypeParam(i as u16))
            .collect();
        let args: Vec<Expr> = signature
            .params
            .iter()
            .map(|p| Expr::Var(p.var.clone()))
            .collect();
        let module = func.module;
        let opaque_fid = program.next_function_id();
        program.natives.decls.insert(
            opaque_fid,
            NativeDecl {
                module,
                name,
                signature,
                effects: crate::ir::Effects::PURE,
                explicit_pure: true,
                is_framework: false,
                spec_target: None,
                user_native: None,
            },
        );
        let rebind = Stmt::Let {
            pattern: vec![Some(ghost_varid(&k, tags))],
            value: Expr::Call {
                fun: opaque_fid,
                type_args,
                args,
            },
        };
        let func = program
            .functions
            .get_mut(&impl_fid)
            .expect("impl fid just read");
        func.body.stmts.insert(0, rebind);
        program
            .ghost_opaque_outputs
            .entry(impl_fid)
            .or_default()
            .push((k, v, opaque_fid));
    }
}

/// Callee->caller fixpoint: a function threads every ghost var its callees
/// thread. `ghost_vars[caller] ∪= ghost_vars[callee]` over the call graph
/// (incl native callees), to fixpoint. Generic callee ghosts are
/// instantiated at each call site using that call's `type_args`, so a
/// native ghost like `public_receive<T>` threads `Coin<X>` in a caller that
/// receives `Coin<X>`. Fixes spec-shadowed impls whose own analysis set was
/// zeroed by the upstream `reachable` guard (e.g. `transfer_coin` getting
/// the transfer ghosts via `public_transfer`).
fn ghost_vars_fixpoint(program: &mut Program, tags: &StructTags) {
    loop {
        let mut changed = false;
        let fids: Vec<FunId> = program.functions.keys().copied().collect();
        for fid in fids {
            let call_sites = collect_call_sites(&program.functions[&fid].body);
            let mut additions: Vec<(Type, Type)> = Vec::new();
            for (callee, type_args) in call_sites {
                if let Some(cset) = program.ghost_vars.get(&callee) {
                    for (k, v) in cset {
                        additions.push((
                            substitute_type_params(k, &type_args),
                            substitute_type_params(v, &type_args),
                        ));
                    }
                }
            }
            if additions.is_empty() {
                continue;
            }
            let entry = program.ghost_vars.entry(fid).or_default();
            for kv in additions {
                if !entry.contains(&kv) {
                    entry.push(kv);
                    changed = true;
                }
            }
            sort_ghost_set(entry, tags);
        }
        if !changed {
            break;
        }
    }
}

fn collect_call_sites(block: &Block) -> Vec<(FunId, Vec<Type>)> {
    struct CallSiteCollector {
        sites: Vec<(FunId, Vec<Type>)>,
    }

    impl Visitor for CallSiteCollector {
        fn visit_expr(&mut self, e: &Expr) {
            if let Expr::Call { fun, type_args, .. } = e {
                self.sites.push((*fun, type_args.clone()));
            }
            walk_expr_default(self, e);
        }
    }

    let mut collector = CallSiteCollector { sites: Vec::new() };
    collector.visit_block(block);
    collector.sites
}

/// Append the ghost value types `vs` as trailing return-tuple slots.
fn augment_return_type_with_ghosts(ret: Type, vs: &[Type]) -> Type {
    if vs.is_empty() {
        return ret;
    }
    match ret {
        Type::Tuple(mut items) => {
            items.extend(vs.iter().cloned());
            Type::Tuple(items)
        }
        Type::Unit => Type::Tuple(vs.to_vec()),
        other => {
            let mut items = vec![other];
            items.extend(vs.iter().cloned());
            Type::Tuple(items)
        }
    }
}

/// Transform B (ghost): per lifted function in `program.ghost_vars`,
/// append a typed `V` param + a trailing return slot per ghost var.
fn augment_signatures(program: &mut Program, tags: &StructTags) {
    let all: Vec<(FunId, Vec<(Type, Type)>)> = program
        .ghost_vars
        .iter()
        .map(|(fid, v)| (*fid, v.clone()))
        .collect();
    for (fid, vars) in all {
        if let Some(func) = program.functions.get_mut(&fid) {
            augment_one_signature(&mut func.signature, &vars, tags);
        } else if let Some(decl) = program.natives.decls.get_mut(&fid) {
            augment_one_signature(&mut decl.signature, &vars, tags);
        }
    }
}

/// Append the ghost params + return slots to one signature (lifted fn or
/// native). Idempotent.
fn augment_one_signature(sig: &mut Signature, vars: &[(Type, Type)], tags: &StructTags) {
    if let Some((k0, _)) = vars.first() {
        let v0 = ghost_varid(k0, tags);
        if sig.params.iter().any(|p| p.var == v0) {
            return;
        }
    }
    for (k, v) in vars {
        let var = ghost_varid(k, tags);
        sig.params.push(Param {
            name: var.as_ref().to_string(),
            var,
            ty: v.clone(),
        });
    }
    let vs: Vec<Type> = vars.iter().map(|(_, v)| v.clone()).collect();
    let ret = std::mem::replace(&mut sig.return_type, Type::Unit);
    sig.return_type = augment_return_type_with_ghosts(ret, &vs);
}

// ---- Transforms C + D (ghost): call-site threading ----

/// Per ghost callee: (total augmented return arity, the ghost var ids in
/// order). Read after `augment_signatures` so arity includes the ghost
/// slots.
fn ghost_call_info(program: &Program, tags: &StructTags) -> BTreeMap<FunId, (usize, Vec<VarId>)> {
    program
        .ghost_vars
        .iter()
        .filter_map(|(fid, vars)| {
            let ret = program
                .lookup_callee(*fid)
                .map(|callee| &callee.signature().return_type)?;
            let arity = match ret {
                Type::Tuple(items) => items.len(),
                Type::Unit => 0,
                _ => 1,
            };
            let vids: Vec<VarId> = vars.iter().map(|(k, _)| ghost_varid(k, tags)).collect();
            Some((*fid, (arity, vids)))
        })
        .collect()
}

/// Transform C+D (ghost): thread ghost vars into Calls to ghost callees
/// inside every ghost-threading caller's body.
fn augment_call_sites(program: &mut Program, tags: &StructTags) {
    let info = ghost_call_info(program, tags);
    let callers: Vec<FunId> = program.ghost_vars.keys().copied().collect();
    for fid in callers {
        if let Some(func) = program.functions.get_mut(&fid) {
            rewrite_block(&mut func.body, &info);
        }
    }
}

fn rewrite_block(block: &mut Block, info: &BTreeMap<FunId, (usize, Vec<VarId>)>) {
    let stmts = std::mem::take(&mut block.stmts);
    block.stmts = stmts.into_iter().map(|s| rewrite_stmt(s, info)).collect();
    rewrite_tail_subblocks(&mut block.tail, info);
}

fn rewrite_stmt(stmt: Stmt, info: &BTreeMap<FunId, (usize, Vec<VarId>)>) -> Stmt {
    match stmt {
        Stmt::Eval(Expr::Call {
            fun,
            type_args,
            args,
        }) if info.contains_key(&fun) => {
            let (arity, gvids) = info.get(&fun).unwrap();
            let n = gvids.len();
            let mut new_args = args;
            extend_args(&mut new_args, gvids);
            let head = arity.saturating_sub(n);
            let mut pattern: Vec<Option<VarId>> = (0..head).map(|_| None).collect();
            for v in gvids {
                pattern.push(Some(v.clone()));
            }
            Stmt::Let {
                pattern,
                value: Expr::Call {
                    fun,
                    type_args,
                    args: new_args,
                },
            }
        }
        Stmt::Let {
            pattern,
            value:
                Expr::Call {
                    fun,
                    type_args,
                    args,
                },
        } if info.contains_key(&fun) => {
            let (arity, gvids) = info.get(&fun).unwrap();
            let n = gvids.len();
            if args_already_ghost_threaded(&args, gvids) {
                return Stmt::Let {
                    pattern,
                    value: Expr::Call {
                        fun,
                        type_args,
                        args,
                    },
                };
            }
            let mut new_args = args;
            extend_args(&mut new_args, gvids);
            let mut new_pattern = pattern;
            let head = arity.saturating_sub(n);
            while new_pattern.len() < head {
                new_pattern.push(None);
            }
            for v in gvids {
                new_pattern.push(Some(v.clone()));
            }
            Stmt::Let {
                pattern: new_pattern,
                value: Expr::Call {
                    fun,
                    type_args,
                    args: new_args,
                },
            }
        }
        Stmt::Eval(e) => Stmt::Eval(rewrite_expr_subblocks(e, info)),
        Stmt::Let { pattern, value } => Stmt::Let {
            pattern,
            value: rewrite_expr_subblocks(value, info),
        },
    }
}

fn extend_args(args: &mut Vec<Expr>, gvids: &[VarId]) {
    for v in gvids {
        args.push(Expr::Var(v.clone()));
    }
}

fn args_already_ghost_threaded(args: &[Expr], gvids: &[VarId]) -> bool {
    if gvids.is_empty() || args.len() < gvids.len() {
        return false;
    }
    let tail = &args[args.len() - gvids.len()..];
    tail.iter()
        .zip(gvids)
        .all(|(a, v)| matches!(a, Expr::Var(av) if av == v))
}

/// Recurse into block-containing exprs (ghost calls live at Stmt
/// position, so only these need descent).
fn rewrite_expr_subblocks(expr: Expr, info: &BTreeMap<FunId, (usize, Vec<VarId>)>) -> Expr {
    match expr {
        Expr::If {
            cond,
            mut then_branch,
            mut else_branch,
        } => {
            rewrite_block(&mut then_branch, info);
            rewrite_block(&mut else_branch, info);
            Expr::If {
                cond,
                then_branch,
                else_branch,
            }
        }
        Expr::Match {
            struct_id,
            selector,
            cases,
        } => {
            let cases = cases
                .into_iter()
                .map(
                    |MatchArm {
                         variant,
                         bindings,
                         mut body,
                     }| {
                        rewrite_block(&mut body, info);
                        MatchArm {
                            variant,
                            bindings,
                            body,
                        }
                    },
                )
                .collect();
            Expr::Match {
                struct_id,
                selector,
                cases,
            }
        }
        Expr::While {
            mut header,
            cond,
            mut body,
            iter_locals,
            header_exit_locals,
            live_out,
        } => {
            rewrite_block(&mut header, info);
            rewrite_block(&mut body, info);
            Expr::While {
                header,
                cond,
                body,
                iter_locals,
                header_exit_locals,
                live_out,
            }
        }
        Expr::LabeledBlock {
            mut body,
            result_ty,
        } => {
            rewrite_block(&mut body, info);
            Expr::LabeledBlock { body, result_ty }
        }
        // Quantifier bodies are pure predicates; a ghost-threaded call
        // inside one would need value-projection hoisting (cf. the world
        // pass). Not expected in v1 -- left as a documented gap.
        other => other,
    }
}

fn rewrite_tail_subblocks(tail: &mut BlockTail, info: &BTreeMap<FunId, (usize, Vec<VarId>)>) {
    match tail {
        BlockTail::Value(e) => {
            let t = std::mem::replace(e, Expr::Unit);
            *e = rewrite_expr_subblocks(t, info);
        }
        BlockTail::Break { value, .. }
        | BlockTail::Continue { value, .. }
        | BlockTail::Return(value)
        | BlockTail::ReturnFromBlock { value, .. } => {
            let t = std::mem::replace(&mut **value, Expr::Unit);
            **value = rewrite_expr_subblocks(t, info);
        }
        BlockTail::Abort { code } => {
            let t = std::mem::replace(&mut **code, Expr::Unit);
            **code = rewrite_expr_subblocks(t, info);
        }
    }
}

// ---- Transform E (ghost): body-tail augmentation ----

/// Append the threaded ghost vars to every `Return` / fall-off tail of
/// each ghost-threading function (after the world slot the world pass
/// already added).
fn augment_body_tails(program: &mut Program, tags: &StructTags) {
    let all: Vec<(FunId, Vec<VarId>)> = program
        .ghost_vars
        .iter()
        .map(|(fid, vars)| {
            (
                *fid,
                vars.iter().map(|(k, _)| ghost_varid(k, tags)).collect(),
            )
        })
        .collect();
    for (fid, gvids) in all {
        if gvids.is_empty() {
            continue;
        }
        if let Some(func) = program.functions.get_mut(&fid) {
            // Skip stub bodies (`[], Value(Unit)`) -- renderer emits sorry.
            let is_stub = func.body.stmts.is_empty()
                && matches!(&func.body.tail, BlockTail::Value(Expr::Unit));
            if is_stub {
                continue;
            }
            tail_in_block(&mut func.body, &gvids, /* top_level= */ true);
        }
    }
}

fn tail_in_block(block: &mut Block, gvids: &[VarId], top_level: bool) {
    for stmt in block.stmts.iter_mut() {
        let v = match stmt {
            Stmt::Let { value, .. } => value,
            Stmt::Eval(e) => e,
        };
        tail_recurse_expr(v, gvids);
    }
    match &mut block.tail {
        BlockTail::Return(value) => {
            tail_recurse_expr(value, gvids);
            if !value_already_ghost_augmented(value, gvids) {
                let t = std::mem::replace(&mut **value, Expr::Unit);
                **value = append_ghosts_to_value(t, gvids);
            }
        }
        BlockTail::Value(e) if top_level => {
            tail_recurse_expr(e, gvids);
            if !value_already_ghost_augmented(e, gvids) {
                let t = std::mem::replace(e, Expr::Unit);
                *e = append_ghosts_to_value(t, gvids);
            }
        }
        BlockTail::Value(e) => tail_recurse_expr(e, gvids),
        BlockTail::Break { value, .. } | BlockTail::Continue { value, .. } => {
            tail_recurse_expr(value, gvids)
        }
        BlockTail::Abort { code } => tail_recurse_expr(code, gvids),
        BlockTail::ReturnFromBlock { value, .. } => tail_recurse_expr(value, gvids),
    }
}

fn tail_recurse_expr(expr: &mut Expr, gvids: &[VarId]) {
    match expr {
        Expr::If {
            cond,
            then_branch,
            else_branch,
        } => {
            tail_recurse_expr(cond, gvids);
            tail_in_block(then_branch, gvids, false);
            tail_in_block(else_branch, gvids, false);
        }
        Expr::Match {
            selector, cases, ..
        } => {
            tail_recurse_expr(selector, gvids);
            for MatchArm { body, .. } in cases.iter_mut() {
                tail_in_block(body, gvids, false);
            }
        }
        Expr::While {
            header, cond, body, ..
        } => {
            tail_in_block(header, gvids, false);
            tail_recurse_expr(cond, gvids);
            tail_in_block(body, gvids, false);
        }
        Expr::Quantifier { body, .. } => tail_in_block(body, gvids, false),
        Expr::LabeledBlock { body, .. } => tail_in_block(body, gvids, false),
        _ => {}
    }
}

/// Append the ghost vars as trailing tuple slots. `Unit` -> drop (a
/// unit return becomes just the threaded slots, matching the world tail
/// wrapping).
fn append_ghosts_to_value(value: Expr, gvids: &[VarId]) -> Expr {
    let mut items = match value {
        Expr::Tuple(items) => items,
        Expr::Unit => Vec::new(),
        other => vec![other],
    };
    for v in gvids {
        items.push(Expr::Var(v.clone()));
    }
    Expr::Tuple(items)
}

fn value_already_ghost_augmented(value: &Expr, gvids: &[VarId]) -> bool {
    if let Expr::Tuple(items) = value {
        if items.len() >= gvids.len() && !gvids.is_empty() {
            let tail = &items[items.len() - gvids.len()..];
            return tail
                .iter()
                .zip(gvids)
                .all(|(it, v)| matches!(it, Expr::Var(av) if av == v));
        }
    }
    false
}

// ---- Phase 2: op lowering ----
//
// A simple mechanical translation: after threading, rewrite each spec
// ghost op onto the threaded `__ghost_<struct_id(K)>` variable so the
// `.ensures` read/write the REAL threaded value instead of the `Ghost.*`
// render stubs. One fixed replacement per op, no dataflow tracking:
//
//   ghost::global<K,V>()  /  ghost::borrow_mut<K,V>()  -> __ghost_<sid(K)>     (read the value)
//   ghost::set<K,V>(e)                                 -> let __ghost_<sid(K)> := e
//   write_back(SpecGlobalRoot<K,V> <- c)               -> let __ghost_<sid(K)> := c
//
// Reads are wholesale `Call -> Var` substitutions wherever the walk finds
// them. Writes rebind the threaded var: `set` from its value arg, the
// `SpecGlobalRoot` writeback from its committed child temp. The
// intervening `*r := e` WriteRef of a `*borrow_mut() = e` write is left
// UNTOUCHED -- with `r` now the threaded var it renders through the
// existing `Mutation` machinery and the writeback rebind commits the
// result. We deliberately do NOT collapse it to a clean `__ghost := e`:
// the mechanical translation is the point. `declare_global(_mut)` /
// `havoc_global` never reach this stage (eliminated upstream), so they
// need no handling.
//
// Runs pre-SSA, so SSA versions the rebinds: a `global` read AFTER the
// impl call resolves to the native's written value, one before a write to
// the prior value.

/// Resolved ghost-op native `FunId`s. A ghost op is a `Call` whose `fun`
/// is one of these.
struct GhostOpFids {
    /// `global` / `borrow_mut` -- read the ghost's current value.
    read: Vec<FunId>,
    /// `set` -- the value arg becomes the new threaded value.
    set: Vec<FunId>,
}

impl GhostOpFids {
    fn is_empty(&self) -> bool {
        self.read.is_empty() && self.set.is_empty()
    }
}

fn resolve_ghost_op_fids(program: &Program) -> GhostOpFids {
    let f = |name: &str| program.native_id_by_name("Prover", "ghost", name);
    let mut read = Vec::new();
    for n in ["global", "borrow_mut"] {
        read.extend(f(n));
    }
    let set: Vec<FunId> = f("set").into_iter().collect();
    GhostOpFids { read, set }
}

/// Lower the spec ghost ops in every ghost-threading function onto the
/// threaded `__ghost_<sid(K)>` variables (see the section comment above).
fn lower_ghost_ops(program: &mut Program, tags: &StructTags) {
    let fids = resolve_ghost_op_fids(program);
    if fids.is_empty() {
        return;
    }
    let targets: Vec<FunId> = program
        .ghost_vars
        .keys()
        .copied()
        .filter(|f| program.functions.contains_key(f))
        .collect();
    for fid in targets {
        let func = program
            .functions
            .get_mut(&fid)
            .expect("ghost target is a function");
        let value_aliases = program
            .ghost_vars
            .get(&fid)
            .into_iter()
            .flatten()
            .map(|(k, _)| ghost_varid(k, tags))
            .collect();
        GhostOpLowering {
            fids: &fids,
            tags,
            value_aliases,
        }
        .visit_block_mut(&mut func.body);
    }
}

/// `set<K,V>(value)` / writeback -> rebind the threaded var (`K = type_args[0]`).
fn ghost_set_rebind(type_args: &[Type], mut args: Vec<Expr>, tags: &StructTags) -> Stmt {
    let k = type_args[0].clone();
    let value = if args.is_empty() {
        Expr::Unit
    } else {
        args.remove(0)
    };
    Stmt::Let {
        pattern: vec![Some(ghost_varid(&k, tags))],
        value,
    }
}

fn spec_global_writeback_rebind(type_args: &[Type], child: &VarId, tags: &StructTags) -> Stmt {
    let k = type_args[0].clone();
    Stmt::Let {
        pattern: vec![Some(ghost_varid(&k, tags))],
        value: Expr::Var(child.clone()),
    }
}

/// In-place op-lowering pass. Reads (`global`/`borrow_mut`) become the
/// threaded var via `visit_expr_mut` (wholesale replacement, any position);
/// writes (`set` / the `SpecGlobalRoot` writeback) become a rebind at the
/// statement level. The shared [`MutVisitor`] walk handles all nested-block
/// recursion.
struct GhostOpLowering<'a> {
    fids: &'a GhostOpFids,
    tags: &'a StructTags,
    value_aliases: BTreeSet<VarId>,
}

impl GhostOpLowering<'_> {
    fn lower_stmt(&mut self, stmt: Stmt) -> Stmt {
        match stmt {
            // set<K,V>(e) -> rebind __ghost_<sid(K)> := e.
            Stmt::Eval(Expr::Call {
                fun,
                type_args,
                args,
            })
            | Stmt::Let {
                value:
                    Expr::Call {
                        fun,
                        type_args,
                        args,
                    },
                ..
            } if self.fids.set.contains(&fun) => ghost_set_rebind(&type_args, args, self.tags),

            // write_back(SpecGlobalRoot<K,V> <- c) -> let __ghost_<sid(K)> := c.
            Stmt::Eval(Expr::WriteBack {
                node: BorrowNode::SpecGlobalRoot { type_args },
                child,
                ..
            })
            | Stmt::Let {
                value:
                    Expr::WriteBack {
                        node: BorrowNode::SpecGlobalRoot { type_args },
                        child,
                        ..
                    },
                ..
            } => spec_global_writeback_rebind(&type_args, &child, self.tags),

            // Default: recurse; `visit_expr_mut` replaces ghost reads in place.
            Stmt::Eval(mut e) => {
                self.visit_expr_mut(&mut e);
                Stmt::Eval(e)
            }
            Stmt::Let { pattern, mut value } => {
                self.visit_expr_mut(&mut value);
                self.record_value_aliases(&pattern, &value);
                Stmt::Let { pattern, value }
            }
        }
    }

    fn record_value_aliases(&mut self, pattern: &[Option<VarId>], value: &Expr) {
        if pattern.len() != 1 {
            return;
        }
        let Some(alias) = &pattern[0] else {
            return;
        };
        let Expr::Var(source) = value else {
            return;
        };
        if self.value_aliases.contains(source) {
            self.value_aliases.insert(alias.clone());
        }
    }
}

impl MutVisitor for GhostOpLowering<'_> {
    fn visit_block_mut(&mut self, b: &mut Block) {
        let aliases_at_entry = self.value_aliases.clone();
        let stmts = std::mem::take(&mut b.stmts);
        b.stmts = stmts.into_iter().map(|s| self.lower_stmt(s)).collect();
        self.visit_tail_mut(&mut b.tail);
        self.value_aliases = aliases_at_entry;
    }

    fn visit_expr_mut(&mut self, e: &mut Expr) {
        if let Expr::Call { fun, type_args, .. } = e {
            if self.fids.read.contains(fun) {
                let k = type_args[0].clone();
                *e = Expr::Var(ghost_varid(&k, self.tags));
                return;
            }
        }
        if let Expr::ReadRef(inner) = e {
            self.visit_expr_mut(inner);
            if let Expr::Var(v) = inner.as_ref() {
                if self.value_aliases.contains(v) {
                    *e = Expr::Var(v.clone());
                }
            }
            return;
        }
        walk_expr_mut_default(self, e);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::{BinOp, Const, Effects, Function, FunctionKind};

    fn empty_sig() -> Signature {
        Signature {
            type_params: Vec::new(),
            params: Vec::new(),
            return_type: Type::Unit,
        }
    }

    fn source_function(name: &str, body: Block) -> Function {
        Function {
            module: 0,
            name: name.to_string(),
            signature: empty_sig(),
            body,
            kind: FunctionKind::Source,
            effects: Effects::PURE,
            explicit_pure: false,
        }
    }

    fn vid(name: &str) -> VarId {
        VarId::from(name)
    }

    /// Register a datatype so `build_struct_tags` can name it. Ghost
    /// binders are derived from the datatype NAME, so a fixture that
    /// leaves `program.structs` empty has no name to derive from.
    fn register_struct(program: &mut Program, sid: crate::ir::StructId, name: &str) -> Type {
        program
            .modules
            .entry(0)
            .or_insert_with(|| crate::ir::Module {
                name: "m".to_string(),
                package_name: String::new(),
                address: String::new(),
                required_imports: Vec::new(),
                is_native: false,
            });
        program.structs.insert(
            sid,
            crate::ir::Struct {
                module_id: 0,
                name: name.to_string(),
                qualified_name: format!("m::{name}"),
                type_params: Vec::new(),
                fields: Vec::new(),
                variants: None,
                is_native: false,
            },
        );
        Type::Struct {
            struct_id: sid,
            type_args: Vec::new(),
        }
    }

    #[test]
    fn fixpoint_instantiates_generic_callee_ghost_at_call_site() {
        let callee = 10;
        let caller = 20;
        let marker = Type::Struct {
            struct_id: 7,
            type_args: Vec::new(),
        };
        let received_coin = Type::Struct {
            struct_id: 42,
            type_args: vec![Type::TypeParam(0)],
        };

        let mut program = Program::default();
        register_struct(&mut program, 7, "Marker");
        register_struct(&mut program, 42, "Coin");
        program
            .ghost_vars
            .insert(callee, vec![(marker.clone(), Type::TypeParam(0))]);
        program.functions.insert(
            caller,
            source_function(
                "caller",
                Block {
                    stmts: vec![Stmt::Eval(Expr::Call {
                        fun: callee,
                        type_args: vec![received_coin.clone()],
                        args: Vec::new(),
                    })],
                    tail: BlockTail::Value(Expr::Unit),
                },
            ),
        );

        let tags = build_struct_tags(&program);
        ghost_vars_fixpoint(&mut program, &tags);

        assert_eq!(
            program.ghost_vars.get(&caller),
            Some(&vec![(marker, received_coin)])
        );
    }

    #[test]
    fn trusted_unrealized_published_ghost_gets_opaque_output() {
        let spec_fid = 1;
        let impl_fid = 2;
        let marker = Type::Struct {
            struct_id: 9,
            type_args: Vec::new(),
        };

        let mut program = Program::default();
        register_struct(&mut program, 9, "Marker");
        program
            .trusted_spec_to_impl
            .insert(spec_fid, (impl_fid, crate::ir::TrustReason::NonProve));
        program
            .ghost_vars
            .insert(spec_fid, vec![(marker.clone(), Type::Bool)]);
        program.functions.insert(
            spec_fid,
            source_function(
                "impl_spec",
                Block {
                    stmts: vec![Stmt::Eval(Expr::Call {
                        fun: impl_fid,
                        type_args: Vec::new(),
                        args: Vec::new(),
                    })],
                    tail: BlockTail::Value(Expr::Unit),
                },
            ),
        );
        program.functions.insert(
            impl_fid,
            source_function(
                "impl",
                Block {
                    stmts: Vec::new(),
                    tail: BlockTail::Value(Expr::Const(Const::Bool(true))),
                },
            ),
        );

        let tags = build_struct_tags(&program);
        run(&mut program);

        let outputs = program
            .ghost_opaque_outputs
            .get(&impl_fid)
            .expect("impl gets an opaque ghost output");
        assert_eq!(outputs.len(), 1);
        let (k, v, opaque_fid) = &outputs[0];
        assert_eq!(k, &marker);
        assert_eq!(v, &Type::Bool);
        let decl = &program.natives.decls[opaque_fid];
        assert_eq!(decl.name, "impl__ghost_out_m__Marker");
        assert_eq!(decl.signature.return_type, Type::Bool);
        // The impl threads the ghost and its entry rebinds it to the
        // opaque call (shadowing the passthrough param).
        assert_eq!(
            program.ghost_vars.get(&impl_fid),
            Some(&vec![(marker.clone(), Type::Bool)])
        );
        let impl_fn = &program.functions[&impl_fid];
        match &impl_fn.body.stmts[0] {
            Stmt::Let { pattern, value } => {
                assert_eq!(pattern, &vec![Some(ghost_varid(&marker, &tags))]);
                assert!(
                    matches!(value, Expr::Call { fun, .. } if fun == opaque_fid),
                    "entry rebind must call the opaque, got {value:?}"
                );
            }
            other => panic!("expected entry rebind, got {other:?}"),
        }
        // Signature threads the ghost param.
        assert!(impl_fn
            .signature
            .params
            .iter()
            .any(|p| p.var == ghost_varid(&marker, &tags)));
    }

    #[test]
    fn realized_ghost_is_not_opacified() {
        let spec_fid = 1;
        let impl_fid = 2;
        let marker = Type::Struct {
            struct_id: 9,
            type_args: Vec::new(),
        };

        let mut program = Program::default();
        register_struct(&mut program, 9, "Marker");
        program
            .trusted_spec_to_impl
            .insert(spec_fid, (impl_fid, crate::ir::TrustReason::NonProve));
        program
            .ghost_vars
            .insert(spec_fid, vec![(marker.clone(), Type::Bool)]);
        // The impl already realises the ghost (e.g. via a seeded
        // writing native in its body).
        program
            .ghost_vars
            .insert(impl_fid, vec![(marker.clone(), Type::Bool)]);
        program.functions.insert(
            spec_fid,
            source_function(
                "impl_spec",
                Block {
                    stmts: vec![Stmt::Eval(Expr::Call {
                        fun: impl_fid,
                        type_args: Vec::new(),
                        args: Vec::new(),
                    })],
                    tail: BlockTail::Value(Expr::Unit),
                },
            ),
        );
        program.functions.insert(
            impl_fid,
            source_function(
                "impl",
                Block {
                    stmts: Vec::new(),
                    tail: BlockTail::Value(Expr::Const(Const::Bool(true))),
                },
            ),
        );

        run(&mut program);

        assert!(program.ghost_opaque_outputs.is_empty());
        let impl_fn = &program.functions[&impl_fid];
        assert!(
            impl_fn.body.stmts.is_empty(),
            "no entry rebind for a realised ghost"
        );
    }

    #[test]
    fn lowering_strips_stale_readref_from_ghost_read_alias() {
        let read_fun = 77;
        let marker = Type::Struct {
            struct_id: 7,
            type_args: Vec::new(),
        };
        let tmp = vid("$t4");
        let result = vid("$t6");

        let mut block = Block {
            stmts: vec![
                Stmt::Let {
                    pattern: vec![Some(tmp.clone())],
                    value: Expr::Call {
                        fun: read_fun,
                        type_args: vec![marker.clone(), Type::Bool],
                        args: Vec::new(),
                    },
                },
                Stmt::Let {
                    pattern: vec![Some(result)],
                    value: Expr::BinOp {
                        op: BinOp::Eq,
                        lhs: Box::new(Expr::ReadRef(Box::new(Expr::Var(tmp.clone())))),
                        rhs: Box::new(Expr::Const(Const::Bool(true))),
                    },
                },
            ],
            tail: BlockTail::Value(Expr::ReadRef(Box::new(Expr::Call {
                fun: read_fun,
                type_args: vec![marker.clone(), Type::Bool],
                args: Vec::new(),
            }))),
        };
        let fids = GhostOpFids {
            read: vec![read_fun],
            set: Vec::new(),
        };
        let mut program = Program::default();
        register_struct(&mut program, 7, "Marker");
        let tags = build_struct_tags(&program);
        let ghost_var = ghost_varid(&marker, &tags);
        let mut lowering = GhostOpLowering {
            fids: &fids,
            tags: &tags,
            value_aliases: [ghost_var.clone()].into_iter().collect(),
        };

        lowering.visit_block_mut(&mut block);

        match &block.stmts[0] {
            Stmt::Let { value, .. } => assert_eq!(value, &Expr::Var(ghost_var.clone())),
            other => panic!("expected let, got {other:?}"),
        }
        match &block.stmts[1] {
            Stmt::Let {
                value: Expr::BinOp { lhs, .. },
                ..
            } => assert_eq!(lhs.as_ref(), &Expr::Var(tmp)),
            other => panic!("expected binop let, got {other:?}"),
        }
        assert_eq!(block.tail, BlockTail::Value(Expr::Var(ghost_var)));
    }

    /// What this pass emits for `*ghost::borrow_mut<K, V>() = e` must
    /// TYPE-CHECK, because every later stage walks the body with
    /// [`crate::ir::analysis::type_of`] (the post-SSA operand
    /// normalization walk is the first). Lowering rewrites the borrow to
    /// the threaded ghost var and deliberately leaves the `*r := e` in
    /// place, so the WriteRef operand carries the ghost's VALUE type --
    /// a rule requiring a `MutableRef` operand rejects the whole
    /// function. This pins the composition, not one body's spelling.
    #[test]
    fn lowered_ghost_write_type_checks() {
        let read_fun = 77;
        let marker = Type::Struct {
            struct_id: 7,
            type_args: Vec::new(),
        };
        let value = vid("$t13");
        let borrow = vid("$t14");
        let written = vid("$t15");

        let mut block = Block {
            stmts: vec![
                Stmt::Let {
                    pattern: vec![Some(value.clone())],
                    value: Expr::Const(Const::Bool(false)),
                },
                // `ghost::borrow_mut<Marker, Bool>()` -- typed `&mut Bool`
                // here, rewritten to the threaded ghost var by lowering.
                Stmt::Let {
                    pattern: vec![Some(borrow.clone())],
                    value: Expr::Call {
                        fun: read_fun,
                        type_args: vec![marker.clone(), Type::Bool],
                        args: Vec::new(),
                    },
                },
                Stmt::Let {
                    pattern: vec![Some(written.clone())],
                    value: Expr::WriteRef {
                        reference: Box::new(Expr::Var(borrow)),
                        value: Box::new(Expr::Var(value)),
                    },
                },
                Stmt::Eval(Expr::WriteBack {
                    node: BorrowNode::SpecGlobalRoot {
                        type_args: vec![marker.clone(), Type::Bool],
                    },
                    edge: crate::ir::BorrowEdge::Direct,
                    child: written,
                    world: None,
                }),
            ],
            tail: BlockTail::Value(Expr::Unit),
        };
        let fids = GhostOpFids {
            read: vec![read_fun],
            set: Vec::new(),
        };
        let mut program = Program::default();
        register_struct(&mut program, 7, "Marker");
        let tags = build_struct_tags(&program);
        let ghost_var = ghost_varid(&marker, &tags);
        GhostOpLowering {
            fids: &fids,
            tags: &tags,
            value_aliases: [ghost_var.clone()].into_iter().collect(),
        }
        .visit_block_mut(&mut block);

        let scope = [(ghost_var.clone(), Type::Bool)].into_iter().collect();
        assert_eq!(
            crate::ir::analysis::type_of::block_value_type(&block, &scope, &program),
            Ok(Type::Unit)
        );
        // The rebind is what commits the write; without it the lowered
        // body would type-check while dropping the ghost update.
        assert_eq!(
            block.stmts.last(),
            Some(&Stmt::Let {
                pattern: vec![Some(ghost_var)],
                value: Expr::Var(vid("$t15")),
            })
        );
    }
}
