//! Stage 12 -- proof-obligation synthesis.
//!
//! Runs after the late transformation steps, once every
//! companion (`.aborts` / `.requires` / `.asserts` / `.ensures`) is in
//! its final signature shape. Purely additive: for each `#[spec]`
//! wrapper paired with a translated or native impl (via `Program::spec_to_impl`),
//! it emits up to two `FunctionKind::Theorem` proof obligations:
//!
//! - `<impl>_correct`        : `requires -> asserts -> ensures(impl args)`
//! - `<impl>_asserts_correct` : `requires -> (isAborted(impl.aborts args) <-> not asserts)`
//!
//! TARGETLESS prove-specs (`Program::targetless_prove_specs`:
//! `#[spec(prove)]` with no `target=`) are standalone lemmas with no impl
//! to pair with. They get the SAME `_correct` statement with the WRAPPER
//! in the impl slot -- `requires -> (asserts ->) ensures(spec args)` --
//! because that shape references only the spec's own companions; the impl
//! side of a paired obligation drives dispatch and the `target` metadata,
//! never the statement. They get NO `_asserts_correct`: that obligation is
//! an abort-faithfulness claim between an impl and its spec, and with no
//! impl there is nothing to be faithful to. Before this, six sui-system
//! prove-specs -- including the security-relevant frozen-deactivation-rate
//! property -- emitted nothing at all, under a `0 missing` header.
//!
//! WHAT BOOGIE PROVES FOR ONE (and so what `_correct` must say). Upstream
//! calls these SCENARIO SPECS (`PackageTargets::scenario_specs`, the
//! `check_spec_scope` arm with neither a `target=` nor a name-derived
//! implicit target). `translate_spec` verifies each in exactly ONE
//! `AssertsMode`, chosen by `ignore_abort`, and the two modes differ in
//! precisely one way -- what an abort site becomes:
//!
//! - WITHOUT `ignore_abort`: `AssertsMode::Check`. Every `AbortAction::Check`
//!   site (any `can_abort()` op -- `as u64` narrowing included -- and any
//!   call not proven total) emits `assert !$abort_flag`. Boogie therefore
//!   proves TOTALITY *and* the postcondition. The unguarded
//!   `requires -> ensures` rendered here is sound against that: it evaluates
//!   the postcondition in the TOTAL semantics, which coincides with Move's
//!   wherever no abort occurs -- and Boogie has proved none does.
//! - WITH `ignore_abort`: `AssertsMode::Assume`. The same sites emit
//!   `assume !$abort_flag`, so Boogie proves the postcondition ONLY on the
//!   no-abort path and proves NOTHING about aborts. An unguarded rendering
//!   is then strictly stronger than the discharged claim, and provably
//!   FALSE where the total semantics diverges from Move's: `as u64` in
//!   `BoundedNat.convert` wraps (`% 2^64`) exactly where Move aborts, so a
//!   quotient of `2^64` reads as `0` and an inequality flips. Four momentum
//!   obligations were refuted at concrete witnesses that way. The
//!   `not isAborted(wrapper.aborts args)` guard below -- the same guard a
//!   PAIRED `ignore_abort` wrapper already gets, over the wrapper's own
//!   abort face instead of an impl's -- restores the Boogie statement.
//!
//! NOT COVERED, and named rather than papered over: the totality half of
//! the non-`ignore_abort` case has no Lean face. It is a real Boogie check
//! with no obligation here. Synthesizing it would ADD one obligation per
//! such spec (31 across the client fleet when this was written) rather than
//! correct any statement, so it is a separate change with its own
//! re-baseline.
//!
//! TRUSTED pairs (`Program::trusted_spec_to_impl`: `#[spec(target=...)]`
//! without `prove` or with `skip`, plus `run_on="boogie"` specs) get the
//! SAME statements but as `FunctionKind::Axiom` -- assumed, rendered as
//! a Lean `axiom`, never seeded into `<Mod>_Proofs.lean`. Their impl
//! side may be a NATIVE decl: the impl call and its Bool-valued native
//! `.aborts` companion (vs the AbortResult-valued translated shape)
//! both resolve through `lookup_callee` / `spec_target`.
//!
//! `_asserts_correct` is emitted for any PAIRED impl with a `.aborts`
//! companion unless the wrapper's spec has `ignore_abort`; when the wrapper
//! has no `.asserts` (precondition `true`) the RHS is `false`, so the
//! obligation is the totality claim "never aborts". For `ignore_abort`
//! wrappers, `<impl>_correct` is guarded by `not isAborted(<abort face> args)`
//! so the postcondition is checked only on non-aborting paths -- the abort
//! face being the impl's for a paired wrapper and the wrapper's OWN for a
//! targetless one, which is the only one that exists there.
//!
//! The statements are Bool-valued `Expr` trees over the wrapper's spec
//! companions, the impl's `.aborts`, and the three logical-connective
//! natives (`Connective::{Imp,Iff,Neg}`, registered here on demand).
//! `Prop` never enters the IR -- the renderer coerces Bool to Prop at
//! render time. `isAborted` is a `Match` on the `AbortResult` enum.
//!
//! WORLD-WELLFORMEDNESS INJECTION. Every obligation whose impl
//! transitively touches bag-valued dynamic-field storage (a `store_bag_*`
//! World native -- see [`needs_world_wf`]) gets the framework predicate
//! `Dynamic_field.world_wf world` prepended as an extra hypothesis
//! (`world_wf world -> <rest>`), threaded on whichever world param the
//! obligation already quantifies. Bag reads/writes are only sound when
//! every parked bag has unique packed keys; `world_wf` carries that
//! precondition into the proof so clients never write it by hand. The
//! `@[simp]` op-preservation lemmas (`world_wf_*` in
//! `lemmas/natives/Sui/Dynamic_fieldNatives.lean`) discharge it across
//! impure callee bodies -- which obligation proofs UNFOLD -- so NO
//! per-function postcondition (`world_wf world_out`) is conjoined into the
//! goal. Prove obligations only: trusted axioms and world-asymmetric /
//! native cases (impl not in [`needs_world_wf`], or no world param) are
//! left untouched.
//!
//! The renderer emits each obligation twice: in the module file as a
//! named proposition `def NAME (params) : Prop := <statement>`, and in
//! a durable sibling `<Mod>_Proofs.lean` as the module-qualified theorem
//! `<pkg>.<mod>_Proofs.NAME`, exported under its short name for compatibility
//! with sibling proof imports. See `render/function.rs` (`is_theorem` /
//! `as_proof_stub`) and `render/mod.rs` (the `<Mod>_Proofs.lean` seeding).
//!
//! See `plans/lean-pipeline/theorem-emission.md` (design) and
//! `theorem-emission-progress.md` (build log + decisions).

use crate::ir::connectives::Connective;
use crate::ir::expr::{Block, BlockTail, Expr, MatchArm};
use crate::ir::function::{Effects, Function, FunctionKind, Param, Signature};
use crate::ir::ty::{Const, Type};
use crate::ir::{FunId, ModId, Program, StructId, VarId};
use crate::stage_07_dejumps::option_aborts::{
    ensure_aborts_types, OPTION_NONE_TAG, OPTION_SOME_TAG,
};

/// Synthesize proof obligations into `program`. Reads `spec_to_impl`
/// (prove pairs -> `FunctionKind::Theorem`) and `trusted_spec_to_impl`
/// (trusted pairs -> `FunctionKind::Axiom`, same statement shape but
/// ASSUMED -- rendered as a Lean `axiom`, never seeded into
/// `<Mod>_Proofs.lean`) and the spec companions; appends the
/// synthesized functions.
/// One obligation-producing wrapper. `impl_fid` is the function the
/// statement constrains: a translated or native impl for a paired spec,
/// and the WRAPPER ITSELF when `targetless` (a `#[spec(prove)]` lemma
/// with no `target=`).
struct Pairing {
    spec_fid: FunId,
    impl_fid: FunId,
    trust: Option<crate::ir::TrustReason>,
    targetless: bool,
}

pub fn run(program: &mut Program) {
    // Pairs to process, tagged with `Some(TrustReason)` when trusted.
    // Both prove and trusted pairs may target a native. The statement is
    // built from the translated WRAPPER's companions plus calls to the native
    // declaration, so a native target still has a real specification theorem
    // to prove. Either way the wrapper itself must be translated -- its
    // companions carry the statement.
    let mut pairs: Vec<Pairing> = program
        .spec_to_impl
        .iter()
        .map(|(s, i)| Pairing {
            spec_fid: *s,
            impl_fid: *i,
            trust: None,
            targetless: false,
        })
        .filter(|p| {
            program.functions.contains_key(&p.spec_fid)
                && program.lookup_callee(p.impl_fid).is_some()
        })
        .collect();
    // Standalone lemmas: `#[spec(prove)]` with no `target=`. The
    // `_correct` statement references only the wrapper's own companions
    // (`requires -> (asserts ->) ensures(spec args)`) -- the impl side of
    // a paired obligation drives DISPATCH and the `target` metadata, not
    // the statement -- so the same shape is well-formed with the wrapper
    // itself in the target slot. No `_asserts_correct`: that obligation
    // is an abort-FAITHFULNESS claim between an impl and its spec, and
    // here there is no impl to be faithful to.
    for &spec_fid in &program.targetless_prove_specs {
        if !program.functions.contains_key(&spec_fid) {
            eprintln!(
                "new-pipeline: targetless prove spec fid {} has no translated wrapper -- \
                 NO OBLIGATION EMITTED",
                spec_fid
            );
            continue;
        }
        pairs.push(Pairing {
            spec_fid,
            impl_fid: spec_fid,
            trust: None,
            targetless: true,
        });
    }
    for (&spec_fid, &(impl_fid, reason)) in &program.trusted_spec_to_impl {
        if !program.functions.contains_key(&spec_fid) {
            eprintln!(
                "new-pipeline: trusted spec fid {} has no translated wrapper -- no axiom emitted",
                spec_fid
            );
            continue;
        }
        if program.lookup_callee(impl_fid).is_none() {
            eprintln!(
                "new-pipeline: trusted spec fid {} targets unknown fid {} -- no axiom emitted",
                spec_fid, impl_fid
            );
            continue;
        }
        pairs.push(Pairing {
            spec_fid,
            impl_fid,
            trust: Some(reason),
            targetless: false,
        });
    }
    if pairs.is_empty() {
        return;
    }

    // Register the connective natives once (idempotent). Module is
    // arbitrary -- the renderer maps these calls to Lean operators by
    // name, never emitting them as `Module.imp`.
    let module = program.first_module_id();
    let imp = register_connective(program, Connective::Imp, module);
    let iff = register_connective(program, Connective::Iff, module);
    let neg = register_connective(program, Connective::Neg, module);
    let abort_struct = ensure_aborts_types(program).option;

    // World-wellformedness gate: the set of translated functions that
    // transitively touch bag storage, and (only when that set is
    // non-empty) the `Dynamic_field.world_wf` predicate native the
    // injection references. Registered in the `Sui::dynamic_field`
    // module so it renders as `_root_.Dynamic_field.world_wf` -- the
    // same namespace as the `store_bag_*` ops it constrains.
    let needs_wf = needs_world_wf(program);
    let world_wf_fid = if needs_wf.is_empty() {
        None
    } else {
        Some(register_world_wf(program))
    };

    // Theorem FunIds start above everything (incl. the just-registered
    // connectives and `world_wf`); each new theorem bumps the local
    // counter.
    let mut next = program.next_function_id();
    let mut new_fns: Vec<(FunId, Function)> = Vec::new();

    // Pre-pass: count how many pairs would emit each obligation name
    // (keyed by the wrapper module + the impl's bare name). A count > 1 means
    // a collision that the per-pair logic below disambiguates.
    let mut ob_name_counts: std::collections::HashMap<(ModId, String), usize> =
        std::collections::HashMap::new();
    for p in &pairs {
        let key = (
            program.functions[&p.spec_fid].module,
            impl_ref(program, p.impl_fid).name().to_string(),
        );
        *ob_name_counts.entry(key).or_insert(0) += 1;
    }

    for Pairing {
        spec_fid,
        impl_fid,
        trust,
        targetless,
    } in pairs
    {
        let is_trusted = trust.is_some();
        // Extract owned data, dropping the borrows before the lookups.
        let (wrapper_name, wrapper_module) = {
            let w = &program.functions[&spec_fid];
            (w.name.clone(), w.module)
        };
        // The impl side may be a native declaration; resolve through
        // `lookup_callee` so both translated and native shapes serve the same role.
        let (impl_name, impl_module, params, type_params) = {
            let i = impl_ref(program, impl_fid);
            (
                i.name().to_string(),
                i.module(),
                i.signature().params.clone(),
                i.signature().type_params.clone(),
            )
        };

        // Obligation defs (`<impl>_correct` / `<impl>_asserts_correct`) live in
        // the wrapper's module. Two distinct impls that share a short name
        // (e.g. `interest_rate_scale` in two modules) both spec'd into one spec
        // module collide on that name. ONLY on a real collision do we adopt the
        // wrapper's author-chosen disambiguation -- the spec author already
        // module-prefixes the colliding wrapper
        // (`interest_model_interest_rate_scale_spec`), so the obligation mirrors
        // it (`interest_model_interest_rate_scale_*`) while its bare sibling keeps
        // the plain impl name. Non-colliding obligations are never renamed, so
        // existing `_Proofs.lean` theorem names stay stable.
        // A targetless lemma has no impl name to borrow, so the base is
        // the wrapper's own with `_spec` dropped -- ONE rule, no
        // collision fallback, so `prove.rs`'s roster mirror of this
        // naming stays a single line. If two obligations in a module ever
        // did land on the same name, `obligations.toml` would carry a
        // duplicate `lean_decl` and the audit rejects that by name.
        let ob_base: String = if targetless {
            crate::ir::names::targetless_obligation_base(&wrapper_name).to_string()
        } else {
            let collides = ob_name_counts
                .get(&(wrapper_module, impl_name.clone()))
                .copied()
                .unwrap_or(0)
                > 1;
            let stripped = wrapper_name
                .strip_suffix("_spec")
                .unwrap_or(wrapper_name.as_str());
            if collides && stripped != impl_name {
                stripped.to_string()
            } else {
                impl_name.clone()
            }
        };

        let args: Vec<Expr> = params.iter().map(|p| Expr::Var(p.var.clone())).collect();
        let type_args: Vec<Type> = (0..type_params.len() as u16).map(Type::TypeParam).collect();

        // Companions: requires/asserts/ensures belong to the wrapper;
        // `.aborts` belongs to the impl. Looked up by (module, name).
        let requires = find_fn(
            program,
            wrapper_module,
            &crate::ir::names::requires_name(&wrapper_name),
        );
        let asserts = find_fn(
            program,
            wrapper_module,
            &crate::ir::names::asserts_name(&wrapper_name),
        );
        let ensures = find_fn(
            program,
            wrapper_module,
            &crate::ir::names::ensures_name(&wrapper_name),
        );
        // The impl's `.aborts`: a translated companion (AbortResult-
        // valued) or, for native impls, the synthetic native companion
        // registered at module lift (Bool-valued, back-referencing the
        // base via `spec_target`).
        // For a TARGETLESS lemma `impl_fid == spec_fid`, so this resolves
        // to the WRAPPER'S OWN `.aborts` -- which is exactly the face the
        // `ignore_abort` guard below needs, and the only one that exists.
        // It is still NOT used for `_asserts_correct` (see the gate on
        // that emission): abort-faithfulness is a claim between an impl
        // and its spec, and a targetless lemma has no impl.
        let impl_aborts_name = crate::ir::names::aborts_name(&impl_name);
        let aborts = find_fn(program, impl_module, &impl_aborts_name).or_else(|| {
            program
                .natives
                .decls
                .iter()
                .find(|(_, d)| d.spec_target == Some(impl_fid) && d.name == impl_aborts_name)
                .map(|(fid, _)| *fid)
        });
        let ignore_abort = program
            .spec_ignore_aborts
            .get(&spec_fid)
            .copied()
            .unwrap_or(false);
        if is_trusted && aborts.is_none() && !ignore_abort {
            eprintln!(
                "new-pipeline: trusted spec `{}`: target `{}` has no .aborts companion -- \
                 abort-faithfulness axiom skipped (postcondition axiom only)",
                wrapper_name, impl_name
            );
        }
        // An `ignore_abort` wrapper whose `.aborts` companion is missing
        // would silently render the UNGUARDED postcondition -- a strictly
        // stronger claim than the one Boogie discharges. Never observed on
        // the corpus; disclosed rather than assumed away.
        if ignore_abort && aborts.is_none() {
            eprintln!(
                "new-pipeline: `ignore_abort` spec `{}`: no `{}` companion -- \
                 `_correct` emitted WITHOUT its no-abort premise",
                wrapper_name, impl_aborts_name
            );
        }

        // Spec companions (`.requires`/`.asserts`/`.ensures`) are
        // world-threaded copies of the impl: their params are the impl's with
        // zero or more ambient `world` params inserted (the spec reads df-backed
        // state through a world-threaded helper the impl itself doesn't thread).
        // Align the spec WRAPPER's params against the impl's once to recover (a)
        // the call-arg list every spec companion takes -- impl args with the
        // ambient world dropped into each inserted slot, wherever it sits -- and
        // (b) the ambient world Param(s) the obligation must quantify. A
        // world-threaded impl shares its `world`, so nothing is inserted and the
        // obligation is unchanged. The impl's own `.aborts` is NOT a spec
        // companion (not world-threaded) -- it always keeps the plain `args`.
        let spec_params = program.functions[&spec_fid].signature.params.clone();
        let (threaded_args, ambient_worlds) =
            match align_world_threaded_args(&spec_params, &params, &args) {
                Some(pair) => pair,
                // Not the clean "impl + inserted worlds" shape -- don't thread;
                // companions get the plain impl args (pre-existing behavior).
                None => (args.clone(), Vec::new()),
            };

        let ob_kind = if let Some(reason) = trust {
            FunctionKind::Axiom {
                target: impl_fid,
                source: spec_fid,
                reason,
            }
        } else {
            FunctionKind::Theorem {
                target: impl_fid,
                source: spec_fid,
            }
        };
        // `isAborted` over the impl's `.aborts` result: translated
        // companions return `AbortResult` (match on it); native
        // companions are Bool-valued already ("does it abort?").
        let aborted = |aborts_fid: FunId| -> Expr {
            if let Some(decl) = program.natives.decls.get(&aborts_fid) {
                // A native companion keeps its lift-time signature: ghost
                // slots stage 4 appended to the BASE decl are not on the
                // companion (render-side ghost dispatch swaps the base
                // call to `<name>__ghost`; the aborts call stays plain --
                // e.g. `Object.new.aborts ctx world` next to
                // `Object.new__ghost ctx world ghost`). Ghost params are
                // strictly appended, so the companion's arg list is
                // exactly the prefix of the impl args at its own arity
                // (cetus `object::new` + `SpecObjectNewValue` ghost).
                let arity = decl.signature.params.len();
                call(aborts_fid, type_args.clone(), args[..arity].to_vec())
            } else {
                is_aborted_expr(
                    abort_struct,
                    call(aborts_fid, type_args.clone(), args.clone()),
                )
            }
        };
        let mk = |body: Expr, name: String, ob_params: Vec<Param>| Function {
            module: wrapper_module,
            name,
            signature: Signature {
                type_params: type_params.clone(),
                params: ob_params,
                return_type: Type::Bool,
            },
            body: Block {
                stmts: Vec::new(),
                tail: BlockTail::Value(body),
            },
            kind: ob_kind.clone(),
            effects: Effects::PURE,
            explicit_pure: false,
        };

        // Prepend `world_wf world` as the OUTERMOST hypothesis of a
        // bag-touching PROVE obligation: `world_wf world -> <goal>`. Gated
        // on the impl transitively reaching bag storage (`needs_wf`) and
        // the obligation already quantifying a world param (searched in the
        // final `ob_params` -- the world-threaded impl's trailing `world`
        // or an inserted ambient world). Trusted axioms and
        // worldless / world-asymmetric-non-bag cases are returned
        // unchanged. Applied AFTER every other hypothesis wrap so it sits
        // outermost.
        let inject_world_wf = |goal: Expr, ob_params: &[Param]| -> Expr {
            let Some(wf_fid) = world_wf_fid else {
                return goal;
            };
            if is_trusted || !needs_wf.contains(&impl_fid) {
                return goal;
            }
            match ob_params.iter().find(|p| {
                p.var
                    .starts_with(crate::stage_04_effects::common::WORLD_VAR)
            }) {
                Some(world) => call(
                    imp,
                    vec![],
                    vec![
                        call(wf_fid, vec![], vec![Expr::Var(world.var.clone())]),
                        goal,
                    ],
                ),
                None => goal,
            }
        };

        // f_asserts_correct: requires -> (isAborted(impl.aborts args) <-> not asserts).
        // Needs the impl's `.aborts`. A missing `.asserts` companion means
        // the precondition is implicitly `true`, so `not asserts` is `false`
        // and the obligation degenerates to `isAborted <-> false`, i.e. the
        // impl never aborts, guarded by `.requires` when the spec has one.
        // NOT emitted for a targetless lemma: this is an abort-FAITHFULNESS
        // claim between an impl and its spec, and there is no impl. Boogie
        // does check a `<>`-shaped totality claim on a NON-`ignore_abort`
        // scenario spec (`assert !$abort_flag` at every abort site under
        // `AssertsMode::Check`); that face is not synthesized here -- see
        // the module header.
        if let Some(aborts_fid) = aborts.filter(|_| !ignore_abort && !targetless) {
            // `impl.aborts` keeps the plain impl `args`; `.asserts` (a spec
            // companion) and `.requires` take the world-threaded args.
            let is_aborted = aborted(aborts_fid);
            let rhs = match asserts {
                Some(asserts_fid) => call(
                    neg,
                    vec![],
                    vec![call(asserts_fid, type_args.clone(), threaded_args.clone())],
                ),
                None => Expr::Const(Const::Bool(false)),
            };
            let mut body = call(iff, vec![], vec![is_aborted, rhs]);
            if let Some(requires_fid) = requires {
                body = call(
                    imp,
                    vec![],
                    vec![
                        call(requires_fid, type_args.clone(), threaded_args.clone()),
                        body,
                    ],
                );
            }
            let mut ob_params = params.clone();
            if asserts.is_some() || requires.is_some() {
                ob_params.extend(ambient_worlds.iter().cloned());
            }
            let body = inject_world_wf(body, &ob_params);
            new_fns.push((
                next,
                mk(
                    body,
                    crate::ir::names::asserts_correct_theorem_name(&ob_base),
                    ob_params,
                ),
            ));
            next += 1;
        }

        // f_correct: requires -> asserts -> ensures(args ++ [impl result]).
        // Only meaningful with a postcondition (ensures).
        if let Some(ensures_fid) = ensures {
            // The `.ensures` companion takes the world-threaded args plus a
            // trailing `result`. When the spec is world-asymmetric (ambient
            // worlds were inserted), the impl's own result lacks the world the
            // ensures expects re-tupled into its `result`, so feed the spec
            // WRAPPER applied to the SAME threaded args -- post spec-extraction
            // the wrapper's value IS the impl call re-tupled with the world,
            // which sidesteps a tuple-destructure the IR can't express in a
            // tail-only body. With no ambient world the wrapper and impl results
            // coincide; use the impl call directly so non-world obligations stay
            // byte-identical. `.requires` / `.asserts` take the threaded args
            // too. All share the single ambient world the obligation quantifies.
            //
            // Native-target pairs ALWAYS use the wrapper: a native impl with a
            // `&mut` param renders as a value call (`native _ctx.val`)
            // returning the plain value, while the wrapper (translated,
            // Mutation-threaded) returns the `Mutation`-retupled shape the
            // `.ensures` result slot expects (observed: SuiSpecs
            // `fresh_object_address_spec` -- `Address × TxContext` vs
            // `Address × Mutation TxContext`). Translated prove targets keep the
            // impl call so existing obligation text stays byte-identical.
            let impl_is_native = program.natives.decls.contains_key(&impl_fid);
            let result = if ambient_worlds.is_empty() && !is_trusted && !impl_is_native {
                call(impl_fid, type_args.clone(), args.clone())
            } else {
                call(spec_fid, type_args.clone(), threaded_args.clone())
            };
            let mut ens_args = threaded_args.clone();
            ens_args.push(result);
            let mut goal = call(ensures_fid, type_args.clone(), ens_args);
            if let Some(asserts_fid) = asserts {
                goal = call(
                    imp,
                    vec![],
                    vec![
                        call(asserts_fid, type_args.clone(), threaded_args.clone()),
                        goal,
                    ],
                );
            }
            if ignore_abort {
                if let Some(aborts_fid) = aborts {
                    let no_abort = call(neg, vec![], vec![aborted(aborts_fid)]);
                    goal = call(imp, vec![], vec![no_abort, goal]);
                }
            }
            if let Some(requires_fid) = requires {
                goal = call(
                    imp,
                    vec![],
                    vec![
                        call(requires_fid, type_args.clone(), threaded_args.clone()),
                        goal,
                    ],
                );
            }
            let mut ob_params = params.clone();
            ob_params.extend(ambient_worlds.iter().cloned());
            let goal = inject_world_wf(goal, &ob_params);
            new_fns.push((
                next,
                mk(
                    goal,
                    crate::ir::names::correct_theorem_name(&ob_base),
                    ob_params,
                ),
            ));
            next += 1;
        }
    }

    for (fid, f) in new_fns {
        program.functions.insert(fid, f);
    }
}

fn call(fun: FunId, type_args: Vec<Type>, args: Vec<Expr>) -> Expr {
    Expr::Call {
        fun,
        type_args,
        args,
    }
}

/// Align a spec companion's params against the impl's to build the companion's
/// call args and discover the extra params -- ambient `world`s and `__ghost_*`
/// ghost-globals -- the obligation must quantify.
///
/// Spec companions are the impl's params with zero or more ambient `world`
/// params inserted (the spec reads df-backed state through a world-threaded
/// helper the impl doesn't thread). Walk both in order: when the spec param and
/// the next impl param agree on world-ness they are the same param -- consume
/// the impl arg; otherwise the spec has an extra `world` the impl lacks -- emit
/// it as an ambient world (its own `Var`, which the obligation quantifies) and
/// DON'T advance the impl cursor. A world-threaded impl shares its own `world`
/// (both are worlds at that position), so nothing is inserted there.
///
/// `spec_params` is the wrapper's own param list (the companions share it, minus
/// the `.ensures` trailing `result`). Returns `None` -- meaning "not the clean
/// `impl + inserted worlds` shape, don't thread" -- if a spec param is neither a
/// shared impl param nor an inserted world, or if impl params are left
/// unconsumed; the caller then falls back to the plain impl args.
fn align_world_threaded_args(
    spec_params: &[Param],
    impl_params: &[Param],
    impl_args: &[Expr],
) -> Option<(Vec<Expr>, Vec<Param>)> {
    let is_world = |p: &Param| {
        p.var
            .starts_with(crate::stage_04_effects::common::WORLD_VAR)
    };
    // Ghost params (`__ghost_*`, appended by stage_04_ghost so the spec can
    // read havoc'd ghost-global state) behave exactly like ambient `world`s: a
    // companion may carry one the impl ALSO has (shared -- consume the impl
    // arg) or one the impl lacks (extra -- the obligation quantifies it and
    // threads it into every companion; the wrapper re-tuples it into
    // `.ensures`' trailing `result`, so the `ambient`-driven "use the wrapper
    // call as result" path below covers it too). Match a spec param to the impl
    // param at the cursor only when they are the SAME category; otherwise the
    // spec param is an extra world/ghost (quantify) or genuinely unexpected
    // (bail). Comparing world-ness alone (the old check) wrongly let a shared
    // ghost fall through to a `None` bail, dropping a sibling world.
    let is_ghost = |p: &Param| p.var.starts_with("__ghost");
    let category = |p: &Param| -> u8 {
        if is_world(p) {
            2
        } else if is_ghost(p) {
            1
        } else {
            0
        }
    };
    let mut threaded = Vec::with_capacity(spec_params.len());
    let mut ambient = Vec::new();
    let mut i = 0;
    for sp in spec_params {
        if i < impl_params.len() && category(&impl_params[i]) == category(sp) {
            threaded.push(impl_args[i].clone());
            i += 1;
        } else if is_world(sp) || is_ghost(sp) {
            threaded.push(Expr::Var(sp.var.clone()));
            ambient.push(sp.clone());
        } else {
            return None;
        }
    }
    if i != impl_params.len() {
        return None;
    }
    Some((threaded, ambient))
}

/// `isAborted(r)` for `r : AbortResult` -- a `Match` returning the Bool
/// `false` on `NoAbort`, `true` on `Aborted(_)`.
fn is_aborted_expr(abort_struct: StructId, aborts_call: Expr) -> Expr {
    let bool_block = |b: bool| Block {
        stmts: Vec::new(),
        tail: BlockTail::Value(Expr::Const(Const::Bool(b))),
    };
    Expr::Match {
        struct_id: abort_struct,
        selector: Box::new(aborts_call),
        cases: vec![
            MatchArm {
                variant: OPTION_NONE_TAG,
                bindings: vec![],
                body: Box::new(bool_block(false)),
            },
            MatchArm {
                variant: OPTION_SOME_TAG,
                bindings: vec![VarId::from("_abort_code")],
                body: Box::new(bool_block(true)),
            },
        ],
    }
}

fn find_fn(program: &Program, module: ModId, name: &str) -> Option<FunId> {
    program
        .functions
        .iter()
        .find(|(_, f)| f.module == module && f.name == name)
        .map(|(fid, _)| *fid)
}

/// Resolve a pair's impl fid -- a translated function or (for trusted
/// pairs) a native decl. Pair construction in `run` already verified
/// the fid resolves, so a miss here is a bug.
fn impl_ref(program: &Program, impl_fid: FunId) -> crate::ir::CalleeRef<'_> {
    program.lookup_callee(impl_fid).unwrap_or_else(|| {
        panic!(
            "stage 12: impl fid {} resolves to neither a translated function nor a native decl",
            impl_fid
        )
    })
}

fn register_connective(program: &mut Program, c: Connective, module: ModId) -> FunId {
    program.insert_synthetic_native(
        c.native_name(),
        c.signature(),
        crate::ir::SyntheticNativeOpts {
            module,
            effects: Effects::PURE,
            explicit_pure: true,
            spec_target: None,
        },
    )
}

/// The bag-valued dynamic-field storage ops (`store_bag_*` World
/// natives). A call reaching any of these evaluates against
/// `World.df_bag_entries` -- the slot `world_wf` constrains.
const STORE_BAG_OPS: [&str; 5] = [
    "store_bag_borrow",
    "store_bag_has",
    "store_bag_set",
    "store_bag_add",
    "store_bag_remove",
];

/// The reserved name of the world-wellformedness predicate native,
/// registered in the `Sui::dynamic_field` module (renders as
/// `_root_.Dynamic_field.world_wf`). Its Lean def lives in
/// `lemmas/natives/Sui/Dynamic_fieldNatives.lean` (returns `Prop`); the
/// renderer emits a call to it bare, without the Bool `= true` coercion.
pub(crate) const WORLD_WF_NAME: &str = "world_wf";

fn world_wf_signature() -> Signature {
    Signature {
        type_params: Vec::new(),
        params: vec![Param {
            name: crate::stage_04_effects::common::WORLD_VAR.to_string(),
            var: VarId::from(crate::stage_04_effects::common::WORLD_VAR),
            ty: Type::Unit,
        }],
        return_type: Type::Bool,
    }
}

/// Functions whose body transitively (through impure callees, whose
/// bodies obligation proofs UNFOLD) reaches a call to any `store_bag_*`
/// World native. Modeled on
/// [`crate::stage_04_effects::common::compute_needs_world`]: seed on the
/// direct `store_bag_*` callers, then propagate to callers -- including
/// callees inside `Quantifier` bodies (`collect_callees` walks them) --
/// to a fixpoint. Contains only translated functions; native decls are
/// never members (they are the seeds, not the reachers).
fn needs_world_wf(program: &Program) -> std::collections::BTreeSet<FunId> {
    use crate::stage_04_effects::common::collect_callees;
    use std::collections::BTreeSet;

    let bag_native_fids: BTreeSet<FunId> = program
        .natives
        .decls
        .iter()
        .filter(|(_, d)| STORE_BAG_OPS.contains(&d.name.as_str()))
        .map(|(id, _)| *id)
        .collect();

    // Seed: any function that directly calls a `store_bag_*` native.
    let mut needs: BTreeSet<FunId> = program
        .functions
        .iter()
        .filter(|(_, f)| {
            collect_callees(&f.body)
                .iter()
                .any(|c| bag_native_fids.contains(c))
        })
        .map(|(id, _)| *id)
        .collect();

    // Transitive closure over the call graph (callers of members).
    loop {
        let mut changed = false;
        for (fid, func) in &program.functions {
            if needs.contains(fid) {
                continue;
            }
            let reaches = collect_callees(&func.body)
                .iter()
                .any(|c| needs.contains(c));
            if reaches {
                needs.insert(*fid);
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
    needs
}

/// The `Sui::dynamic_field` module id, where the `store_bag_*` and
/// `world_wf` natives live (see `stage_02_ir_cfg::dynamic_fields`).
fn find_dynamic_field_module(program: &Program) -> Option<ModId> {
    program.module_id_by_name("Sui", "dynamic_field")
}

pub(crate) fn is_world_wf_native(program: &Program, fid: FunId) -> bool {
    let Some(decl) = program.natives.decls.get(&fid) else {
        return false;
    };
    find_dynamic_field_module(program) == Some(decl.module)
        && decl.name == WORLD_WF_NAME
        && decl.signature == world_wf_signature()
        && decl.effects == Effects::PURE
        && decl.explicit_pure
        && decl.is_framework
        && decl.spec_target.is_none()
        && decl.user_native.is_none()
}

/// Register the `world_wf` predicate native. Idempotent. Lives in the
/// `Sui::dynamic_field` module so it renders as
/// `_root_.Dynamic_field.world_wf` -- matching the Lean def's namespace.
/// The IR signature is `(world) -> Bool` (a single opaque world slot,
/// zero type params -- the Lean def's `{Ev Ob Df Bg}` are all inferred):
/// Bool keeps it a valid connective operand, and the renderer emits the
/// call bare (it is a `Prop` in Lean). A non-empty `needs_world_wf`
/// guarantees the module exists (its `store_bag_*` seeds are registered
/// there), so the lookup never falls back.
fn register_world_wf(program: &mut Program) -> FunId {
    let module = find_dynamic_field_module(program)
        .expect("world_wf injection requires the Sui::dynamic_field module");
    program.insert_synthetic_native(
        WORLD_WF_NAME,
        world_wf_signature(),
        crate::ir::SyntheticNativeOpts {
            module,
            effects: Effects::PURE,
            explicit_pure: true,
            spec_target: None,
        },
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::program::Module;
    use crate::ir::{SpecKind, VarId};
    use crate::stage_07_dejumps::option_aborts::{ensure_aborts_types, OPTION_QUALIFIED_NAME};

    const IMPL: FunId = 0;
    const WRAPPER: FunId = 1;
    const ABORTS: FunId = 2;
    const REQUIRES: FunId = 3;
    const ASSERTS: FunId = 4;
    const ENSURES: FunId = 5;

    fn module() -> Module {
        Module {
            name: "m".to_string(),
            package_name: "p".to_string(),
            address: String::new(),
            required_imports: Vec::new(),
            is_native: false,
        }
    }

    fn param(name: &str, ty: Type) -> Param {
        Param {
            name: name.to_string(),
            var: VarId::from(name),
            ty,
        }
    }

    fn sig(params: Vec<Param>, return_type: Type) -> Signature {
        Signature {
            type_params: Vec::new(),
            params,
            return_type,
        }
    }

    fn value(e: Expr) -> Block {
        Block {
            stmts: Vec::new(),
            tail: BlockTail::Value(e),
        }
    }

    fn func(name: &str, signature: Signature, body: Block, kind: FunctionKind) -> Function {
        Function {
            module: 0,
            name: name.to_string(),
            signature,
            body,
            kind,
            effects: Effects::PURE,
            explicit_pure: false,
        }
    }

    fn fixture(has_requires: bool, has_asserts: bool) -> Program {
        let mut program = Program::default();
        program.modules.insert(0, module());
        let abort_types = ensure_aborts_types(&mut program);
        let x = param("x", Type::Bool);

        program.functions.insert(
            IMPL,
            func(
                "foo",
                sig(vec![x.clone()], Type::Bool),
                value(Expr::Const(Const::Bool(true))),
                FunctionKind::Source,
            ),
        );
        program.functions.insert(
            WRAPPER,
            func(
                "foo_spec",
                sig(vec![x.clone()], Type::Bool),
                value(Expr::Const(Const::Bool(true))),
                FunctionKind::Source,
            ),
        );
        program.functions.insert(
            ABORTS,
            func(
                &crate::ir::names::aborts_name("foo"),
                sig(vec![x.clone()], abort_types.option_abort_code_type()),
                value(abort_types.make_none()),
                FunctionKind::Spec {
                    kind: SpecKind::Aborts,
                    target: IMPL,
                },
            ),
        );
        if has_requires {
            program.functions.insert(
                REQUIRES,
                func(
                    &crate::ir::names::requires_name("foo_spec"),
                    sig(vec![x.clone()], Type::Prop),
                    value(Expr::Const(Const::Bool(true))),
                    FunctionKind::Spec {
                        kind: SpecKind::Requires,
                        target: WRAPPER,
                    },
                ),
            );
        }
        if has_asserts {
            program.functions.insert(
                ASSERTS,
                func(
                    &crate::ir::names::asserts_name("foo_spec"),
                    sig(vec![x], Type::Bool),
                    value(Expr::Const(Const::Bool(true))),
                    FunctionKind::Spec {
                        kind: SpecKind::Asserts,
                        target: WRAPPER,
                    },
                ),
            );
        }
        program.spec_to_impl.insert(WRAPPER, IMPL);
        program
    }

    fn fixture_with_ensures(has_requires: bool, has_asserts: bool) -> Program {
        let mut program = fixture(has_requires, has_asserts);
        let x = param("x", Type::Bool);
        let result = param("result", Type::Bool);
        program.functions.insert(
            ENSURES,
            func(
                &crate::ir::names::ensures_name("foo_spec"),
                sig(vec![x, result], Type::Bool),
                value(Expr::Const(Const::Bool(true))),
                FunctionKind::Spec {
                    kind: SpecKind::Ensures,
                    target: WRAPPER,
                },
            ),
        );
        program
    }

    fn native(program: &Program, name: &str) -> FunId {
        program
            .natives
            .decls
            .iter()
            .find(|(_, decl)| decl.name == name)
            .map(|(fid, _)| *fid)
            .expect("native present")
    }

    fn theorem_body(program: &Program) -> Expr {
        program
            .functions
            .values()
            .find(|f| f.name == "foo_asserts_correct")
            .and_then(|f| match &f.body.tail {
                BlockTail::Value(e) => Some(e.clone()),
                _ => None,
            })
            .expect("asserts_correct theorem present")
    }

    fn correct_theorem_body(program: &Program) -> Expr {
        program
            .functions
            .values()
            .find(|f| f.name == "foo_correct")
            .and_then(|f| match &f.body.tail {
                BlockTail::Value(e) => Some(e.clone()),
                _ => None,
            })
            .expect("correct theorem present")
    }

    fn has_theorem(program: &Program, name: &str) -> bool {
        program
            .functions
            .values()
            .any(|f| f.name == name && matches!(f.kind, FunctionKind::Theorem { .. }))
    }

    fn has_axiom(program: &Program, name: &str) -> bool {
        program
            .functions
            .values()
            .any(|f| f.name == name && matches!(f.kind, FunctionKind::Axiom { .. }))
    }

    fn obligation_body(program: &Program, name: &str) -> Expr {
        program
            .functions
            .values()
            .find(|f| f.name == name)
            .and_then(|f| match &f.body.tail {
                BlockTail::Value(e) => Some(e.clone()),
                _ => None,
            })
            .unwrap_or_else(|| panic!("obligation `{}` present", name))
    }

    fn is_aborted(program: &Program) -> Expr {
        let abort_struct = program
            .struct_id_by_qualified_name(OPTION_QUALIFIED_NAME)
            .expect("abort result struct present");
        is_aborted_expr(
            abort_struct,
            call(ABORTS, Vec::new(), vec![Expr::Var(VarId::from("x"))]),
        )
    }

    #[test]
    fn asserts_correct_is_guarded_by_requires_when_present_without_asserts() {
        let mut program = fixture(true, false);
        run(&mut program);

        let imp = native(&program, Connective::Imp.native_name());
        let iff = native(&program, Connective::Iff.native_name());
        let expected = call(
            imp,
            Vec::new(),
            vec![
                call(REQUIRES, Vec::new(), vec![Expr::Var(VarId::from("x"))]),
                call(
                    iff,
                    Vec::new(),
                    vec![is_aborted(&program), Expr::Const(Const::Bool(false))],
                ),
            ],
        );

        assert_eq!(theorem_body(&program), expected);
    }

    #[test]
    fn asserts_correct_keeps_explicit_asserts_under_requires() {
        let mut program = fixture(true, true);
        run(&mut program);

        let imp = native(&program, Connective::Imp.native_name());
        let iff = native(&program, Connective::Iff.native_name());
        let neg = native(&program, Connective::Neg.native_name());
        let expected = call(
            imp,
            Vec::new(),
            vec![
                call(REQUIRES, Vec::new(), vec![Expr::Var(VarId::from("x"))]),
                call(
                    iff,
                    Vec::new(),
                    vec![
                        is_aborted(&program),
                        call(
                            neg,
                            Vec::new(),
                            vec![call(ASSERTS, Vec::new(), vec![Expr::Var(VarId::from("x"))])],
                        ),
                    ],
                ),
            ],
        );

        assert_eq!(theorem_body(&program), expected);
    }

    #[test]
    fn asserts_correct_without_requires_stays_unconditional() {
        let mut program = fixture(false, false);
        run(&mut program);

        let iff = native(&program, Connective::Iff.native_name());
        let expected = call(
            iff,
            Vec::new(),
            vec![is_aborted(&program), Expr::Const(Const::Bool(false))],
        );

        assert_eq!(theorem_body(&program), expected);
    }

    #[test]
    fn ignore_abort_skips_asserts_correct() {
        let mut program = fixture(false, false);
        program.spec_ignore_aborts.insert(WRAPPER, true);
        run(&mut program);

        assert!(!has_theorem(&program, "foo_asserts_correct"));
    }

    #[test]
    fn ignore_abort_guards_correct_with_no_abort() {
        let mut program = fixture_with_ensures(false, false);
        program.spec_ignore_aborts.insert(WRAPPER, true);
        run(&mut program);

        let imp = native(&program, Connective::Imp.native_name());
        let neg = native(&program, Connective::Neg.native_name());
        let expected = call(
            imp,
            Vec::new(),
            vec![
                call(neg, Vec::new(), vec![is_aborted(&program)]),
                call(
                    ENSURES,
                    Vec::new(),
                    vec![
                        Expr::Var(VarId::from("x")),
                        call(IMPL, Vec::new(), vec![Expr::Var(VarId::from("x"))]),
                    ],
                ),
            ],
        );

        assert_eq!(correct_theorem_body(&program), expected);
    }

    #[test]
    fn non_ignore_abort_keeps_correct_unguarded() {
        let mut program = fixture_with_ensures(false, false);
        run(&mut program);

        let expected = call(
            ENSURES,
            Vec::new(),
            vec![
                Expr::Var(VarId::from("x")),
                call(IMPL, Vec::new(), vec![Expr::Var(VarId::from("x"))]),
            ],
        );

        assert_eq!(correct_theorem_body(&program), expected);
    }

    #[test]
    fn trusted_pair_emits_axiom_obligations_with_theorem_statement() {
        // Same fixture as the prove path, but routed through
        // `trusted_spec_to_impl`: identical statements, `Axiom` kind.
        let mut program = fixture_with_ensures(false, false);
        let impl_fid = program.spec_to_impl.remove(&WRAPPER).expect("pair");
        program
            .trusted_spec_to_impl
            .insert(WRAPPER, (impl_fid, crate::ir::TrustReason::Skip));
        run(&mut program);

        assert!(has_axiom(&program, "foo_correct"));
        assert!(has_axiom(&program, "foo_asserts_correct"));
        assert!(!has_theorem(&program, "foo_correct"));
        assert!(!has_theorem(&program, "foo_asserts_correct"));

        // Trusted `_correct` uses the WRAPPER call as `result` (a native
        // impl's value-form return wouldn't match the ensures slot).
        let expected = call(
            ENSURES,
            Vec::new(),
            vec![
                Expr::Var(VarId::from("x")),
                call(WRAPPER, Vec::new(), vec![Expr::Var(VarId::from("x"))]),
            ],
        );
        assert_eq!(correct_theorem_body(&program), expected);
    }

    const NATIVE_IMPL: FunId = 10;
    const NATIVE_ABORTS: FunId = 11;
    const NATIVE_WRAPPER: FunId = 12;
    const NATIVE_ENSURES: FunId = 13;

    fn native_fixture(with_aborts: bool) -> Program {
        let mut program = Program::default();
        program.modules.insert(0, module());
        let x = param("x", Type::Bool);
        program.natives.decls.insert(
            NATIVE_IMPL,
            crate::ir::NativeDecl {
                module: 0,
                name: "nfoo".to_string(),
                signature: sig(vec![x.clone()], Type::Bool),
                effects: Effects::PURE,
                explicit_pure: false,
                is_framework: true,
                spec_target: None,
                user_native: None,
            },
        );
        if with_aborts {
            // Native `.aborts` companions are Bool-valued ("does it
            // abort?"), unlike the AbortResult-valued translated shape.
            program.natives.decls.insert(
                NATIVE_ABORTS,
                crate::ir::NativeDecl {
                    module: 0,
                    name: crate::ir::names::aborts_name("nfoo"),
                    signature: sig(vec![x.clone()], Type::Bool),
                    effects: Effects::PURE,
                    explicit_pure: true,
                    is_framework: true,
                    spec_target: Some(NATIVE_IMPL),
                    user_native: None,
                },
            );
        }
        program.functions.insert(
            NATIVE_WRAPPER,
            func(
                "nfoo_spec",
                sig(vec![x.clone()], Type::Bool),
                value(Expr::Const(Const::Bool(true))),
                FunctionKind::Source,
            ),
        );
        program.functions.insert(
            NATIVE_ENSURES,
            func(
                &crate::ir::names::ensures_name("nfoo_spec"),
                sig(vec![x, param("result", Type::Bool)], Type::Bool),
                value(Expr::Const(Const::Bool(true))),
                FunctionKind::Spec {
                    kind: SpecKind::Ensures,
                    target: NATIVE_WRAPPER,
                },
            ),
        );
        program.trusted_spec_to_impl.insert(
            NATIVE_WRAPPER,
            (NATIVE_IMPL, crate::ir::TrustReason::NonProve),
        );
        program
    }

    #[test]
    fn trusted_native_target_uses_bool_aborts_directly() {
        let mut program = native_fixture(true);
        run(&mut program);

        assert!(has_axiom(&program, "nfoo_correct"));
        assert!(has_axiom(&program, "nfoo_asserts_correct"));

        // The native's Bool `.aborts` is the abort condition itself --
        // no AbortResult match wrapper.
        let iff = native(&program, Connective::Iff.native_name());
        let expected = call(
            iff,
            Vec::new(),
            vec![
                call(NATIVE_ABORTS, Vec::new(), vec![Expr::Var(VarId::from("x"))]),
                Expr::Const(Const::Bool(false)),
            ],
        );
        assert_eq!(obligation_body(&program, "nfoo_asserts_correct"), expected);

        // Trusted `_correct` feeds the WRAPPER call as `result`, never
        // the native impl call (value-form return vs Mutation-retupled).
        let expected_correct = call(
            NATIVE_ENSURES,
            Vec::new(),
            vec![
                Expr::Var(VarId::from("x")),
                call(
                    NATIVE_WRAPPER,
                    Vec::new(),
                    vec![Expr::Var(VarId::from("x"))],
                ),
            ],
        );
        assert_eq!(obligation_body(&program, "nfoo_correct"), expected_correct);
    }

    #[test]
    fn prove_native_target_emits_theorem_obligations() {
        let mut program = native_fixture(true);
        let (impl_fid, _) = program
            .trusted_spec_to_impl
            .remove(&NATIVE_WRAPPER)
            .expect("trusted pair");
        program.spec_to_impl.insert(NATIVE_WRAPPER, impl_fid);
        run(&mut program);

        assert!(has_theorem(&program, "nfoo_correct"));
        assert!(has_theorem(&program, "nfoo_asserts_correct"));
        assert!(!has_axiom(&program, "nfoo_correct"));
        assert!(!has_axiom(&program, "nfoo_asserts_correct"));

        // The wrapper preserves the Mutation/world-retupled result shape for a
        // native target, just as it does on the trusted path.
        let expected = call(
            NATIVE_ENSURES,
            Vec::new(),
            vec![
                Expr::Var(VarId::from("x")),
                call(
                    NATIVE_WRAPPER,
                    Vec::new(),
                    vec![Expr::Var(VarId::from("x"))],
                ),
            ],
        );
        assert_eq!(obligation_body(&program, "nfoo_correct"), expected);
    }

    #[test]
    fn trusted_native_aborts_uses_companion_arity_not_base() {
        // Stage 4 appends ghost slots to the BASE native decl only; the
        // `.aborts` companion keeps its lift-time signature. The
        // obligation's aborts call must use the companion's own arity
        // (cetus `object::new` + `SpecObjectNewValue` ghost).
        let mut program = native_fixture(true);
        let g = param("__ghost_1", Type::Bool);
        program
            .natives
            .decls
            .get_mut(&NATIVE_IMPL)
            .expect("base native")
            .signature
            .params
            .push(g.clone());
        program
            .functions
            .get_mut(&NATIVE_WRAPPER)
            .expect("wrapper")
            .signature
            .params
            .push(g.clone());
        let ens = program.functions.get_mut(&NATIVE_ENSURES).expect("ensures");
        let result = ens.signature.params.pop().expect("result param");
        ens.signature.params.push(g);
        ens.signature.params.push(result);
        run(&mut program);

        let iff = native(&program, Connective::Iff.native_name());
        let expected = call(
            iff,
            Vec::new(),
            vec![
                call(NATIVE_ABORTS, Vec::new(), vec![Expr::Var(VarId::from("x"))]),
                Expr::Const(Const::Bool(false)),
            ],
        );
        assert_eq!(obligation_body(&program, "nfoo_asserts_correct"), expected);
    }

    #[test]
    fn trusted_native_without_aborts_emits_correct_only() {
        let mut program = native_fixture(false);
        run(&mut program);

        assert!(has_axiom(&program, "nfoo_correct"));
        assert!(program
            .functions
            .values()
            .all(|f| f.name != "nfoo_asserts_correct"));
    }

    // ---- world_wf injection -----------------------------------------

    const BAG_NATIVE: FunId = 20;
    const BAG_IMPL: FunId = 21;
    const BAG_WRAPPER: FunId = 22;
    const BAG_ENSURES: FunId = 23;
    const NONBAG_IMPL: FunId = 24;
    const NONBAG_WRAPPER: FunId = 25;
    const NONBAG_ENSURES: FunId = 26;

    fn df_module() -> Module {
        Module {
            name: "dynamic_field".to_string(),
            package_name: "Sui".to_string(),
            address: String::new(),
            required_imports: Vec::new(),
            is_native: true,
        }
    }

    fn store_bag_borrow_native(module: crate::ir::ModId) -> crate::ir::NativeDecl {
        crate::ir::NativeDecl {
            module,
            name: "store_bag_borrow".to_string(),
            signature: sig(vec![param("uid", Type::Unit)], Type::Bool),
            effects: Effects::PURE,
            explicit_pure: true,
            is_framework: true,
            spec_target: None,
            user_native: None,
        }
    }

    /// Two world-threaded `(x, world)` impls, each with a spec wrapper +
    /// `.ensures`: `bag_impl` calls the `store_bag_borrow` native (so it is
    /// in `needs_world_wf`), `plain_impl` touches no bag op. Used to prove
    /// the gate discriminates.
    fn bag_fixture() -> Program {
        let mut program = Program::default();
        program.modules.insert(0, module());
        let df_mod: crate::ir::ModId = 1;
        program.modules.insert(df_mod, df_module());
        ensure_aborts_types(&mut program);

        program
            .natives
            .decls
            .insert(BAG_NATIVE, store_bag_borrow_native(df_mod));

        let x = param("x", Type::Bool);
        let world = param("world", Type::Unit);
        let result = param("result", Type::Bool);

        program.functions.insert(
            BAG_IMPL,
            func(
                "bag_impl",
                sig(vec![x.clone(), world.clone()], Type::Bool),
                value(call(
                    BAG_NATIVE,
                    Vec::new(),
                    vec![Expr::Const(Const::Bool(true))],
                )),
                FunctionKind::Source,
            ),
        );
        program.functions.insert(
            BAG_WRAPPER,
            func(
                "bag_impl_spec",
                sig(vec![x.clone(), world.clone()], Type::Bool),
                value(Expr::Const(Const::Bool(true))),
                FunctionKind::Source,
            ),
        );
        program.functions.insert(
            BAG_ENSURES,
            func(
                &crate::ir::names::ensures_name("bag_impl_spec"),
                sig(vec![x.clone(), world.clone(), result.clone()], Type::Bool),
                value(Expr::Const(Const::Bool(true))),
                FunctionKind::Spec {
                    kind: SpecKind::Ensures,
                    target: BAG_WRAPPER,
                },
            ),
        );
        program.spec_to_impl.insert(BAG_WRAPPER, BAG_IMPL);

        program.functions.insert(
            NONBAG_IMPL,
            func(
                "plain_impl",
                sig(vec![x.clone(), world.clone()], Type::Bool),
                value(Expr::Const(Const::Bool(true))),
                FunctionKind::Source,
            ),
        );
        program.functions.insert(
            NONBAG_WRAPPER,
            func(
                "plain_impl_spec",
                sig(vec![x.clone(), world.clone()], Type::Bool),
                value(Expr::Const(Const::Bool(true))),
                FunctionKind::Source,
            ),
        );
        program.functions.insert(
            NONBAG_ENSURES,
            func(
                &crate::ir::names::ensures_name("plain_impl_spec"),
                sig(vec![x, world, result], Type::Bool),
                value(Expr::Const(Const::Bool(true))),
                FunctionKind::Spec {
                    kind: SpecKind::Ensures,
                    target: NONBAG_WRAPPER,
                },
            ),
        );
        program.spec_to_impl.insert(NONBAG_WRAPPER, NONBAG_IMPL);

        program
    }

    #[test]
    fn needs_world_wf_seeds_direct_bag_callers_only() {
        let program = bag_fixture();
        let needs = needs_world_wf(&program);
        assert!(
            needs.contains(&BAG_IMPL),
            "a direct store_bag_borrow caller seeds the set"
        );
        assert!(
            !needs.contains(&NONBAG_IMPL),
            "a non-bag world-threading impl is excluded"
        );
        assert!(
            !needs.contains(&BAG_NATIVE),
            "the bag native is a seed, not a member"
        );
    }

    #[test]
    fn reserved_native_collisions_do_not_alias_obligation_intrinsics() {
        let mut program = bag_fixture();
        let imp_collision = 100;
        program.natives.decls.insert(
            imp_collision,
            crate::ir::NativeDecl {
                module: 0,
                name: Connective::Imp.native_name().to_string(),
                signature: Connective::Imp.signature(),
                effects: Effects::PURE,
                explicit_pure: true,
                is_framework: false,
                spec_target: None,
                user_native: Some(true),
            },
        );
        let world_wf_collision = 101;
        program.natives.decls.insert(
            world_wf_collision,
            crate::ir::NativeDecl {
                module: 1,
                name: WORLD_WF_NAME.to_string(),
                signature: world_wf_signature(),
                effects: Effects::PURE,
                explicit_pure: true,
                is_framework: false,
                spec_target: None,
                user_native: Some(true),
            },
        );

        let imp = register_connective(&mut program, Connective::Imp, 0);
        let world_wf = register_world_wf(&mut program);

        assert_ne!(imp, imp_collision);
        assert_ne!(world_wf, world_wf_collision);
        assert_eq!(
            Connective::from_native_decl(&program.natives.decls[&imp]),
            Some(Connective::Imp)
        );
        assert_eq!(
            Connective::from_native_decl(&program.natives.decls[&imp_collision]),
            None
        );
        assert!(is_world_wf_native(&program, world_wf));
        assert!(!is_world_wf_native(&program, world_wf_collision));
        assert_eq!(register_connective(&mut program, Connective::Imp, 0), imp);
        assert_eq!(register_world_wf(&mut program), world_wf);
    }

    #[test]
    fn world_wf_prepended_only_on_bag_touching_correct_obligation() {
        let mut program = bag_fixture();
        run(&mut program);

        let imp = native(&program, Connective::Imp.native_name());
        let world_wf = native(&program, WORLD_WF_NAME);
        let world = || Expr::Var(VarId::from("world"));
        let x = || Expr::Var(VarId::from("x"));

        // Bag-touching `_correct`:
        //   world_wf world -> ensures(x, world, impl(x, world)).
        let ens = call(
            BAG_ENSURES,
            Vec::new(),
            vec![x(), world(), call(BAG_IMPL, Vec::new(), vec![x(), world()])],
        );
        let expected = call(
            imp,
            Vec::new(),
            vec![call(world_wf, Vec::new(), vec![world()]), ens],
        );
        assert_eq!(obligation_body(&program, "bag_impl_correct"), expected);

        // Non-bag `_correct`: same shape, NO world_wf hypothesis.
        let plain_expected = call(
            NONBAG_ENSURES,
            Vec::new(),
            vec![
                x(),
                world(),
                call(NONBAG_IMPL, Vec::new(), vec![x(), world()]),
            ],
        );
        assert_eq!(
            obligation_body(&program, "plain_impl_correct"),
            plain_expected
        );
    }

    // --- targetless prove specs (`#[spec(prove)]` with no `target=`) ---

    const LEMMA: FunId = 20;
    const LEMMA_ABORTS: FunId = 21;
    const LEMMA_REQUIRES: FunId = 22;
    const LEMMA_ASSERTS: FunId = 23;
    const LEMMA_ENSURES: FunId = 24;

    /// A standalone lemma with the full companion set the renderer
    /// already emits for one (`.aborts`, `.requires`, `.ensures`, and
    /// optionally `.asserts`) and NO entry in `spec_to_impl`.
    fn targetless_fixture(has_requires: bool, has_asserts: bool, has_ensures: bool) -> Program {
        let mut program = Program::default();
        program.modules.insert(0, module());
        let abort_types = ensure_aborts_types(&mut program);
        let x = param("x", Type::Bool);

        program.functions.insert(
            LEMMA,
            func(
                "frozen_rate_spec",
                sig(vec![x.clone()], Type::Bool),
                value(Expr::Const(Const::Bool(true))),
                FunctionKind::Source,
            ),
        );
        program.functions.insert(
            LEMMA_ABORTS,
            func(
                &crate::ir::names::aborts_name("frozen_rate_spec"),
                sig(vec![x.clone()], abort_types.option_abort_code_type()),
                value(abort_types.make_none()),
                FunctionKind::Spec {
                    kind: SpecKind::Aborts,
                    target: LEMMA,
                },
            ),
        );
        if has_requires {
            program.functions.insert(
                LEMMA_REQUIRES,
                func(
                    &crate::ir::names::requires_name("frozen_rate_spec"),
                    sig(vec![x.clone()], Type::Prop),
                    value(Expr::Const(Const::Bool(true))),
                    FunctionKind::Spec {
                        kind: SpecKind::Requires,
                        target: LEMMA,
                    },
                ),
            );
        }
        if has_asserts {
            program.functions.insert(
                LEMMA_ASSERTS,
                func(
                    &crate::ir::names::asserts_name("frozen_rate_spec"),
                    sig(vec![x.clone()], Type::Bool),
                    value(Expr::Const(Const::Bool(true))),
                    FunctionKind::Spec {
                        kind: SpecKind::Asserts,
                        target: LEMMA,
                    },
                ),
            );
        }
        if has_ensures {
            program.functions.insert(
                LEMMA_ENSURES,
                func(
                    &crate::ir::names::ensures_name("frozen_rate_spec"),
                    sig(vec![x, param("result", Type::Bool)], Type::Bool),
                    value(Expr::Const(Const::Bool(true))),
                    FunctionKind::Spec {
                        kind: SpecKind::Ensures,
                        target: LEMMA,
                    },
                ),
            );
        }
        program.targetless_prove_specs.insert(LEMMA);
        program
    }

    fn lemma_x() -> Expr {
        Expr::Var(VarId::from("x"))
    }

    #[test]
    fn targetless_prove_spec_emits_correct_from_its_own_companions() {
        let mut program = targetless_fixture(true, false, true);
        run(&mut program);

        let imp = native(&program, Connective::Imp.native_name());
        let expected = call(
            imp,
            Vec::new(),
            vec![
                call(LEMMA_REQUIRES, Vec::new(), vec![lemma_x()]),
                call(
                    LEMMA_ENSURES,
                    Vec::new(),
                    vec![lemma_x(), call(LEMMA, Vec::new(), vec![lemma_x()])],
                ),
            ],
        );
        assert_eq!(obligation_body(&program, "frozen_rate_correct"), expected);
    }

    #[test]
    fn targetless_prove_spec_keeps_the_asserts_clause_when_present() {
        let mut program = targetless_fixture(true, true, true);
        run(&mut program);

        let imp = native(&program, Connective::Imp.native_name());
        let expected = call(
            imp,
            Vec::new(),
            vec![
                call(LEMMA_REQUIRES, Vec::new(), vec![lemma_x()]),
                call(
                    imp,
                    Vec::new(),
                    vec![
                        call(LEMMA_ASSERTS, Vec::new(), vec![lemma_x()]),
                        call(
                            LEMMA_ENSURES,
                            Vec::new(),
                            vec![lemma_x(), call(LEMMA, Vec::new(), vec![lemma_x()])],
                        ),
                    ],
                ),
            ],
        );
        assert_eq!(obligation_body(&program, "frozen_rate_correct"), expected);
    }

    /// The wrapper's own `.aborts` is NOT an impl's abort face. Emitting
    /// `_asserts_correct` off it would turn the obligation into a
    /// "this lemma's scenario is executable" claim, which nobody declared.
    #[test]
    fn targetless_prove_spec_emits_no_asserts_correct() {
        let mut program = targetless_fixture(true, true, true);
        run(&mut program);

        assert!(has_theorem(&program, "frozen_rate_correct"));
        assert!(!has_theorem(&program, "frozen_rate_asserts_correct"));
        assert!(!has_theorem(&program, "frozen_rate_spec_asserts_correct"));
    }

    fn lemma_is_aborted(program: &Program) -> Expr {
        let abort_struct = program
            .struct_id_by_qualified_name(OPTION_QUALIFIED_NAME)
            .expect("abort result struct present");
        is_aborted_expr(
            abort_struct,
            call(LEMMA_ABORTS, Vec::new(), vec![lemma_x()]),
        )
    }

    /// A targetless `#[spec(prove, ignore_abort)]` wrapper is verified by
    /// Boogie under `AssertsMode::Assume`, which turns every abort site in
    /// the scenario body into `assume !$abort_flag`. The Lean obligation
    /// must carry the matching premise, over the wrapper's OWN `.aborts` --
    /// the only abort face a targetless lemma has. Without it the statement
    /// is strictly stronger than the discharged claim and, where the total
    /// rendering wraps instead of aborting, false: four momentum
    /// obligations were refuted at concrete witnesses.
    #[test]
    fn targetless_ignore_abort_correct_is_guarded_by_its_own_no_abort() {
        let mut program = targetless_fixture(true, true, true);
        program.spec_ignore_aborts.insert(LEMMA, true);
        run(&mut program);

        let imp = native(&program, Connective::Imp.native_name());
        let neg = native(&program, Connective::Neg.native_name());
        let expected = call(
            imp,
            Vec::new(),
            vec![
                call(LEMMA_REQUIRES, Vec::new(), vec![lemma_x()]),
                call(
                    imp,
                    Vec::new(),
                    vec![
                        call(neg, Vec::new(), vec![lemma_is_aborted(&program)]),
                        call(
                            imp,
                            Vec::new(),
                            vec![
                                call(LEMMA_ASSERTS, Vec::new(), vec![lemma_x()]),
                                call(
                                    LEMMA_ENSURES,
                                    Vec::new(),
                                    vec![lemma_x(), call(LEMMA, Vec::new(), vec![lemma_x()])],
                                ),
                            ],
                        ),
                    ],
                ),
            ],
        );
        assert_eq!(obligation_body(&program, "frozen_rate_correct"), expected);
    }

    /// The guard is scoped to `ignore_abort` and nothing else. WITHOUT it
    /// upstream verifies the same scenario under `AssertsMode::Check`,
    /// which ASSERTS `!$abort_flag` at every abort site -- so Boogie proves
    /// totality as well as the postcondition, and the unguarded statement
    /// is sound. Adding the premise there would weaken an obligation
    /// nobody asked to weaken.
    #[test]
    fn targetless_without_ignore_abort_keeps_correct_unguarded() {
        let mut program = targetless_fixture(true, true, true);
        run(&mut program);

        let imp = native(&program, Connective::Imp.native_name());
        let expected = call(
            imp,
            Vec::new(),
            vec![
                call(LEMMA_REQUIRES, Vec::new(), vec![lemma_x()]),
                call(
                    imp,
                    Vec::new(),
                    vec![
                        call(LEMMA_ASSERTS, Vec::new(), vec![lemma_x()]),
                        call(
                            LEMMA_ENSURES,
                            Vec::new(),
                            vec![lemma_x(), call(LEMMA, Vec::new(), vec![lemma_x()])],
                        ),
                    ],
                ),
            ],
        );
        assert_eq!(obligation_body(&program, "frozen_rate_correct"), expected);
    }

    /// Resolving the wrapper's own `.aborts` for the `_correct` guard must
    /// not leak it into an `_asserts_correct` face: abort-faithfulness is a
    /// claim between an impl and its spec, and there is no impl here.
    #[test]
    fn targetless_ignore_abort_still_emits_no_asserts_correct() {
        let mut program = targetless_fixture(true, true, true);
        program.spec_ignore_aborts.insert(LEMMA, true);
        run(&mut program);

        assert!(has_theorem(&program, "frozen_rate_correct"));
        assert!(!has_theorem(&program, "frozen_rate_asserts_correct"));
    }

    /// No `.aborts` companion means no premise to add. The obligation is
    /// still emitted (unguarded, as before) and the render discloses it on
    /// stderr rather than silently overstating the claim.
    #[test]
    fn targetless_ignore_abort_without_an_aborts_companion_stays_unguarded() {
        let mut program = targetless_fixture(true, false, true);
        program.spec_ignore_aborts.insert(LEMMA, true);
        program.functions.remove(&LEMMA_ABORTS);
        run(&mut program);

        let imp = native(&program, Connective::Imp.native_name());
        let expected = call(
            imp,
            Vec::new(),
            vec![
                call(LEMMA_REQUIRES, Vec::new(), vec![lemma_x()]),
                call(
                    LEMMA_ENSURES,
                    Vec::new(),
                    vec![lemma_x(), call(LEMMA, Vec::new(), vec![lemma_x()])],
                ),
            ],
        );
        assert_eq!(obligation_body(&program, "frozen_rate_correct"), expected);
    }

    #[test]
    fn targetless_prove_spec_without_ensures_emits_nothing() {
        let mut program = targetless_fixture(true, true, false);
        run(&mut program);

        assert!(!program
            .functions
            .values()
            .any(|f| matches!(f.kind, FunctionKind::Theorem { .. })));
    }

    /// `target` and `source` both name the wrapper: the manifest's
    /// `target_source` must agree with the authoritative roster, which
    /// rosters a targetless lemma against itself.
    #[test]
    fn targetless_obligation_targets_the_wrapper_itself() {
        let mut program = targetless_fixture(true, false, true);
        run(&mut program);

        let kind = program
            .functions
            .values()
            .find(|f| f.name == "frozen_rate_correct")
            .map(|f| f.kind.clone())
            .expect("targetless obligation present");
        assert!(matches!(
            kind,
            FunctionKind::Theorem {
                target: LEMMA,
                source: LEMMA
            }
        ));
    }

    #[test]
    fn targetless_prove_spec_with_no_translated_wrapper_emits_nothing() {
        let mut program = targetless_fixture(true, false, true);
        program.functions.remove(&LEMMA);
        run(&mut program);

        assert!(!has_theorem(&program, "frozen_rate_correct"));
    }

    /// Paired and targetless obligations coexist in one module without
    /// either renaming the other.
    #[test]
    fn targetless_obligations_coexist_with_paired_ones() {
        let mut program = fixture_with_ensures(true, false);
        let x = param("x", Type::Bool);
        program.functions.insert(
            LEMMA,
            func(
                "frozen_rate_spec",
                sig(vec![x.clone()], Type::Bool),
                value(Expr::Const(Const::Bool(true))),
                FunctionKind::Source,
            ),
        );
        program.functions.insert(
            LEMMA_ENSURES,
            func(
                &crate::ir::names::ensures_name("frozen_rate_spec"),
                sig(vec![x, param("result", Type::Bool)], Type::Bool),
                value(Expr::Const(Const::Bool(true))),
                FunctionKind::Spec {
                    kind: SpecKind::Ensures,
                    target: LEMMA,
                },
            ),
        );
        program.targetless_prove_specs.insert(LEMMA);
        run(&mut program);

        assert!(has_theorem(&program, "foo_correct"));
        assert!(has_theorem(&program, "foo_asserts_correct"));
        assert!(has_theorem(&program, "frozen_rate_correct"));
    }
}
