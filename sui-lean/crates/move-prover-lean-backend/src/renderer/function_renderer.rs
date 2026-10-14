// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Renders Function to Lean syntax.
//! Dumb renderer — just emits `def name (params) : ReturnType := body` for each function.

use intermediate_theorem_format::{
    Function, FunctionID, IRNode, ModuleID, Program, ProofParam, Type,
};
use std::collections::HashSet;
use std::fmt::Write;

use super::context::RenderCtx;
use super::lean_writer::LeanWriter;
use super::render;
use super::type_renderer::{type_to_string_full_with_mut, type_to_string_with_params};
use crate::escape;

/// Render a proof parameter's Lean type. `LoopInvHook` applies the hook to the
/// carrying function's type params and value params (with identifier escaping);
/// `Verbatim` is emitted as-is. Shared by the function renderer and
/// goal-statement rendering so the binder form never drifts between them.
pub(crate) fn proof_param_type_string(
    pp: &ProofParam,
    func: &Function,
    program: &Program,
) -> String {
    use intermediate_theorem_format::ProofParamType;
    match &pp.param_type {
        ProofParamType::Verbatim(s) => s.clone(),
        ProofParamType::DataInv {
            key_type,
            value_type,
            pred,
            map_expr,
        } => {
            // Fully-qualified type rendering (namespace = None) so the binder
            // elaborates identically in module, Correctness, and Proofs files.
            let k = type_to_string_with_params(key_type, program, None, None);
            let v = type_to_string_with_params(value_type, program, None, None);
            format!("TypedMap.all ({}) ({}) {} {}", k, v, pred, map_expr)
        }
        ProofParamType::DataInvWorld { parent_expr, pred } => {
            // World-mode face (unified-backend design §7, Phase 5): the
            // hypothesis quantifies the threaded `__world` binder, which is
            // always in scope on the carrying spec face (Phase B threads it
            // before proof params materialize). The stored value type is
            // inferred from the predicate's domain.
            format!(
                "Prover.World.World.allDf __world (World.uidNat {}) {}",
                parent_expr, pred
            )
        }
        ProofParamType::LoopInvHook(hook) => {
            let mut s = hook.clone();
            for tp in &func.signature.type_params {
                s.push(' ');
                s.push_str(&escape::escape_identifier(tp));
            }
            for p in &func.signature.parameters {
                s.push(' ');
                s.push_str(&escape::escape_identifier(&p.name));
            }
            s
        }
    }
}

/// Check if a type contains MutableReference (possibly nested in a Tuple).
fn contains_mutable_ref(ty: &Type) -> bool {
    match ty {
        Type::MutableReference(_, _) => true,
        Type::Tuple(elems) => elems.iter().any(contains_mutable_ref),
        _ => false,
    }
}

/// Check if a function cannot be rendered as a Lean definition.
pub fn must_skip_function(func: &Function) -> bool {
    let body_is_empty = matches!(&func.body, IRNode::Tuple(v) if v.is_empty());
    if body_is_empty && func.name == "default" {
        return true;
    }
    false
}

/// Render a function definition.
/// `target_module_id` is the module being rendered to (may differ from func.module_id for merged modules)
/// `has_termination_measure` indicates whether a Termination/ file defines a
/// `<func>.termination` measure for THIS function, enabling a user-provided
/// termination measure + decreasing macro instead of the sorry-based default.

/// Render the recomposition lemmas for `.aborts` functions decomposed by the
/// `decompose_aborts` pass: `theorem <fn>.decompose ... : <fn> args =
/// <fn>.seg_1 args := rfl`. One per decomposition whose parent lives in
/// `module_id`. Returns the concatenated theorem text ("" if none).
pub fn render_decompose_theorems(
    program: &Program,
    module_id: ModuleID,
    current_module_namespace: &str,
) -> String {
    if program.for_test {
        return String::new();
    }
    let mut out = String::new();
    for (aborts_id, seg1_id) in &program.aborts_decompositions {
        let parent = program.functions.get(aborts_id);
        if parent.module_id != module_id {
            continue;
        }
        let seg1 = program.functions.get(seg1_id);
        let pname = escape::escape_identifier(&parent.name);
        let sname = escape::escape_identifier(&seg1.name);
        let mut binders = String::new();
        for p in &parent.signature.parameters {
            let ty = type_to_string_with_params(
                &p.param_type,
                program,
                Some(current_module_namespace),
                Some(&parent.signature.type_params),
            );
            binders.push_str(&format!(
                " ({} : {})",
                escape::escape_identifier(&p.name),
                ty
            ));
        }
        for pp in &parent.signature.proof_params {
            binders.push_str(&format!(
                " ({} : {})",
                pp.name,
                proof_param_type_string(pp, parent, program)
            ));
        }
        let args = |f: &Function| -> String {
            f.signature
                .parameters
                .iter()
                .map(|p| escape::escape_identifier(&p.name))
                .chain(f.signature.proof_params.iter().map(|pp| pp.name.clone()))
                .map(|a| format!(" {}", a))
                .collect()
        };
        out.push_str(&format!(
            "/-- Recomposition of the segmented `.aborts` body (see `decompose_aborts`).\nRewrite with this, then discharge one `seg_k = none` at a time. -/\ntheorem {p}.decompose{binders} :\n    {p}{la} = {s}{ra} := rfl\n\n",
            p = pname,
            s = sname,
            binders = binders,
            la = args(parent),
            ra = args(seg1),
        ));
    }
    out
}

pub fn render_function<W: Write>(
    func: &Function,
    func_id: FunctionID,
    program: &Program,
    current_module_namespace: &str,
    w: LeanWriter<W>,
    merged_module_ids: &HashSet<ModuleID>,
    target_module_id: ModuleID,
    has_termination_measure: bool,
) -> LeanWriter<W> {
    let escaped_name = escape::escape_identifier(&func.name);

    render_function_inner(
        func,
        func_id,
        &escaped_name,
        program,
        current_module_namespace,
        w,
        merged_module_ids,
        target_module_id,
        has_termination_measure,
    )
}

fn render_function_inner<W: Write>(
    func: &Function,
    func_id: FunctionID,
    escaped_name: &str,
    program: &Program,
    current_module_namespace: &str,
    mut w: LeanWriter<W>,
    merged_module_ids: &HashSet<ModuleID>,
    target_module_id: ModuleID,
    has_termination_measure: bool,
) -> LeanWriter<W> {
    // Mark non-mutual non-native defs `@[reducible]` so `decide` and `simp`
    // can unfold them when discharging test obligations. Mutual groups are
    // excluded because Lean rejects `@[reducible]` on `partial def` and on
    // functions in mutual blocks where reducibility can cause unification
    // loops. `.requires`/`.ensures` (Prop-returning) are also excluded — they
    // shouldn't unfold during regular elaboration.
    if func.mutual_group_id.is_none()
        && !func.is_uninterpreted
        && !func.is_native
        && !func.name.contains(".requires")
        && !func.name.contains(".ensures")
        && !func.name.contains(".asserts_cond")
        // Loop-body helpers extracted by `loop_body_extraction` (named
        // `<loop>.while_N.step`) MUST stay non-reducible: their whole purpose is
        // to be an opaque call inside the recursive loop, so the well-founded
        // eq-lemma elaboration does not span their (heavy) body. `@[reducible]`
        // lets the elaborator unfold them back in, re-triggering the WF blow-up.
        && !func.name.ends_with(".step")
        && func.signature.return_type != intermediate_theorem_format::Type::Prop
        // Under the per-module `irreducible_defs` gate (§5.3) the def gets
        // `attribute [irreducible]` AFTER its equation-lemma block instead
        // (see `render_equation_lemmas`); `@[reducible]` here would conflict.
        && !program.equation_lemmas.iter().any(|s| s.fn_id == func_id)
    {
        w.write("@[reducible] ");
    }
    // Uninterpreted spec helpers render as `opaque` constants: binders +
    // return type, no body — congruence-only reasoning by construction.
    if func.is_uninterpreted {
        w.write("opaque ");
    } else {
        w.write("def ");
    }
    w.write(escaped_name);

    // All generated defs take their type parameters explicitly (`(t_tv0 : Type)`).
    // This keeps a single convention end-to-end: the call-site loop unconditionally
    // emits the matching positional type args.
    render_type_params(&func.signature.type_params, false, &mut w);

    // World-mode generic state ops (unified-backend design Phase 5): type
    // params flowing into World typed views need a `HasCode TyCode` instance.
    // Instance-implicit, so the positional call-site type-arg convention is
    // unchanged (Lean synthesizes at concrete instantiations from the
    // Generated/TyCodeInterp instances, and forwards binders in generic
    // middle layers).
    if let Some(idx) = program.fn_hascode_params.get(&func_id) {
        for &i in idx {
            w.write(&format!(
                " [HasCode TyCode {}]",
                escape::escape_identifier(&func.signature.type_params[i as usize])
            ));
        }
    }
    // Bag-universe (`BagU`) constraint for type params flowing into a
    // `bag`/`object_bag` op over a generic value type (e.g. `Bag.borrow
    // (Balance T)`). Separate universe from the World `TyCode` binder above.
    if let Some(idx) = program.fn_bagu_params.get(&func_id) {
        for &i in idx {
            w.write(&format!(
                " [HasCode BagU {}]",
                escape::escape_identifier(&func.signature.type_params[i as usize])
            ));
        }
    }

    // `decompose_aborts` splits an oversized `.aborts` body into `<fn>.seg_N`
    // helpers purely to keep individual Lean defs small — it is NOT a real
    // Move function boundary. Their Mutable-typed parameters are plumbing
    // for a single value threaded straight from the parent segment (tracked
    // concretely by `decompose_aborts`'s `env`/`try_type`), not a genuine
    // `&mut` argument whose caller-side container is unknown. Genericizing
    // them behind a fresh `{s : Type}` (as done below for ordinary functions)
    // erases that concrete state and breaks any later concretization of the
    // same variable (e.g. a write-back `Mutable.apply` immediately field-
    // projected) — see the Test_runner.lean `s_1`/`runner.scenario` bug.
    // Segment functions therefore always render the stored concrete state.
    let is_segment = func.name.contains(".seg_");

    // Count &mut parameters to determine state variable names
    let mut_param_count = func
        .signature
        .parameters
        .iter()
        .filter(|p| matches!(p.param_type, Type::MutableReference(_, _)))
        .count();

    let mut mut_param_idx = 0;
    let state_var_name = |idx: usize, total: usize| -> String {
        if total == 1 {
            "s".to_string()
        } else {
            format!("s_{}", idx + 1)
        }
    };

    // Emit {s : Type} implicits for each &mut parameter (segments render the
    // concrete state directly and need no implicit type variable).
    if !is_segment {
        for p in &func.signature.parameters {
            if matches!(p.param_type, Type::MutableReference(_, _)) {
                let svar = state_var_name(mut_param_idx, mut_param_count);
                w.write(&format!(" {{{} : Type}}", svar));
                mut_param_idx += 1;
            }
        }
    }

    // Reset counter for param rendering
    mut_param_idx = 0;

    // Parameters
    for p in &func.signature.parameters {
        let param_name = if p.name.is_empty() || p.name == "_" {
            panic!("BUG: Parameter has empty or underscore name in function '{}': param name='{}' ssa_value='{}'", func.name, p.name, p.ssa_value);
        } else {
            escape::escape_identifier(&p.name)
        };

        let type_str = if matches!(p.param_type, Type::MutableReference(_, _)) {
            if is_segment {
                type_to_string_with_params(
                    &p.param_type,
                    program,
                    Some(current_module_namespace),
                    Some(&func.signature.type_params),
                )
            } else {
                let svar = state_var_name(mut_param_idx, mut_param_count);
                mut_param_idx += 1;
                type_to_string_full_with_mut(
                    &p.param_type,
                    program,
                    Some(current_module_namespace),
                    Some(&func.signature.type_params),
                    Some(&svar),
                )
            }
        } else {
            type_to_string_with_params(
                &p.param_type,
                program,
                Some(current_module_namespace),
                Some(&func.signature.type_params),
            )
        };

        w.write(" (");
        w.write(&param_name);
        w.write(" : ");
        w.write(&type_str);
        w.write(")");
    }

    // Proof parameters (`hinv` loop-invariant hypothesis, `hpre` precondition
    // hypothesis) — appended after the value params. These were materialized
    // onto the signature as the single source of truth; the renderer just emits
    // them in order. See `Program::materialize_proof_params`.
    for pp in &func.signature.proof_params {
        w.write(" (");
        w.write(&pp.name);
        w.write(" : ");
        w.write(&proof_param_type_string(pp, func, program));
        w.write(")");
    }

    // Body analysis - needed to decide whether to include return type
    let body = &func.body;
    let body_is_empty = matches!(&body, IRNode::Tuple(v) if v.is_empty());
    let return_type_is_unit = matches!(&func.signature.return_type, Type::Tuple(v) if v.is_empty());
    let body_is_sorry = body_is_empty && !return_type_is_unit;

    // Return type handling:
    // For MutableReference returns: ALWAYS skip the annotation (let Lean infer).
    // The stored state type is a placeholder that is often incorrect.
    // Even for sorry bodies, wrong type annotations cause type mismatches.
    // Lean will either infer from call sites or fail with "can't synthesize".
    // For all other types: render the annotation (needed for sorry bodies).
    if func.is_uninterpreted {
        assert!(
            !contains_mutable_ref(&func.signature.return_type),
            "uninterpreted function `{}` must not return a mutable reference",
            func.name
        );
        w.write(" : ");
        let type_str = type_to_string_with_params(
            &func.signature.return_type,
            program,
            Some(current_module_namespace),
            Some(&func.signature.type_params),
        );
        w.write(&type_str);
        w.newline();
        return w;
    }

    if contains_mutable_ref(&func.signature.return_type) {
        w.line(" :=");
    } else {
        w.write(" : ");
        let type_str = type_to_string_with_params(
            &func.signature.return_type,
            program,
            Some(current_module_namespace),
            Some(&func.signature.type_params),
        );
        w.write(&type_str);
        w.line(" :=");
    }

    // Body
    w.indent(false);

    if body_is_sorry {
        // `sorry` would panic the Lean executable (`INTERNAL PANIC: executed
        // 'sorry'`) under the per-test driver, which evaluates the body
        // directly. Emit the parseable `raiseAbort` marker instead so the
        // driver catches it as a structured abort verdict.
        let module = program.modules.get(func.module_id);
        w.write(&format!(
            "MoveAbort.raiseAbort 0 MoveAbort.AbortSource.userAssert \"{}::{}\"",
            module.package_name, module.name
        ));
        w.dedent(false);
        w.newline();
        return w;
    }

    if body_is_empty && return_type_is_unit {
        w.write("()");
    } else {
        let mut registry = func.param_registry(program);
        let mut ctx = RenderCtx::new(
            program,
            target_module_id,
            Some(current_module_namespace),
            w,
            merged_module_ids.clone(),
        );
        // Set the current function name
        ctx.current_function_name = escaped_name.to_string();
        ctx.current_function_id = Some(func_id);
        ctx.object_field_borrow_children =
            intermediate_theorem_format::analysis::dynamic_field_rewriting::collect_object_field_borrow_children(
                ctx.program,
                &func.body,
            );
        ctx.current_function_params = func
            .signature
            .parameters
            .iter()
            .map(|p| escape::escape_identifier(&p.name))
            .collect();
        // Set type params on the context for proper rendering
        ctx.with_type_params(&func.signature.type_params);
        // Set mutual group info so the renderer can detect all-fixed recursive calls
        if let Some(group_id) = func.mutual_group_id {
            let param_names: Vec<String> = func
                .signature
                .parameters
                .iter()
                .map(|p| p.name.clone())
                .collect();
            ctx.mutual_group_info = Some((group_id, param_names));
            // Collect escaped names of all functions in this mutual group
            ctx.mutual_group_func_names = program
                .functions
                .iter()
                .filter(|(_, f)| f.mutual_group_id == Some(group_id))
                .map(|(_, f)| escape::escape_identifier(&f.name))
                .collect();
        }
        render::render(body, &mut ctx, &mut registry);

        if render::body_ends_with_let(body) {
            ctx.newline();
            ctx.write("()");
        }

        w = ctx.into_writer();
    }

    w.dedent(false);

    // While-loop functions (in mutual groups) need termination_by since
    // Lean can't infer a decreasing measure.
    //
    // If a Termination/ file exists, reference user-provided definitions:
    //   termination_by <func>.termination <args>
    //   decreasing_by exact <func>.decreasing ‹_›
    //
    // Otherwise, use sorry-based defaults that keep definitions transparent:
    //   termination_by (0 : Nat)
    //   decreasing_by all_goals sorry
    if func.mutual_group_id.is_some() {
        // A while/after helper is named `<base>.while_N`, `<base>.after`, with an
        // optional `.aborts` suffix. If `<base>` carries a
        // `#[spec_only(loop_inv(target=<base>))]` invariant, the loop is known to
        // terminate under that invariant, so emit the user-measure + decreasing-macro
        // form (the proof lives in a Termination/ file) instead of the sorry default.
        // Scoped strictly to loop_inv-bearing loops: every other recursive helper is
        // emitted byte-for-byte as before.
        let base_name = {
            let n = func.name.strip_suffix(".aborts").unwrap_or(&func.name);
            let n = n.strip_suffix(".after").unwrap_or(n);
            match n.rfind(".while_") {
                Some(i) => &n[..i],
                None => n,
            }
        };
        let has_loop_inv = program.loop_invariants.contains_key(base_name);
        w.newline();
        if has_termination_measure || has_loop_inv {
            // termination_by: reference a user-provided Nat-valued definition.
            // The user defines it in Termination/<module>.lean inside the same namespace.
            // Pass type params first (explicit in the termination function), then
            // all regular parameters so the user can choose which ones to use.
            w.write("termination_by ");
            w.write(escaped_name);
            w.write(".termination");
            // Type params (explicit in termination function, implicit [BEq]/[Inhabited] auto-resolved)
            for tp in &func.signature.type_params {
                w.write(" ");
                w.write(&escape::escape_identifier(tp));
            }
            // Regular params
            for p in &func.signature.parameters {
                let param_name = escape::escape_identifier(&p.name);
                w.write(" ");
                w.write(&param_name);
            }
            w.newline();

            // decreasing_by: reference a user-provided tactic macro.
            // Dots are not allowed in Lean syntax names, so convert to underscores.
            // Prefix with module namespace to avoid cross-module tactic name clashes
            // (e.g., MoveVector.insert_while_0 vs Skip_list.insert_while_0).
            let tactic_name = format!(
                "{}_{}_decreasing",
                current_module_namespace.replace('.', "_"),
                escaped_name.replace('.', "_")
            );
            w.write("decreasing_by ");
            w.line(&tactic_name);
        } else {
            // No user-provided measure and no loop-inv annotation: emit the
            // transparent `sorry` default. The generator never GUESSES a measure
            // (no ranking-function synthesis) — a real measure is specified in
            // Lean by adding `def <name>.termination ...` (+ the decreasing macro)
            // to `Termination/<module>.lean`, which flips `has_termination_measure`
            // and switches this loop to the user-measure reference form above.
            w.line("termination_by (0 : Nat)");
            w.line("decreasing_by all_goals sorry");
        }
    }

    w.newline();
    w
}

/// Render type parameters with constraints.
fn render_type_params<W: Write>(type_params: &[String], implicit: bool, w: &mut LeanWriter<W>) {
    let (open, close) = if implicit { ("{", "}") } else { ("(", ")") };
    for tp in type_params {
        let escaped_tp = escape::escape_identifier(tp);
        w.write(" ");
        w.write(open);
        w.write(&escaped_tp);
        w.write(" : Type");
        w.write(close);

        if escaped_tp == "U" {
            w.write(" [HasRealOps ");
            w.write(&escaped_tp);
            w.write("]");
        } else {
            w.write(" [BEq ");
            w.write(&escaped_tp);
            w.write("] [Inhabited ");
            w.write(&escaped_tp);
            w.write("]");
        }
    }
}

/// Render the obligation-bundle artifacts for `.aborts` functions bundled by
/// the `decompose_aborts` pass: one `@[reducible] def <fn>.ob_k … : Prop` per
/// leaf verification condition, plus the `<fn>_none_of` theorem whose proof is
/// a direct structural term over the `MoveAbort.*_none_*` combinators — no
/// tactics, so downstream proofs `apply` the theorem and discharge the small
/// leaves. One block per bundle whose parent lives in `module_id`.
pub fn render_aborts_bundles(program: &Program, module_id: ModuleID) -> String {
    // The obligation bundles are verification artifacts; test drivers only
    // evaluate the `.aborts` body, never the `_none_of` proofs. Skip them in
    // test mode so a bundle proof that fails to type-check cannot block the
    // module (and its importing drivers) from building.
    if program.for_test {
        return String::new();
    }
    render_bundles(program, module_id, &program.aborts_bundles, false)
}

/// Render the ensures-bundle artifacts (unified-backend design §5.1, Phase
/// 3.1): `<fn>.ob_k` Prop defs plus the `<fn>_of` theorem recomposing them
/// into `<fn> args` via the `SpecEnsures.*` prelude combinators. Each theorem
/// is capped at 1M heartbeats (`set_option maxHeartbeats 1000000 in`) — the
/// per-declaration budget assertion of §5.6: a generated lemma that breaches
/// the standard ceiling fails the corpus lake build, not the client's proof
/// session.
pub fn render_ensures_bundles(program: &Program, module_id: ModuleID) -> String {
    render_bundles(program, module_id, &program.ensures_bundles, true)
}

fn render_bundles(
    program: &Program,
    module_id: ModuleID,
    bundles: &[intermediate_theorem_format::AbortsBundle],
    ensures: bool,
) -> String {
    use intermediate_theorem_format::{AbortsLeaf, AbortsProofNode};

    let mut out = String::new();
    for bundle in bundles {
        let parent = program.functions.get(&bundle.fn_id);
        if parent.module_id != module_id {
            continue;
        }
        let pname = escape::escape_identifier(&parent.name);
        let expr = |ir: &intermediate_theorem_format::IRNode| -> String {
            super::render_expression_to_string(ir, parent, program)
        };
        let param_binder = |p: &intermediate_theorem_format::Parameter| -> String {
            format!(
                " ({} : {})",
                escape::escape_identifier(&p.name),
                type_to_string_with_params(&p.param_type, program, None, None)
            )
        };

        // Obligation definitions.
        for ob in &bundle.obligations {
            let mut free: std::collections::BTreeSet<String> = std::collections::BTreeSet::new();
            match &ob.leaf {
                AbortsLeaf::GuardFalse(e)
                | AbortsLeaf::GuardTrue(e)
                | AbortsLeaf::OptionNone(e)
                | AbortsLeaf::PropHolds(e) => {
                    free.extend(e.free_vars().iter().map(|v| v.to_string()));
                }
                AbortsLeaf::RequiresHolds { args, .. }
                | AbortsLeaf::CalleeNoneUnderRequires { args, .. } => {
                    for a in args {
                        free.extend(a.free_vars().iter().map(|v| v.to_string()));
                    }
                }
            }
            for (c, _) in &ob.path {
                free.extend(c.free_vars().iter().map(|v| v.to_string()));
            }
            let uses_proof_param = parent
                .signature
                .proof_params
                .iter()
                .any(|pp| free.contains(&pp.name));

            let mut binders = String::new();
            if uses_proof_param {
                // Bind the full parent signature so verbatim hypothesis types
                // stay well-scoped.
                for p in &parent.signature.parameters {
                    binders.push_str(&param_binder(p));
                }
                for pp in &parent.signature.proof_params {
                    if free.contains(&pp.name) {
                        binders.push_str(&format!(
                            " ({} : {})",
                            pp.name,
                            proof_param_type_string(pp, parent, program)
                        ));
                    }
                }
            } else {
                for p in &ob.parameters {
                    binders.push_str(&param_binder(p));
                }
            }

            let mut body = String::new();
            for (c, pol) in &ob.path {
                body.push_str(&format!(
                    "({}) = {} →\n    ",
                    expr(c),
                    if *pol { "true" } else { "false" }
                ));
            }
            match &ob.leaf {
                AbortsLeaf::GuardFalse(e) => body.push_str(&format!("({}) = false", expr(e))),
                AbortsLeaf::GuardTrue(e) => body.push_str(&format!("({}) = true", expr(e))),
                AbortsLeaf::OptionNone(e) => body.push_str(&format!("({}) = Option.none", expr(e))),
                AbortsLeaf::PropHolds(e) => body.push_str(&format!("({})", expr(e))),
                AbortsLeaf::RequiresHolds { callee, args } => {
                    body.push_str(&format!(
                        "({})",
                        requires_instance_text(program, *callee, args, &expr)
                    ));
                }
                AbortsLeaf::CalleeNoneUnderRequires { callee, args } => {
                    let cf = program.functions.get(callee);
                    let ns = super::program_renderer::get_namespace(program, cf.module_id);
                    let mut call = format!("{}.{}", ns, escape::escape_identifier(&cf.name));
                    for a in args {
                        call.push_str(&format!(" ({})", expr(a)));
                    }
                    body.push_str(&format!(
                        "∀ (hpre__ : {}), ({} hpre__) = Option.none",
                        requires_instance_text(program, *callee, args, &expr),
                        call
                    ));
                }
            }
            out.push_str(&format!(
                "@[reducible, aborts_simp] def {}.{}{} : Prop :=\n    {}\n\n",
                pname, ob.name, binders, body
            ));
        }

        // Bundle theorem.
        let mut binders = String::new();
        for p in &parent.signature.parameters {
            binders.push_str(&param_binder(p));
        }
        for pp in &parent.signature.proof_params {
            binders.push_str(&format!(
                " ({} : {})",
                pp.name,
                proof_param_type_string(pp, parent, program)
            ));
        }
        for (k, ob) in bundle.obligations.iter().enumerate() {
            let mut free: std::collections::BTreeSet<String> = std::collections::BTreeSet::new();
            match &ob.leaf {
                AbortsLeaf::GuardFalse(e)
                | AbortsLeaf::GuardTrue(e)
                | AbortsLeaf::OptionNone(e)
                | AbortsLeaf::PropHolds(e) => {
                    free.extend(e.free_vars().iter().map(|v| v.to_string()));
                }
                AbortsLeaf::RequiresHolds { args, .. }
                | AbortsLeaf::CalleeNoneUnderRequires { args, .. } => {
                    for a in args {
                        free.extend(a.free_vars().iter().map(|v| v.to_string()));
                    }
                }
            }
            for (c, _) in &ob.path {
                free.extend(c.free_vars().iter().map(|v| v.to_string()));
            }
            let uses_proof_param = parent
                .signature
                .proof_params
                .iter()
                .any(|pp| free.contains(&pp.name));
            let mut args = String::new();
            if uses_proof_param {
                for p in &parent.signature.parameters {
                    args.push(' ');
                    args.push_str(&escape::escape_identifier(&p.name));
                }
                for pp in &parent.signature.proof_params {
                    if free.contains(&pp.name) {
                        args.push(' ');
                        args.push_str(&pp.name);
                    }
                }
            } else {
                for p in &ob.parameters {
                    args.push(' ');
                    args.push_str(&escape::escape_identifier(&p.name));
                }
            }
            binders.push_str(&format!(
                "\n    (h_ob_{} : {}.{}{})",
                k + 1,
                pname,
                ob.name,
                args
            ));
        }
        let lhs_args: String = parent
            .signature
            .parameters
            .iter()
            .map(|p| escape::escape_identifier(&p.name))
            .chain(
                parent
                    .signature
                    .proof_params
                    .iter()
                    .map(|pp| pp.name.clone()),
            )
            .map(|a| format!(" {}", a))
            .collect();

        fn pp_proof(
            pn: &AbortsProofNode,
            obs: &[intermediate_theorem_format::AbortsObligation],
            depth: usize,
        ) -> String {
            let ob_app = |k: usize| -> String {
                let mut s = format!("h_ob_{}", k + 1);
                for i in 1..=obs[k].path.len() {
                    s.push_str(&format!(" hb{}", i));
                }
                if obs[k].path.is_empty() {
                    s
                } else {
                    format!("({})", s)
                }
            };
            match pn {
                AbortsProofNode::Rfl => "rfl".to_string(),
                AbortsProofNode::OrElse(a, b) => format!(
                    "(MoveAbort.orElse_none_of {} {})",
                    pp_proof(a, obs, depth),
                    pp_proof(b, obs, depth)
                ),
                AbortsProofNode::GuardFalse { ob, rest } => format!(
                    "(MoveAbort.bite_none_of_false {} {})",
                    pp_proof(&AbortsProofNode::Leaf { ob: *ob }, obs, depth),
                    pp_proof(rest, obs, depth)
                ),
                AbortsProofNode::GuardTrue { ob, rest } => format!(
                    "(MoveAbort.bite_none_of_true {} {})",
                    pp_proof(&AbortsProofNode::Leaf { ob: *ob }, obs, depth),
                    pp_proof(rest, obs, depth)
                ),
                AbortsProofNode::BIte(t, e) => format!(
                    "(MoveAbort.bite_none_split (fun hb{} => {}) (fun hb{} => {}))",
                    depth + 1,
                    pp_proof(t, obs, depth + 1),
                    depth + 1,
                    pp_proof(e, obs, depth + 1)
                ),
                AbortsProofNode::DIte(t, e) => format!(
                    "(MoveAbort.bdite_none_split (fun hb{} => {}) (fun hb{} => {}))",
                    depth + 1,
                    pp_proof(t, obs, depth + 1),
                    depth + 1,
                    pp_proof(e, obs, depth + 1)
                ),
                AbortsProofNode::Leaf { ob } => ob_app(*ob),
                AbortsProofNode::AndBool(a, b) => format!(
                    "(SpecEnsures.and_of {} {})",
                    pp_proof(a, obs, depth),
                    pp_proof(b, obs, depth)
                ),
                AbortsProofNode::PIte(t, e) => format!(
                    "(SpecEnsures.ite_of (fun hb{} => {}) (fun hb{} => {}))",
                    depth + 1,
                    pp_proof(t, obs, depth + 1),
                    depth + 1,
                    pp_proof(e, obs, depth + 1)
                ),
                AbortsProofNode::BIteBool(t, e) => format!(
                    "(SpecEnsures.bite_eq_true_of (fun hb{} => {}) (fun hb{} => {}))",
                    depth + 1,
                    pp_proof(t, obs, depth + 1),
                    depth + 1,
                    pp_proof(e, obs, depth + 1)
                ),
                AbortsProofNode::RequiresApp { req_ob, call_ob } => {
                    format!("({} {})", ob_app(*call_ob), ob_app(*req_ob))
                }
            }
        }

        // A leaf-free bundle is a TOTAL function: its `aborts_none_of` has no
        // obligation hypotheses, i.e. it IS the callee contract. Pre-register
        // it in the `@[contract]` set (unified-backend design §5.2) so callers'
        // callee-aborts leaves close silently in `discharge_obligation`.
        if ensures {
            out.push_str(&format!(
                "set_option maxHeartbeats 1000000 in\n/-- Ensures bundle for `{p}`: the named postcondition leaves above imply\nthe full ensures face. Generated structural proof — `apply` this and\ndischarge the `ob_k` leaves. -/\ntheorem {p}_of{binders} :\n    {p}{lhs} :=\n  {proof}\n\n",
                p = pname,
                binders = binders,
                lhs = lhs_args,
                proof = pp_proof(&bundle.proof, &bundle.obligations, 0),
            ));
        } else {
            let attr = if bundle.obligations.is_empty() {
                "@[contract]\n"
            } else {
                ""
            };
            // Per-declaration heartbeat budget (§5.6) on gated packages: a
            // generated bundle theorem that breaches the standard 1M ceiling
            // fails the corpus lake build. Gate-conditional to preserve
            // byte-identity for ungated packages (whose oversized bundles
            // predate the budget assertion).
            let budget =
                if intermediate_theorem_format::analysis::decompose_aborts::contract_aborts_enabled(
                    program,
                ) {
                    "set_option maxHeartbeats 1000000 in\n"
                } else {
                    ""
                };
            out.push_str(&format!(
                "{budget}/-- Obligation bundle for `{p}`: the named verification conditions above\nimply abort-freedom. Generated structural proof — `apply` this and discharge\nthe `ob_k` leaves. -/\n{attr}theorem {p}_none_of{binders} :\n    {p}{lhs} = Option.none :=\n  {proof}\n\n",
                p = pname,
                budget = budget,
                attr = attr,
                binders = binders,
                lhs = lhs_args,
                proof = pp_proof(&bundle.proof, &bundle.obligations, 0),
            ));
        }
    }
    out
}

/// The callee's declared `requires` hypothesis (its single verbatim proof
/// param) instantiated at a call site: each callee param name is replaced,
/// whole-word, by the rendered caller-side argument. Used by the
/// `requires_leaves` leaf kinds (§5.2, deferred 2.2).
fn requires_instance_text(
    program: &Program,
    callee: FunctionID,
    args: &[intermediate_theorem_format::IRNode],
    expr: &dyn Fn(&intermediate_theorem_format::IRNode) -> String,
) -> String {
    use intermediate_theorem_format::ProofParamType;
    let cf = program.functions.get(&callee);
    assert_eq!(cf.signature.parameters.len(), args.len());
    let ProofParamType::Verbatim(text) = &cf.signature.proof_params[0].param_type else {
        panic!(
            "requires_leaves: callee `{}` proof param is not verbatim",
            cf.name
        );
    };
    let mut out = text.clone();
    for (p, a) in cf.signature.parameters.iter().zip(args) {
        out = replace_whole_word(
            &out,
            &escape::escape_identifier(&p.name),
            &format!("({})", expr(a)),
        );
    }
    out
}

fn replace_whole_word(text: &str, ident: &str, replacement: &str) -> String {
    let is_ident_char = |b: u8| b.is_ascii_alphanumeric() || b == b'_' || b == b'\'';
    let bytes = text.as_bytes();
    let mut out = String::new();
    let mut start = 0;
    while let Some(pos) = text[start..].find(ident) {
        let abs = start + pos;
        let before_ok = abs == 0 || !is_ident_char(bytes[abs - 1]);
        let after = abs + ident.len();
        let after_ok = after >= bytes.len() || !is_ident_char(bytes[after]);
        out.push_str(&text[start..abs]);
        if before_ok && after_ok {
            out.push_str(replacement);
        } else {
            out.push_str(ident);
        }
        start = after;
    }
    out.push_str(&text[start..]);
    out
}

/// Render the frame-lemma block for a world-mode value face (unified-backend
/// design §5.4, Phase 4): the `@[reducible] def <fn>.dfFootprint` key-source
/// list (callee footprints composed by substitution — call-not-copy), the
/// `<fn>.frame_thm` combinator-tree theorem over the `Prover.World.FrameDf`
/// prelude leaves, and the user-facing `<fn>.frame_df_out` corollary (plus an
/// unconditional `<fn>.frame_df` when the footprint is syntactically empty).
/// Emitted right after the def, BEFORE any `attribute [irreducible]` line.
/// Returns "" for functions without a recorded set.
pub fn render_frame_lemmas(program: &Program, func_id: FunctionID) -> String {
    use intermediate_theorem_format::analysis::frame_lemmas::FrameProofNode;

    let Some(set) = program.frame_lemmas.iter().find(|s| s.fn_id == func_id) else {
        return String::new();
    };
    let func = program.functions.get(&func_id);
    let fname = escape::escape_identifier(&func.name);
    let expr = |ir: &IRNode| -> String { super::render_expression_to_string(ir, func, program) };
    let qualified = |fid: &FunctionID| -> String {
        let f = program.functions.get(fid);
        format!(
            "{}.{}",
            super::program_renderer::get_namespace(program, f.module_id),
            escape::escape_identifier(&f.name)
        )
    };
    let tps: Vec<String> = func.signature.type_params.clone();
    let ty_arg = |t: &intermediate_theorem_format::Type| -> String {
        format!(
            "({})",
            type_to_string_with_params(t, program, None, Some(&tps))
        )
    };
    // Call-site type args for a callee reference (generated defs take their
    // type params explicitly, so footprint/frame references pass them too).
    let callee_ty_args = |type_args: &[intermediate_theorem_format::Type]| -> String {
        type_args
            .iter()
            .map(|t| format!(" {}", ty_arg(t)))
            .collect::<String>()
    };

    // Footprint expression — derived from the proof tree, so statement and
    // proof share one source of truth.
    fn fp_expr(
        node: &FrameProofNode,
        program: &Program,
        expr: &dyn Fn(&IRNode) -> String,
        qualified: &dyn Fn(&FunctionID) -> String,
        cta: &dyn Fn(&[intermediate_theorem_format::Type]) -> String,
    ) -> String {
        match node {
            FrameProofNode::Refl => "[]".to_string(),
            FrameProofNode::SetDf { uid, key, .. } | FrameProofNode::EraseDf { uid, key, .. } => {
                format!(
                    "[Prover.World.DfKey.mk (World.uidNat ({})) (Prover.World.KeyEntry.of ({}))]",
                    expr(uid),
                    expr(key)
                )
            }
            FrameProofNode::DfPreserve { .. } => "[]".to_string(),
            FrameProofNode::Callee {
                function,
                type_args,
                args,
            } => {
                let set = program
                    .frame_lemmas
                    .iter()
                    .find(|s| s.fn_id == *function)
                    .expect("callee frame set exists (checked by the analysis)");
                let callee = program.functions.get(function);
                let mut s = format!("({}.dfFootprint{}", qualified(function), cta(type_args));
                for fp in &set.footprint_params {
                    let idx = callee
                        .signature
                        .parameters
                        .iter()
                        .position(|p| p.ssa_value == fp.ssa_value)
                        .expect("footprint param is a callee param");
                    s.push_str(&format!(" ({})", expr(&args[idx])));
                }
                s.push(')');
                s
            }
            FrameProofNode::Comp(a, b)
            | FrameProofNode::ItePair(a, b)
            | FrameProofNode::BiteWorld(a, b) => format!(
                "({} ++ {})",
                fp_expr(a, program, expr, qualified, cta),
                fp_expr(b, program, expr, qualified, cta)
            ),
        }
    }

    fn proof_term(
        node: &FrameProofNode,
        program: &Program,
        expr: &dyn Fn(&IRNode) -> String,
        qualified: &dyn Fn(&FunctionID) -> String,
        ty_arg: &dyn Fn(&intermediate_theorem_format::Type) -> String,
        cta: &dyn Fn(&[intermediate_theorem_format::Type]) -> String,
    ) -> String {
        match node {
            FrameProofNode::Refl => "(Prover.World.FrameDf.refl __world)".to_string(),
            FrameProofNode::SetDf {
                key_ty,
                val_ty,
                uid,
                key,
            } => format!(
                "(World.frame_setDf {} {} ({}) ({}))",
                ty_arg(key_ty),
                ty_arg(val_ty),
                expr(uid),
                expr(key)
            ),
            FrameProofNode::EraseDf {
                key_ty,
                val_ty,
                uid,
                key,
            } => format!(
                "(World.frame_eraseDf {} {} ({}) ({}))",
                ty_arg(key_ty),
                ty_arg(val_ty),
                expr(uid),
                expr(key)
            ),
            FrameProofNode::DfPreserve { op, obj_ty } => {
                format!("({} {})", op.wrapper_lemma(), ty_arg(obj_ty))
            }
            FrameProofNode::Callee {
                function,
                type_args,
                args,
            } => {
                // Trailing `_`: the callee's world argument, inferred from
                // the goal (never rendered — WriteBack render sensitivity).
                let mut s = format!("({}.frame_thm{}", qualified(function), cta(type_args));
                for a in args {
                    s.push_str(&format!(" ({})", expr(a)));
                }
                s.push_str(" _)");
                s
            }
            FrameProofNode::Comp(a, b) => format!(
                "(Prover.World.FrameDf.comp {} {})",
                proof_term(a, program, expr, qualified, ty_arg, cta),
                proof_term(b, program, expr, qualified, ty_arg, cta)
            ),
            FrameProofNode::ItePair(a, b) => format!(
                "(Prover.World.FrameDf.ite_pair {} {})",
                proof_term(a, program, expr, qualified, ty_arg, cta),
                proof_term(b, program, expr, qualified, ty_arg, cta)
            ),
            FrameProofNode::BiteWorld(a, b) => format!(
                "(Prover.World.FrameDf.bite {} {})",
                proof_term(a, program, expr, qualified, ty_arg, cta),
                proof_term(b, program, expr, qualified, ty_arg, cta)
            ),
        }
    }

    let param_binder = |p: &intermediate_theorem_format::Parameter| -> String {
        format!(
            " ({} : {})",
            escape::escape_identifier(&p.name),
            type_to_string_with_params(&p.param_type, program, None, Some(&tps))
        )
    };
    // Type-parameter binders mirror the def convention (explicit, `[BEq]`
    // `[Inhabited]`), plus `[HasCode TyCode <tp>]` for the HasCode-constrained
    // indices (unified-backend design Phase 5, generic state ops).
    let mut tp_binders = String::new();
    let mut tp_args = String::new();
    for tp in &tps {
        let e = escape::escape_identifier(tp);
        if e == "U" {
            tp_binders.push_str(&format!(" ({e} : Type) [HasRealOps {e}]"));
        } else {
            tp_binders.push_str(&format!(" ({e} : Type) [BEq {e}] [Inhabited {e}]"));
        }
        tp_args.push(' ');
        tp_args.push_str(&e);
    }
    if let Some(idx) = program.fn_hascode_params.get(&func_id) {
        for &i in idx {
            tp_binders.push_str(&format!(
                " [HasCode TyCode {}]",
                escape::escape_identifier(&tps[i as usize])
            ));
        }
    }
    if let Some(idx) = program.fn_bagu_params.get(&func_id) {
        for &i in idx {
            tp_binders.push_str(&format!(
                " [HasCode BagU {}]",
                escape::escape_identifier(&tps[i as usize])
            ));
        }
    }
    let mut binders = tp_binders.clone();
    let mut args = tp_args.clone();
    for p in &func.signature.parameters {
        binders.push_str(&param_binder(p));
        args.push(' ');
        args.push_str(&escape::escape_identifier(&p.name));
    }
    let mut fp_binders = tp_binders.clone();
    let mut fp_args = tp_args.clone();
    for p in &set.footprint_params {
        fp_binders.push_str(&param_binder(p));
        fp_args.push(' ');
        fp_args.push_str(&escape::escape_identifier(&p.name));
    }
    let proj = if set.world_proj_snd { ".2" } else { "" };
    let budget = "set_option maxHeartbeats 1000000 in\n";

    let mut out = String::new();
    out.push_str(&format!(
        "/-- Df footprint of `{f}` (unified-backend design §5.4): the concrete key\nsources it writes, callee footprints composed by substitution. -/\n@[reducible] def {f}.dfFootprint{fpb} : List (Prover.World.DfKey TyCode) :=\n    {fp}\n\n",
        f = fname,
        fpb = fp_binders,
        fp = fp_expr(&set.proof, program, &expr, &qualified, &callee_ty_args),
    ));
    out.push_str(&format!(
        "{budget}/-- Generated frame theorem: the output world agrees with the input world on\nevery dynamic field outside `{f}.dfFootprint`. Structural combinator proof —\nno body unfolding. -/\ntheorem {f}.frame_thm{binders} :\n    Prover.World.FrameDf __world ({f}{args}){proj} ({f}.dfFootprint{fpa}) :=\n  {proof}\n\n",
        budget = budget,
        f = fname,
        binders = binders,
        args = args,
        proj = proj,
        fpa = fp_args,
        proof = proof_term(&set.proof, program, &expr, &qualified, &ty_arg, &callee_ty_args),
    ));
    out.push_str(&format!(
        "{budget}theorem {f}.frame_df_out{binders} {{K' V' : Type}} [HasCode TyCode K'] [HasCode TyCode V'] (p : Nat) (k' : K')\n    (h : Prover.World.DfKey.mk p (Prover.World.KeyEntry.of k') ∉ {f}.dfFootprint{fpa}) :\n    (Prover.World.World.getDf (({f}{args}){proj}) p k' : Option V') = Prover.World.World.getDf __world p k' :=\n  {f}.frame_thm{args} p k' h\n\n",
        budget = budget,
        f = fname,
        binders = binders,
        args = args,
        proj = proj,
        fpa = fp_args,
    ));
    if set.proof.footprint_is_empty() {
        out.push_str(&format!(
            "{budget}/-- `{f}` touches no dynamic field at all. -/\ntheorem {f}.frame_df{binders} {{K' V' : Type}} [HasCode TyCode K'] [HasCode TyCode V'] (p : Nat) (k' : K') :\n    (Prover.World.World.getDf (({f}{args}){proj}) p k' : Option V') = Prover.World.World.getDf __world p k' :=\n  {f}.frame_thm{args} p k' (by simp [{f}.dfFootprint])\n\n",
            budget = budget,
            f = fname,
            binders = binders,
            args = args,
            proj = proj,
        ));
    }
    out
}

/// Render the equation/projection lemma block for a def under the per-module
/// `irreducible_defs` gate (unified-backend design §5.3, Phase 3.2), followed
/// by the `attribute [irreducible]` line. Emitted immediately after the def
/// itself so every lemma elaborates while the def is still unfoldable; from
/// the attribute line on, tactic-level `simp [<fn>]`/defeq-on-body use fails
/// fast. Each lemma carries the 1M-heartbeat per-declaration budget (§5.6).
/// Returns "" for functions without a recorded lemma set.
pub fn render_equation_lemmas(program: &Program, func_id: FunctionID) -> String {
    let Some(set) = program.equation_lemmas.iter().find(|s| s.fn_id == func_id) else {
        return String::new();
    };
    let func = program.functions.get(&func_id);
    let fname = escape::escape_identifier(&func.name);
    let expr = |ir: &IRNode| -> String { super::render_expression_to_string(ir, func, program) };
    let mut binders = String::new();
    let mut args = String::new();
    for p in &func.signature.parameters {
        let pn = escape::escape_identifier(&p.name);
        binders.push_str(&format!(
            " ({} : {})",
            pn,
            type_to_string_with_params(&p.param_type, program, None, None)
        ));
        args.push(' ');
        args.push_str(&pn);
    }
    let budget = "set_option maxHeartbeats 1000000 in\n";
    let mut out = String::new();
    if set.unfold {
        out.push_str(&format!(
            "{budget}/-- Whole-body equation lemma (the def is `irreducible` below; rewrite with\nthis instead of unfolding). -/\ntheorem {f}.eq_body{binders} :\n    {f}{args} = ({body}) := rfl\n\n",
            budget = budget,
            f = fname,
            binders = binders,
            args = args,
            body = expr(&func.body),
        ));
    }
    if let Some((cond, then_e, else_e)) = &set.branches {
        out.push_str(&format!(
            "{budget}theorem {f}.eq_then{binders} (h : ({c}) = true) :\n    {f}{args} = ({t}) := SpecEnsures.ite_then h\n\n",
            budget = budget,
            f = fname,
            binders = binders,
            args = args,
            c = expr(cond),
            t = expr(then_e),
        ));
        out.push_str(&format!(
            "{budget}theorem {f}.eq_else{binders} (h : ({c}) = false) :\n    {f}{args} = ({e}) := SpecEnsures.ite_else h\n\n",
            budget = budget,
            f = fname,
            binders = binders,
            args = args,
            c = expr(cond),
            e = expr(else_e),
        ));
    }
    let n = set.projections.len();
    for (k, comp) in &set.projections {
        let mut proj = String::new();
        if *k == n - 1 {
            for _ in 0..(n - 1) {
                proj.push_str(".2");
            }
        } else {
            for _ in 0..*k {
                proj.push_str(".2");
            }
            proj.push_str(".1");
        }
        out.push_str(&format!(
            "{budget}theorem {f}.result_{i}{binders} :\n    ({f}{args}){proj} = ({c}) := rfl\n\n",
            budget = budget,
            f = fname,
            binders = binders,
            args = args,
            i = k + 1,
            proj = proj,
            c = expr(comp),
        ));
    }
    out.push_str(&format!("attribute [irreducible] {}\n\n", fname));
    out
}
