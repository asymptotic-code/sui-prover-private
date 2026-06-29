// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Renders Function to Lean syntax.
//! Dumb renderer — just emits `def name (params) : ReturnType := body` for each function.

use intermediate_theorem_format::{Function, IRNode, ModuleID, Program, ProofParam, Type};
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
pub(crate) fn proof_param_type_string(pp: &ProofParam, func: &Function) -> String {
    use intermediate_theorem_format::ProofParamType;
    match &pp.param_type {
        ProofParamType::Verbatim(s) => s.clone(),
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
pub fn render_function<W: Write>(
    func: &Function,
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
        && !func.is_native
        && !func.name.contains(".requires")
        && !func.name.contains(".ensures")
        && !func.name.contains(".asserts_cond")
        && func.signature.return_type != intermediate_theorem_format::Type::Prop
    {
        w.write("@[reducible] ");
    }
    w.write("def ");
    w.write(escaped_name);

    // All generated defs take their type parameters explicitly (`(t_tv0 : Type)`).
    // This keeps a single convention end-to-end: the call-site loop unconditionally
    // emits the matching positional type args.
    render_type_params(&func.signature.type_params, false, &mut w);

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

    // Emit {s : Type} implicits for each &mut parameter
    for p in &func.signature.parameters {
        if matches!(p.param_type, Type::MutableReference(_, _)) {
            let svar = state_var_name(mut_param_idx, mut_param_count);
            w.write(&format!(" {{{} : Type}}", svar));
            mut_param_idx += 1;
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
            let svar = state_var_name(mut_param_idx, mut_param_count);
            mut_param_idx += 1;
            type_to_string_full_with_mut(
                &p.param_type,
                program,
                Some(current_module_namespace),
                Some(&func.signature.type_params),
                Some(&svar),
            )
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
        w.write(&proof_param_type_string(pp, func));
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
