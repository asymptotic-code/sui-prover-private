// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Unified IR renderer - renders IR nodes to Lean syntax

use super::context::RenderCtx;
use super::type_renderer::{render_type, render_type_as_arg};
use crate::escape;
use intermediate_theorem_format::{
    BinOp, BitOp, Const, Function, IRNode, ProofParamType, QuantifierKind, StructID, Type, UnOp,
    VariableRegistry, WriteBackEdge,
};

/// True if `func` is a loop helper carrying an injected loop-invariant
/// hypothesis (`hinv`). Detected from the materialized signature proof params —
/// the single source of truth — rather than a side-table lookup.
fn is_loop_inv_helper(func: &Function) -> bool {
    func.signature
        .proof_params
        .iter()
        .any(|p| matches!(p.param_type, ProofParamType::LoopInvHook(_)))
}
use std::fmt::Write;
use std::rc::Rc;

/// Check if a function is a MoveReal operation and transform it for generic specs
/// Transform int_ops calls to built-in Int operations
///
/// Only transforms functions that are actually from the int_ops module and are
/// the runtime/pure variants (not aborts variants which need type-specific handling).
fn try_transform_int_ops_call<'a, W: Write>(
    func_name: &str,
    module_name: &str,
    args: &[IRNode],
    ctx: &mut RenderCtx<'a, W>,
    reg: &mut VariableRegistry<'a>,
) -> bool {
    // Only transform if this is actually from the int_ops module
    if !module_name.ends_with("int_ops") {
        return false;
    }

    // Transform int_ops operations to Lean's built-in Int operations
    match func_name {
        // Arithmetic - map to Int operators (built-in)
        "add" => {
            if args.len() == 2 {
                ctx.write("(");
                render(&args[0], ctx, reg);
                ctx.write(" + ");
                render(&args[1], ctx, reg);
                ctx.write(")");
                return true;
            }
        }

        "sub" => {
            if args.len() == 2 {
                ctx.write("(");
                render(&args[0], ctx, reg);
                ctx.write(" - ");
                render(&args[1], ctx, reg);
                ctx.write(")");
                return true;
            }
        }

        "mul" => {
            if args.len() == 2 {
                ctx.write("(");
                render(&args[0], ctx, reg);
                ctx.write(" * ");
                render(&args[1], ctx, reg);
                ctx.write(")");
                return true;
            }
        }

        "abs" => {
            if let Some(arg) = args.first() {
                ctx.write("Int_ops.abs ");
                render_with_parens_if_needed(arg, ctx, reg);
                return true;
            }
        }

        "neg" => {
            if let Some(arg) = args.first() {
                ctx.write("(-");
                render(arg, ctx, reg);
                ctx.write(")");
                return true;
            }
        }

        _ => {}
    }

    false
}

/// True if `node` contains a loop-invariant entry call: a `Call` to a loop
/// helper (one carrying an injected `hinv` param) whose trailing argument is the
/// `sorry` placeholder. Drives the dependent-`if` rendering.
fn contains_entry_call<W: Write>(node: &IRNode, ctx: &RenderCtx<W>) -> bool {
    node.iter().any(|n| {
        matches!(n, IRNode::Call { function, args, .. }
            if is_loop_inv_helper(ctx.program.functions.get(function))
                && matches!(args.last(), Some(IRNode::Abort { .. })))
    })
}

/// Render an IR node to Lean syntax
pub fn render<'a, W: Write>(
    ir: &IRNode,
    ctx: &mut RenderCtx<'a, W>,
    reg: &mut VariableRegistry<'a>,
) {
    match ir {
        // Atomic expressions - always inline
        IRNode::Var(name) => {
            if let Some(override_str) = ctx.var_overrides.get(name).cloned() {
                ctx.write(&override_str);
            } else {
                ctx.write(&escape::escape_identifier(name));
            }
        }

        IRNode::Const(c) => render_const(c, ctx),

        IRNode::Tuple(elems) => {
            ctx.tuple(elems.iter(), "()", |ctx, elem| render(elem, ctx, reg));
        }

        IRNode::BinOp { op, lhs, rhs } => {
            // If And/Or has a Prop-typed operand, render as ∧/∨ with = true wrapping
            // for Bool operands. This handles mixed Bool/Prop && chains in Prop functions.
            let is_prop_logic = matches!(op, BinOp::And | BinOp::Or) && {
                let lhs_prop = matches!(lhs.get_type(reg), Type::Prop);
                let rhs_prop = matches!(rhs.get_type(reg), Type::Prop);
                lhs_prop || rhs_prop
            };

            if is_prop_logic {
                let prop_sym = if matches!(op, BinOp::And) {
                    " \u{2227} "
                } else {
                    " \u{2228} "
                };
                let lhs_is_prop = matches!(lhs.get_type(reg), Type::Prop);
                let rhs_is_prop = matches!(rhs.get_type(reg), Type::Prop);

                // Wrap Bool operands with (... = true), leave Prop as-is
                if !lhs_is_prop {
                    ctx.write("(");
                }
                if needs_multiline(lhs) {
                    ctx.write("(");
                    ctx.indent(true);
                    render(lhs, ctx, reg);
                    ctx.write(")");
                    ctx.dedent(false);
                } else {
                    render_with_parens_if_needed(lhs, ctx, reg);
                }
                if !lhs_is_prop {
                    ctx.write(" = true)");
                }

                ctx.write(prop_sym);

                if needs_multiline(rhs) {
                    if !rhs_is_prop {
                        ctx.write("(");
                    }
                    ctx.write("(");
                    ctx.indent(true);
                    render(rhs, ctx, reg);
                    ctx.write(")");
                    ctx.dedent(false);
                    if !rhs_is_prop {
                        ctx.write(" = true)");
                    }
                } else {
                    if !rhs_is_prop {
                        ctx.write("(");
                    }
                    render_with_parens_if_needed(rhs, ctx, reg);
                    if !rhs_is_prop {
                        ctx.write(" = true)");
                    }
                }
            } else {
                let op_sym = binop_symbol(*op);
                let is_comparison = matches!(op, BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge);

                if is_comparison {
                    ctx.write("decide (");
                }

                if needs_multiline(rhs) {
                    render_with_parens_if_needed(lhs, ctx, reg);
                    ctx.write(op_sym);
                    ctx.write("(");
                    ctx.indent(true);
                    render(rhs, ctx, reg);
                    ctx.write(")");
                    ctx.dedent(false);
                } else {
                    render_with_parens_if_needed(lhs, ctx, reg);
                    ctx.write(op_sym);
                    render_with_parens_if_needed(rhs, ctx, reg);
                }

                if is_comparison {
                    ctx.write(")");
                }
            }
        }

        IRNode::UnOp { op, operand } => {
            match op {
                UnOp::Not => {
                    // `!` over a Bool stays `Bool.not`; over a Prop operand
                    // (a negated quantifier / connective) it is `¬`.
                    if matches!(operand.get_type(reg), Type::Prop) {
                        ctx.write("\u{00AC} ");
                    } else {
                        ctx.write("!");
                    }
                    render_with_parens_if_needed(operand, ctx, reg);
                }
                UnOp::BitNot => {
                    ctx.write("~~~");
                    render_with_parens_if_needed(operand, ctx, reg);
                }
                UnOp::Cast(bits) => {
                    // Use BoundedNat.convert to explicitly convert between different bounds
                    // Type ascription alone does not work because Lean has no Coe for this
                    ctx.write("(BoundedNat.convert ");
                    render_with_parens_if_needed(operand, ctx, reg);
                    ctx.write(&format!(" : BoundedNat (2^{}))", bits));
                }
            }
        }

        IRNode::Call {
            function,
            args,
            type_args,
        } => {
            // Loop-invariant entry call: a call to a loop helper whose trailing
            // argument is the `sorry` placeholder, being rendered inside the
            // dependent `if` that bound the branch hypothesis. Discharge the loop
            // invariant with a user `by`-macro (defined in the Termination file,
            // imported before this module; unhygienic, so it resolves the
            // in-scope `hpre`/branch hyp/`requires`/`is_preactive` at THIS
            // use-site). No proof definition is spliced into the generated code.
            // (Same-module helper; the cross-module case is not yet handled.)
            // Emit the entry `by`-macro for every loop_inv helper entry call,
            // whether or not a precondition hypothesis is in scope: for a
            // trivial/`True` loop_hyp the user macro is just `trivial`, so there
            // is no reason to fall through to the value-shaped `MoveAbort.raiseAbort`
            // (which mistypes the `Prop`-valued `hinv` slot).
            {
                let func_name = ctx.program.functions.get(function).name.clone();
                let same_module =
                    ctx.program.functions.get(function).module_id == ctx.current_module_id;
                if same_module
                    && is_loop_inv_helper(ctx.program.functions.get(function))
                    && matches!(args.last(), Some(IRNode::Abort { .. }))
                {
                    let base = func_name
                        .strip_suffix(".aborts")
                        .unwrap_or(&func_name)
                        .to_string();
                    let escaped = escape::escape_identifier(&func_name);
                    let macro_name = format!(
                        "{}_{}_entry",
                        ctx.current_module_namespace.unwrap_or("").replace('.', "_"),
                        base.replace('.', "_")
                    );
                    ctx.write("(");
                    ctx.write(&escaped);
                    for arg in &args[..args.len() - 1] {
                        ctx.write(" ");
                        render_with_parens_if_needed(arg, ctx, reg);
                    }
                    ctx.write(&format!(" (by {}))", macro_name));
                    return;
                }
            }

            let func = ctx.program.functions.get(function);
            let module = ctx.program.modules.get(func.module_id);

            // Try to transform int_ops operations to built-in Int operations
            if try_transform_int_ops_call(&func.name, &module.name, args, ctx, reg) {
                return;
            }

            let escaped_name = escape::escape_identifier(&func.name);
            // Qualify the call if we're in a different module or a variable shadows the name
            // Also don't qualify calls to functions in merged modules (they're in the same file)
            let is_same_or_merged_module = func.module_id == ctx.current_module_id
                || ctx.merged_module_ids.contains(&func.module_id);
            // Check if the name would be misinterpreted as field access on a function
            // defined in the current mutual group.
            // E.g., calling `insert.while_0.after` from inside a mutual block that
            // defines `insert.while_0` would parse as `(insert.while_0).after`.
            // Only applies when the callee is NOT itself in the mutual group.
            let callee_in_mutual = ctx
                .mutual_group_info
                .as_ref()
                .map_or(false, |(gid, _)| func.mutual_group_id == Some(*gid));
            let conflicts_with_mutual = !callee_in_mutual
                && ctx.mutual_group_func_names.iter().any(|mf_name| {
                    escaped_name.starts_with(&format!("{}.", mf_name)) && &escaped_name != mf_name
                });
            // Companion forms (`<f>.aborts`, `<f>.ensures`, ...) need
            // qualification when ANY in-scope variable matches the
            // dotted prefix — Lean would otherwise parse `split_coin.aborts`
            // as a field projection on a `split_coin` local rather than
            // as a reference to the function.
            let prefix_collides = func
                .name
                .split_once('.')
                .is_some_and(|(prefix, _)| reg.contains(prefix));
            // When the function being defined has a dotted name (e.g.
            // `val_spec.aborts`), Lean implicitly opens the dotted prefix
            // as a sub-namespace inside the body. A bare call to `ensures`
            // would then resolve to a sibling `val_spec.ensures` (if any)
            // rather than the unrelated `Prover.ensures` we wanted —
            // the prover module's natives sit alongside auto-derived
            // `<spec>.ensures` companions, so unqualified calls to those
            // natives shadow whenever the caller has the same dotted shape.
            // Force `_root_.<namespace>.<name>` so resolution starts at the
            // root and ignores the auto-opened sub-namespace.
            //
            // Two callee shapes are exempt from this forced qualification:
            //   1. Same-mutual-group callees — Lean resolves recursive
            //      mutual references by bare name during elaboration, and
            //      `_root_.` qualification can't reach a not-yet-finalized
            //      definition in the same block.
            //   2. Callees whose name shares the dotted prefix with the
            //      currently-defined function (e.g. `val_spec.aborts`
            //      calling `val_spec`, or `contains.while_0` calling its
            //      `.after`). These are exactly the calls the
            //      auto-opened sub-namespace was supposed to facilitate;
            //      `_root_` would make Lean resolve to a different
            //      function or fail.
            let current_fn_is_dotted = ctx.current_function_name.contains('.');
            let current_fn_prefix = ctx
                .current_function_name
                .split_once('.')
                .map(|(p, _)| p.to_string());
            let callee_shares_current_prefix = current_fn_prefix
                .as_deref()
                .map(|p| escaped_name == p || escaped_name.starts_with(&format!("{}.", p)))
                .unwrap_or(false);
            let force_root = (conflicts_with_mutual || current_fn_is_dotted)
                && !callee_in_mutual
                && !callee_shares_current_prefix;
            let func_name = if force_root {
                // Use _root_ to force absolute name resolution, bypassing
                // both field-access parsing and auto-opened sub-namespaces.
                let effective_module_id = ctx
                    .program
                    .spec_to_impl
                    .get(&func.module_id)
                    .copied()
                    .unwrap_or(func.module_id);
                let module = ctx.program.modules.get(effective_module_id);
                let namespace = ctx
                    .program
                    .namespace_overrides
                    .get(&effective_module_id)
                    .cloned()
                    .unwrap_or_else(|| escape::module_name_to_namespace(&module.name));
                format!("_root_.{}.{}", namespace, escaped_name)
            } else if is_same_or_merged_module
                && ctx.current_module_namespace.is_some()
                && !reg.contains(&func.name)
                && !prefix_collides
            {
                escaped_name
            } else {
                // If the function's module has been merged into another module,
                // use the target module's namespace instead of the original.
                let effective_module_id = ctx
                    .program
                    .spec_to_impl
                    .get(&func.module_id)
                    .copied()
                    .unwrap_or(func.module_id);
                let module = ctx.program.modules.get(effective_module_id);
                let namespace = ctx
                    .program
                    .namespace_overrides
                    .get(&effective_module_id)
                    .cloned()
                    .unwrap_or_else(|| escape::module_name_to_namespace(&module.name));
                format!("{}.{}", namespace, escaped_name)
            };

            // Extract and render any let bindings from arguments first
            // This handles cases where args contain Let nodes which can't be rendered inline
            let mut extracted_args = Vec::new();
            for arg in args {
                let (lets, value) = extract_lets(arg);
                for (pattern, let_value) in lets {
                    ctx.write("let ");
                    ctx.tuple(pattern.iter(), "_", |ctx, p| {
                        ctx.write(&escape::escape_identifier(p))
                    });
                    ctx.write(" := ");
                    render(&let_value, ctx, reg);
                    ctx.newline();
                    reg.register_pattern(&pattern, let_value.get_type(reg));
                }
                extracted_args.push(value);
            }

            // Pre-collect which callee params are MutableReference to avoid borrow conflicts
            let param_is_mut_ref: Vec<bool> = func
                .signature
                .parameters
                .iter()
                .map(|p| matches!(&p.param_type, Type::MutableReference(_, _)))
                .collect();

            // For cross-module field accessor calls, use dot notation (arg.field)
            // to avoid collisions with same-named local structs (e.g. Display_registry
            // has a local Display struct that shadows the imported Display.fields).
            if !is_same_or_merged_module
                && extracted_args.len() == 1
                && func.is_field_accessor().is_some_and(|(sid, fidx)| {
                    let s = ctx.program.structs.get(&sid);
                    s.fields.get(fidx).is_some_and(|f| f.name == func.name)
                })
            {
                render_with_parens_if_needed(&extracted_args[0], ctx, reg);
                let field_name = func_name.rsplit('.').next().unwrap_or(&func_name);
                ctx.write(&format!(".{}", field_name));
                return;
            }

            // Move's `default::default<T>()` lowers to Lean's typeclass method
            // `default : α`, which is 0-ary — its value is resolved via the
            // `[Inhabited α]` instance from the expected type. Skip both name
            // and type args; emit just `default`.
            // (The function is intentionally not rendered as a Lean def — see
            // `must_skip_function` in function_renderer.rs.)
            let is_typeclass_default =
                func.name == "default" && matches!(&func.body, IRNode::Tuple(v) if v.is_empty());
            if is_typeclass_default {
                ctx.write("default");
                return;
            }

            ctx.write(&func_name);
            // Single rule: every generated/native callable takes its type
            // parameters explicitly, so we always emit the type args positionally.
            for ty in type_args {
                ctx.write(" ");
                render_type_as_arg(ty, ctx);
            }
            // Detect all-fixed recursive calls: if the call target is in the
            // same mutual group and every argument is a Var matching a parameter
            // name, Lean rejects well-founded recursion ("does not take any
            // non-fixed arguments"). Wrapping an arg in `id` breaks the
            // syntactic match without changing semantics.
            // Choose the last non-Prop arg to wrap (Prop args have [Decidable]
            // constraints that break if wrapped in `id`).
            let wrap_idx_in_id: Option<usize> =
                ctx.mutual_group_info
                    .as_ref()
                    .and_then(|(group_id, param_names)| {
                        if func.mutual_group_id == Some(*group_id)
                    && extracted_args.len() == param_names.len()
                    && extracted_args.iter().zip(param_names.iter()).all(|(arg, param)| {
                        matches!(arg, IRNode::Var(name) if name.as_ref() == param.as_str())
                    })
                {
                    // Find last non-Prop parameter to wrap
                    func.signature.parameters.iter().enumerate().rev()
                        .find(|(_, p)| !matches!(p.param_type, Type::Bool))
                        .map(|(idx, _)| idx)
                        // If all params are Prop, wrap the last one anyway (rare edge case)
                        .or(Some(extracted_args.len() - 1))
                } else {
                    None
                }
                    });

            for (i, arg) in extracted_args.iter().enumerate() {
                ctx.write(" ");
                // If the argument has MutableReference type but the callee's
                // corresponding parameter does NOT, unwrap with .val
                let needs_val = if i < param_is_mut_ref.len() {
                    !param_is_mut_ref[i] && is_mutable_ref_expr(arg, ctx, reg)
                } else {
                    false
                };

                if needs_val {
                    ctx.write("(Mutable.val ");
                    render_with_parens_if_needed(arg, ctx, reg);
                    ctx.write(")");
                } else if wrap_idx_in_id == Some(i) {
                    ctx.write("(id ");
                    render_with_parens_if_needed(arg, ctx, reg);
                    ctx.write(")");
                } else {
                    render_with_parens_if_needed(arg, ctx, reg);
                }
            }
        }

        IRNode::Pack {
            struct_id,
            type_args,
            fields,
            variant_index,
        } => {
            let struct_def = ctx.program.structs.get(*struct_id);
            let module_def = ctx.program.modules.get(struct_def.module_id);
            let escaped_name = escape::escape_struct_name(&struct_def.name);

            // Qualify struct constructor like we do for types
            let qualified_name = if escape::is_lean_builtin(&struct_def.name) {
                escaped_name
            } else {
                let namespace = ctx
                    .program
                    .namespace_overrides
                    .get(&struct_def.module_id)
                    .cloned()
                    .unwrap_or_else(|| escape::module_name_to_namespace(&module_def.name));
                if ctx.current_module_namespace == Some(namespace.as_str()) {
                    escaped_name
                } else {
                    format!("{}.{}", namespace, escaped_name)
                }
            };

            // Check if this is an enum variant or regular struct
            if let Some(variant_idx) = variant_index {
                // Enum variant construction: EnumName.VariantName fields...
                let variant = struct_def
                    .variants
                    .as_ref()
                    .expect("Pack with variant_index should have variants in struct def")
                    .iter()
                    .find(|v| v.tag == *variant_idx)
                    .unwrap_or_else(|| {
                        panic!(
                            "Variant {} not found in enum {}",
                            variant_idx, struct_def.name
                        )
                    });
                let variant_name = escape::escape_identifier(&variant.name);
                ctx.write(&format!("{}.{}", qualified_name, variant_name));
            } else {
                // Regular struct construction: StructName.mk fields...
                // If there are type args, use @ to make implicit args explicit
                if !type_args.is_empty() {
                    ctx.write(&format!("@{}.mk", qualified_name));
                    for ty in type_args {
                        ctx.write(" ");
                        render_type_as_arg(ty, ctx);
                    }
                } else {
                    ctx.write(&format!("{}.mk", qualified_name));
                }
            }

            for field in fields.iter() {
                ctx.write(" ");
                render_with_parens_if_needed(field, ctx, reg);
            }

            // If struct has ghost dynamic_fields fields, append empty list defaults
            if variant_index.is_none() && fields.len() < struct_def.fields.len() {
                let ghost_count = struct_def
                    .fields
                    .iter()
                    .filter(|f| f.name == "dynamic_fields" || f.name.starts_with("dynamic_fields_"))
                    .count();
                for _ in 0..ghost_count {
                    ctx.write(" []");
                }
            }
        }

        IRNode::Field {
            struct_id,
            field_index,
            base,
        } => {
            let struct_def = ctx.program.structs.get(*struct_id);
            let field_name = &struct_def.fields[*field_index].name;

            // Use dot notation: base.field_name
            // If base is a Mutable reference, unwrap with .val first
            render_struct_base(base, ctx, reg);
            ctx.write(&format!(".{}", escape::escape_identifier(field_name)));
        }

        IRNode::Unpack {
            struct_id,
            value,
            variant_index,
        } => {
            let struct_def = ctx.program.structs.get(*struct_id);
            let struct_name = escape::escape_struct_name(&struct_def.name);

            if let Some(vi) = variant_index {
                // Enum variant unpacking: use a match to extract fields
                // Generate: match value with | Variant f1 f2 => (f1, f2)
                let variant = struct_def
                    .variants
                    .as_ref()
                    .expect("Unpack with variant_index should have variants in struct def")
                    .iter()
                    .find(|v| v.tag == *vi)
                    .unwrap_or_else(|| {
                        panic!("Variant {} not found in enum {}", vi, struct_def.name)
                    });
                let variant_name = escape::escape_identifier(&variant.name);

                // Get qualified enum name
                let module_def = ctx.program.modules.get(struct_def.module_id);
                let qualified_name = if escape::is_lean_builtin(&struct_def.name) {
                    struct_name.clone()
                } else {
                    let namespace = ctx
                        .program
                        .namespace_overrides
                        .get(&struct_def.module_id)
                        .cloned()
                        .unwrap_or_else(|| escape::module_name_to_namespace(&module_def.name));
                    if ctx.current_module_namespace == Some(namespace.as_str()) {
                        struct_name.clone()
                    } else {
                        format!("{}.{}", namespace, struct_name)
                    }
                };

                if variant.fields.is_empty() {
                    // No fields to extract, just return unit
                    ctx.write("()");
                } else {
                    // Generate field binding names
                    let field_bindings: Vec<String> = variant
                        .fields
                        .iter()
                        .enumerate()
                        .map(|(i, _)| format!("_unpack_f{}", i))
                        .collect();

                    ctx.write("(match ");
                    // If value is a mutable reference, unwrap with .val first
                    render_struct_base(value, ctx, reg);
                    ctx.write(" with | ");
                    ctx.write(&format!("{}.{}", qualified_name, variant_name));
                    for binding in &field_bindings {
                        ctx.write(" ");
                        ctx.write(binding);
                    }
                    ctx.write(" => ");
                    if field_bindings.len() == 1 {
                        ctx.write(&field_bindings[0]);
                    } else {
                        ctx.write("(");
                        ctx.sep_with(", ", field_bindings.iter(), |ctx, b| ctx.write(b));
                        ctx.write(")");
                    }
                    // Add wildcard case for exhaustiveness (unreachable in practice)
                    ctx.write(" | _ => default)");
                }
                return;
            } else {
                // Regular struct unpacking: use field accessors.
                // Skip ghost fields (e.g. dynamic_fields) that were added to the IR struct
                // but don't correspond to bytecode temporaries.
                let real_fields: Vec<_> = struct_def
                    .fields
                    .iter()
                    .filter(|f| f.name != "dynamic_fields")
                    .collect();
                ctx.write("(");
                ctx.sep_with(", ", real_fields.iter(), |ctx, field| {
                    ctx.write(&struct_name);
                    ctx.write(".");
                    ctx.write(&escape::escape_identifier(&field.name));
                    ctx.write(" ");
                    render_with_parens_if_needed(value, ctx, reg);
                });
                ctx.write(")");
            }
        }

        IRNode::UpdateField {
            base,
            struct_id,
            field_index,
            value,
        } => {
            // Detect a stale UID-slot write produced by post-Phase-2
            // optimization. After Phase 2 rewrites a `borrow_mut(&mut p.id, k)`
            // into a `MutableBorrow` anchored on `p` itself, the original
            // bytecode-level "write the threaded-back UID into p.id"
            // step becomes redundant — a subsequent mutable_threading /
            // temp_inlining pass can substitute the dyn-fields reconstruction
            // (which already produces the parent struct) into the outer
            // UpdateField's value slot. The result is
            // `UpdateField(p, id, UpdateField(p, dynamic_fields_N, ...))`
            // where the outer assigns a struct value into a UID slot
            // (type-broken). When we see this exact shape — outer field
            // is a UID slot of struct S, value is itself an UpdateField on
            // the same struct S with the same base — drop the outer wrap
            // and render the inner reconstruction directly. The inner
            // already produces the new parent value.
            let struct_def = ctx.program.structs.get(*struct_id);
            let outer_field_is_id = struct_def
                .fields
                .get(*field_index)
                .map(|f| f.name == "id")
                .unwrap_or(false);
            let value_is_inner_struct_update = matches!(
                value.as_ref(),
                IRNode::UpdateField {
                    base: inner_base,
                    struct_id: inner_struct_id,
                    ..
                } if *inner_struct_id == *struct_id
                    && **inner_base == **base
            );
            if outer_field_is_id && value_is_inner_struct_update {
                render(value, ctx, reg);
            } else {
                let field_name = &struct_def.fields[*field_index].name;
                ctx.write("{ ");
                // If base is a Mutable reference, unwrap with .val first
                render_struct_base(base, ctx, reg);
                ctx.write(&format!(" with {} := ", field_name));
                render(value, ctx, reg);
                ctx.write(" }");
            }
        }

        IRNode::UpdateVec { base, index, value } => {
            render(base, ctx, reg);
            ctx.write(".set ");
            render_with_parens_if_needed(index, ctx, reg);
            ctx.write(" ");
            render_with_parens_if_needed(value, ctx, reg);
        }

        IRNode::MutableBorrow {
            val_expr,
            reconstruct_param,
            reconstruct_expr,
            state_type,
        } => {
            // Render as: Mutable.mk val_expr (fun param => (reconstruct_expr : state_type))
            // Using Mutable.mk explicitly avoids type inference issues with anonymous structs
            ctx.write("Mutable.mk ");
            render_with_parens_if_needed(val_expr, ctx, reg);
            ctx.write(" (fun ");
            ctx.write(&escape::escape_identifier(reconstruct_param));
            ctx.write(" => (");
            render_with_parens_if_needed(reconstruct_expr, ctx, reg);
            ctx.write(" : ");
            render_type(state_type, ctx);
            ctx.write("))");
        }

        IRNode::ReadRef(inner) => {
            // Add Mutable.val when the inner expression is a Mutable wrapper:
            // - MutableBorrow nodes directly create Mutable structs
            // - Variables with MutableReference type are Mutable-wrapped params
            // Use explicit Mutable.val instead of .val to avoid namespace collisions
            // (e.g., Config.Config.val when the struct name matches the namespace)
            let needs_val = matches!(inner.as_ref(), IRNode::MutableBorrow { .. })
                || is_mutable_ref_expr(inner, ctx, reg);
            if needs_val {
                ctx.write("(Mutable.val ");
                render_with_parens_if_needed(inner, ctx, reg);
                ctx.write(")");
            } else {
                render_with_parens_if_needed(inner, ctx, reg);
            }
        }

        IRNode::WriteRef { reference, value } => {
            // WriteRef updates a Mutable's value without triggering write-back.
            // Write-back happens at Destroy time via Mutable.apply.
            // Renders as: Mutable.set ref val
            let is_mut_borrow = matches!(reference.as_ref(), IRNode::MutableBorrow { .. });
            let is_mut_ref = is_mutable_ref_expr(reference, ctx, reg);
            if is_mut_borrow || is_mut_ref {
                ctx.write("Mutable.set ");
                render_with_parens_if_needed(reference, ctx, reg);
                ctx.write(" ");
                render_with_parens_if_needed(value, ctx, reg);
            } else {
                // Non-Mutable WriteRef: render as `()` to preserve Let-chain structure
                ctx.write("()");
            }
        }

        // Non-atomic expressions - multi-line
        // Iteratively walk Let chains to avoid stack overflow on deep nesting.
        IRNode::Let { .. } => {
            let mut current = ir;
            while let IRNode::Let {
                pattern,
                value,
                body,
            } = current
            {
                // WriteRef renders as `Mutable.set ref val` or `()`.
                // Wrap it in a normal Let binding: `let pattern := expr`.
                //
                // Special case: when the upstream `fix_writeref_empty_patterns`
                // pass rewrote `Let([], WriteRef { ref: Var(X) })` into
                // `Let([X], WriteRef { ref: Var(X) })` so a Mutable
                // `Mutable.set` chain rebinds X correctly, but X turns
                // out NOT to be a Mutable at this point (e.g. demoted by
                // mutable_threading), the WriteRef renders as `()` and
                // we'd produce `let X := ()`, rebinding X to `PUnit`
                // and breaking every later use of X. Detect that shape
                // (single-var pattern matching the WriteRef's reference,
                // reference is non-Mutable) and discard the pattern so
                // we emit `let _ := ()` instead. The Mutable case is
                // unaffected.
                if let IRNode::WriteRef { reference, .. } = value.as_ref() {
                    let writeref_renders_unit =
                        !matches!(reference.as_ref(), IRNode::MutableBorrow { .. })
                            && !is_mutable_ref_expr(reference, ctx, reg);
                    let pattern_matches_ref = pattern.len() == 1
                        && matches!(reference.as_ref(), IRNode::Var(v) if v == &pattern[0]);
                    let drop_pattern = writeref_renders_unit && pattern_matches_ref;
                    let effective_pattern: &[Rc<str>] = if drop_pattern {
                        &[]
                    } else {
                        pattern.as_slice()
                    };
                    ctx.write("let ");
                    ctx.tuple(effective_pattern.iter(), "_", |ctx, p| {
                        ctx.write(&escape::escape_identifier(p))
                    });
                    ctx.write(" := ");
                    render(value, ctx, reg);
                    ctx.newline();
                    current = body;
                    continue;
                }

                // WriteBack: rebinds the parent variable with write-back from child.
                // The bytecode has empty dests, so pattern is normally [] and we
                // bind the `parent` name. But `distinguish_param_rebinds_in_ensures`
                // may set a non-empty pattern (a fresh `<p>_post` name) so the
                // post-state rebind does not shadow the parameter — honor it.
                if let IRNode::WriteBack { parent, .. } = value.as_ref() {
                    ctx.write("let ");
                    match pattern.first() {
                        Some(name) => ctx.write(&escape::escape_identifier(name)),
                        // In an `.aborts` body the reconstructed parent value is
                        // never returned (the body yields `Option MoveAbort`), and
                        // rebinding the receiver to `Mutable.apply child` mistypes
                        // it (the child is a borrowed sub-struct, not the parent).
                        // Discard the reconstruction so the receiver keeps its
                        // original (correct) type for later abort-side field reads.
                        None if ctx.current_function_name.ends_with(".aborts") => ctx.write("_"),
                        None => ctx.write(&escape::escape_identifier(parent)),
                    }
                    ctx.write(" := ");
                    render(value, ctx, reg);
                    ctx.newline();
                    if let Some(name) = pattern.first() {
                        if reg.contains(parent) {
                            let ty = reg.get_type(parent).clone();
                            reg.register(name.clone(), ty);
                        }
                    }
                    current = body;
                    continue;
                }

                // If the value is a Let containing Lets, we need to extract them
                // to avoid malformed Lean syntax like `let x := let y := v`
                let (extracted_lets, final_value) = extract_lets(value);

                // Render extracted lets first.
                //
                // Same `let X := WriteRef -> ()` rebind hazard as on the
                // outer Let above: if `extract_lets` lifted out a
                // `Let([X], WriteRef { ref: Var(X) })` whose reference is
                // not Mutable at this point in the chain, the WriteRef
                // would render as `()` and we'd produce `let X := ()`,
                // pinning X to PUnit and breaking every later use.
                // Drop the pattern in that exact case.
                for (inner_pattern, inner_value) in extracted_lets {
                    let writeref_info = if let IRNode::WriteRef { reference, .. } = &inner_value {
                        let ref_node = reference.as_ref();
                        let renders_unit = !matches!(ref_node, IRNode::MutableBorrow { .. })
                            && !is_mutable_ref_expr(ref_node, ctx, reg);
                        let pattern_matches_ref = inner_pattern.len() == 1
                            && matches!(ref_node, IRNode::Var(v) if v == &inner_pattern[0]);
                        Some((ref_node.clone(), renders_unit, pattern_matches_ref))
                    } else {
                        None
                    };
                    let drop_inner_pattern = writeref_info
                        .as_ref()
                        .map(|(_, renders_unit, matches_ref)| *renders_unit && *matches_ref)
                        .unwrap_or(false);
                    let effective_inner_pattern: &[Rc<str>] = if drop_inner_pattern {
                        &[]
                    } else {
                        inner_pattern.as_slice()
                    };
                    ctx.write("let ");
                    ctx.tuple(effective_inner_pattern.iter(), "_", |ctx, p| {
                        ctx.write(&escape::escape_identifier(p))
                    });
                    ctx.write(" := ");
                    render(&inner_value, ctx, reg);
                    ctx.newline();
                    if !drop_inner_pattern {
                        // For a Mutable WriteRef (`let X := Mutable.set X v`),
                        // the new X has the SAME type as the reference
                        // (Mutable α State). The IR's `WriteRef::get_type`
                        // returns just `State` (the parent type), which
                        // would mis-register X as the bare struct and
                        // strip the `Mutable.val` wrap from later field
                        // accesses (manifesting as `Invalid field
                        // 'Mutable.<field>'` errors at lake-build time).
                        // Use the reference's type instead.
                        let pattern_type = if let Some((ref_node, renders_unit, _)) = &writeref_info
                        {
                            if !*renders_unit {
                                ref_node.get_type(reg)
                            } else {
                                inner_value.get_type(reg)
                            }
                        } else {
                            inner_value.get_type(reg)
                        };
                        reg.register_pattern(&inner_pattern, pattern_type);
                    }
                }

                // If final_value is WriteRef, render as normal Let binding
                if matches!(final_value, IRNode::WriteRef { .. }) {
                    ctx.write("let ");
                    ctx.tuple(pattern.iter(), "_", |ctx, p| {
                        ctx.write(&escape::escape_identifier(p))
                    });
                    ctx.write(" := ");
                    render(&final_value, ctx, reg);
                    ctx.newline();
                    current = body;
                    continue;
                }

                // For multi-element patterns where at least one is not `_` and the value is
                // not a tuple literal, split into an intermediate binding + projections.
                // This makes bound variables transparent (simple let-assignments via projections),
                // which is required for termination proofs: in decreasing_by, Lean's zetaDelta
                // can inline the projection definitions, making the relationship between
                // destructured and original variables visible to tactics like simp/split/rfl.
                // Pattern match destructuring (let (a,b,c) := expr) creates opaque match
                // variables with no attached definitions, losing this information.
                let non_discard: Vec<&Rc<str>> =
                    pattern.iter().filter(|p| p.as_ref() != "_").collect();
                if pattern.len() >= 2
                    && !non_discard.is_empty()
                    && !matches!(&final_value, IRNode::Tuple(_))
                {
                    // Build pair name from non-discarded variables
                    let pair_name: Rc<str> = Rc::from(
                        format!(
                            "__pair_{}",
                            non_discard
                                .iter()
                                .map(|p| p.as_ref())
                                .collect::<Vec<_>>()
                                .join("_")
                        )
                        .as_str(),
                    );
                    ctx.write("let ");
                    ctx.write(&escape::escape_identifier(&pair_name));
                    ctx.write(" := ");
                    if needs_let_value_parens(&final_value) {
                        ctx.write("(");
                        render(&final_value, ctx, reg);
                        ctx.write(")");
                    } else {
                        render(&final_value, ctx, reg);
                    }
                    ctx.newline();
                    let val_type = final_value.get_type(reg);
                    let elem_types = if let Type::Tuple(elems) = &val_type {
                        Some(elems.clone())
                    } else {
                        None
                    };
                    let n = pattern.len();
                    for (idx, p) in pattern.iter().enumerate() {
                        if p.as_ref() == "_" {
                            continue;
                        }
                        ctx.write("let ");
                        ctx.write(&escape::escape_identifier(p));
                        ctx.write(" := ");
                        ctx.write(&escape::escape_identifier(&pair_name));
                        ctx.write(&tuple_projection_path(idx, n));
                        ctx.newline();
                        if let Some(ref elems) = elem_types {
                            if idx < elems.len() {
                                reg.register(p.clone(), elems[idx].clone());
                            }
                        }
                    }
                    current = body;
                    continue;
                }

                // Default: render as tuple pattern
                ctx.write("let ");
                ctx.tuple(pattern.iter(), "_", |ctx, p| {
                    ctx.write(&escape::escape_identifier(p))
                });
                // Add type annotation when value is `default` and pattern is a single
                // variable with a known type — Lean needs it to infer the Inhabited instance.
                if matches!(&final_value, IRNode::Var(v) if v.as_ref() == "default")
                    && pattern.len() == 1
                {
                    if reg.contains(&pattern[0]) {
                        let ty = reg.get_type(&pattern[0]).clone();
                        ctx.write(" : ");
                        render_type(&ty, ctx);
                    }
                }
                write_update_field_type_annotation(&final_value, pattern, ctx, reg);
                ctx.write(" := ");
                if needs_let_value_parens(&final_value) {
                    ctx.write("(");
                    render(&final_value, ctx, reg);
                    ctx.write(")");
                } else {
                    render(&final_value, ctx, reg);
                }
                // When a Let pattern rebinds a variable that has an active var_override,
                // clear the override — inner bindings shadow the outer name in Lean.
                // (The if-branch save/restore in If rendering handles cross-branch scoping.)
                for p in pattern.iter() {
                    ctx.var_overrides.remove(p);
                }
                // Update scope-aware variable type for the bound pattern.
                reg.register_pattern(pattern, final_value.get_type(reg));
                ctx.newline();
                current = body;
            }
            // Render the final non-Let tail
            if is_empty_block(current) || body_ends_with_empty(current) {
                ctx.write("()");
            } else {
                render(current, ctx, reg);
            }
        }

        IRNode::If {
            cond,
            then_branch,
            else_branch,
        } => {
            // Loop-invariant entry cascade: if a branch holds a loop-helper entry
            // call (a `sorry` placeholder to discharge), render a DEPENDENT
            // `if h : cond = true then … else …` so the branch fact `h` is in
            // scope for the entry proof. `entry_hyp` is set while rendering the
            // branch that contains the entry call.
            let then_entry = contains_entry_call(then_branch, ctx);
            let else_entry = contains_entry_call(else_branch, ctx);
            let dep_hyp = if then_entry || else_entry {
                // Stable name so the user's entry `by`-macro (in the Termination
                // file, resolved at this use-site) can reference the branch fact.
                ctx.entry_hyp_counter += 1;
                Some(format!("h_entry_{}", ctx.entry_hyp_counter - 1))
            } else {
                None
            };

            ctx.write("if ");
            if let Some(h) = &dep_hyp {
                ctx.write(h);
                ctx.write(" : ");
            }
            render(cond, ctx, reg);
            if dep_hyp.is_some() {
                ctx.write(" = true");
            }
            ctx.write(" then");
            ctx.indent(true);
            // Save var_overrides and registry before then-branch.
            // The else-branch needs the same state as the then-branch started with,
            // since rebindings in the then-branch shouldn't affect the else-branch.
            let saved_overrides = if ctx.var_overrides.is_empty() {
                None
            } else {
                Some(ctx.var_overrides.clone())
            };
            let saved_reg = reg.clone();
            let saved_entry_hyp = ctx.entry_hyp.clone();
            if then_entry {
                ctx.entry_hyp = dep_hyp.clone();
            }
            render_if_branch(then_branch, ctx, reg);
            ctx.entry_hyp = saved_entry_hyp.clone();
            ctx.dedent(false);
            ctx.newline();
            ctx.write("else");
            ctx.indent(true);
            if let Some(overrides) = saved_overrides {
                ctx.var_overrides = overrides;
            }
            *reg = saved_reg.clone();
            if else_entry {
                ctx.entry_hyp = dep_hyp.clone();
            }
            render_if_branch(else_branch, ctx, reg);
            ctx.entry_hyp = saved_entry_hyp;
            ctx.dedent(false);
            *reg = saved_reg;
        }

        IRNode::BitOp(bit_op) => {
            match bit_op {
                BitOp::Extract { high, low, operand } => {
                    // Extract bits by shifting right and masking
                    // (operand >>> low) &&& ((1 <<< (high - low + 1)) - 1)
                    let width = high - low + 1;
                    ctx.write("((");
                    render_with_parens_if_needed(operand, ctx, reg);
                    // Use UInt8 for shift amount to satisfy Lean's type requirements
                    ctx.write(&format!(") >>> ({} : UInt8))", low));
                    if width < 32 {
                        // Mask to extract only the relevant bits
                        let mask = (1u64 << width) - 1;
                        ctx.write(&format!(" &&& {}", mask));
                    }
                }
                BitOp::Concat { high, low } => {
                    // Concat: (high <<< low_width) ||| low
                    // For now, just render as a tuple representation
                    ctx.write("(");
                    render_with_parens_if_needed(high, ctx, reg);
                    ctx.write(", ");
                    render_with_parens_if_needed(low, ctx, reg);
                    ctx.write(")");
                }
                BitOp::ZeroExtend { operand, .. } => {
                    // Zero extension is implicit in Lean's type coercion
                    render_with_parens_if_needed(operand, ctx, reg);
                }
                BitOp::SignExtend { operand, .. } => {
                    // Sign extension needs explicit handling
                    // For now, just render the operand
                    render_with_parens_if_needed(operand, ctx, reg);
                }
            }
        }

        IRNode::Quantifier {
            kind,
            callback,
            lambda_param,
            lambda_type,
            collection,
            range,
        } => {
            // `forall!`/`exists!` over a type are Prop → native Lean `∀`/`∃`,
            // provable with ordinary intro/elim. No opaque fallback. The other
            // kinds (`any`/`all`/`map`/...) fold over a concrete list and are
            // genuinely computable Bool/data, so they keep their helpers.
            if matches!(kind, QuantifierKind::Forall | QuantifierKind::Exists) {
                render_quantifier_native(ir, ctx, reg);
                return;
            }
            let helper_name = match kind {
                // Forall/Exists are handled natively above and never reach here.
                QuantifierKind::Forall | QuantifierKind::Exists => {
                    unreachable!("Forall/Exists render as native ∀/∃")
                }
                QuantifierKind::Any => "spec_any",
                QuantifierKind::AnyRange => "spec_any_range",
                QuantifierKind::All => "spec_all",
                QuantifierKind::AllRange => "spec_all_range",
                QuantifierKind::FindIndex => "spec_find_index",
                QuantifierKind::FindIndexRange => "spec_find_index_range",
                QuantifierKind::RangeMap => "spec_range_map",
                QuantifierKind::Map => "spec_map",
                QuantifierKind::MapRange => "spec_map_range",
                QuantifierKind::Filter => "spec_filter",
                QuantifierKind::FilterRange => "spec_filter_range",
                QuantifierKind::Count => "spec_count",
                QuantifierKind::CountRange => "spec_count_range",
                QuantifierKind::Find => "spec_find",
                QuantifierKind::FindRange => "spec_find_range",
                QuantifierKind::FindIndices => "spec_find_indices",
                QuantifierKind::FindIndicesRange => "spec_find_indices_range",
                QuantifierKind::SumMap => "spec_sum_map",
                QuantifierKind::SumMapRange => "spec_sum_map_range",
                QuantifierKind::RangeCount => "spec_range_count",
                QuantifierKind::RangeSumMap => "spec_range_sum_map",
            };
            let is_find_index = matches!(
                kind,
                QuantifierKind::FindIndex
                    | QuantifierKind::FindIndexRange
                    | QuantifierKind::Find
                    | QuantifierKind::FindRange
            );
            if is_find_index {
                ctx.write("\u{27E8}");
            }
            ctx.write(helper_name);
            // Emit range args if present: start end
            if let Some((start, end)) = range {
                ctx.write(" ");
                render_with_parens_if_needed(start, ctx, reg);
                ctx.write(" ");
                render_with_parens_if_needed(end, ctx, reg);
            }
            // Emit collection arg if present
            if let Some(coll) = collection {
                ctx.write(" ");
                render_with_parens_if_needed(coll, ctx, reg);
            }
            // Emit lambda: (fun param => callback_body)
            ctx.write(" (fun ");
            ctx.write(&escape::escape_identifier(lambda_param));
            ctx.write(" => ");
            reg.register(lambda_param.clone(), lambda_type.clone());
            render(callback, ctx, reg);
            ctx.write(")");
            if is_find_index {
                ctx.write("\u{27E9}");
            }
        }

        IRNode::ToProp(inner) => {
            // Bool → Prop coercion `(expr = true)`. If the inner is already a
            // Prop (e.g. a native `∀`/`∃` or a logical connective), render it
            // directly — there is nothing to coerce.
            if matches!(inner.get_type(reg), Type::Prop) {
                render_with_parens_if_needed(inner, ctx, reg);
            } else {
                ctx.write("(");
                render_with_parens_if_needed(inner, ctx, reg);
                ctx.write(" = true)");
            }
        }

        IRNode::ToBool(inner) => {
            // ToBool nodes are no longer generated (bool_coercion pass removed).
            // If one appears, just render the inner expression directly.
            render(inner, ctx, reg);
        }

        IRNode::Match { scrutinee, cases } => {
            let scrutinee_type = scrutinee.get_type(reg);
            let inner_type = match &scrutinee_type {
                Type::Reference(inner) => inner.as_ref().clone(),
                Type::MutableReference(inner, _) => inner.as_ref().clone(),
                t => t.clone(),
            };
            let (struct_id, enum_def) = match inner_type {
                Type::Struct { struct_id, .. } => {
                    let s = ctx.program.structs.get(&struct_id);
                    if s.variants.is_some() {
                        (struct_id, s)
                    } else {
                        panic!("Match scrutinee type {:?} is not an enum", s.name);
                    }
                }
                Type::TypeParameter(_) => {
                    ctx.write("sorry");
                    return;
                }
                _ => panic!(
                    "Match scrutinee should have enum type, got {:?}",
                    scrutinee_type
                ),
            };

            let variants = enum_def
                .variants
                .as_ref()
                .expect("Enum should have variants");

            // Get qualified enum name
            let module_def = ctx.program.modules.get(enum_def.module_id);
            let escaped_name = escape::escape_struct_name(&enum_def.name);
            let qualified_name = if escape::is_lean_builtin(&enum_def.name) {
                escaped_name
            } else {
                let namespace = ctx
                    .program
                    .namespace_overrides
                    .get(&enum_def.module_id)
                    .cloned()
                    .unwrap_or_else(|| escape::module_name_to_namespace(&module_def.name));
                if ctx.current_module_namespace == Some(namespace.as_str()) {
                    escaped_name
                } else {
                    format!("{}.{}", namespace, escaped_name)
                }
            };

            ctx.write("match ");
            render(scrutinee, ctx, reg);
            ctx.write(" with");

            for (variant_tag, bindings, body) in cases {
                let variant = variants
                    .iter()
                    .find(|v| v.tag == *variant_tag)
                    .unwrap_or_else(|| {
                        panic!(
                            "Variant {} not found in enum {}",
                            variant_tag, enum_def.name
                        )
                    });
                let variant_name = escape::escape_identifier(&variant.name);

                ctx.indent(true);
                ctx.write(&format!("| {}.{}", qualified_name, variant_name));

                // Render bindings for variant fields
                // If bindings are provided, use them; otherwise use wildcards for all fields
                if bindings.is_empty() {
                    for _ in &variant.fields {
                        ctx.write(" _");
                    }
                } else {
                    for binding in bindings {
                        ctx.write(" ");
                        ctx.write(&escape::escape_identifier(binding));
                    }
                }

                ctx.write(" =>");
                ctx.indent(true);
                render_if_branch(body, ctx, reg);
                ctx.dedent(false);
                ctx.dedent(false);
            }
        }

        IRNode::OptionSome(inner) => {
            // Qualify with `Option.` so the constructor resolves to
            // `_root_.Option.some` even inside namespaces that shadow the
            // bare `some` (notably `MoveOption`, which has its own `def
            // some : ... → MoveOption tv0` matching the Move source).
            ctx.write("Option.some ");
            render_with_parens_if_needed(inner, ctx, reg);
        }

        IRNode::OptionNone => {
            ctx.write("Option.none");
        }

        IRNode::MatchOption {
            scrutinee,
            binding,
            some_branch,
            none_branch,
        } => {
            ctx.write("match ");
            render(scrutinee, ctx, reg);
            ctx.write(" with");
            ctx.indent(true);
            // Qualify with `Option.` for the same reason as `OptionSome`
            // / `OptionNone` above — bare `some`/`none` would resolve to
            // namespace-local defs in modules like `MoveOption` and Lean
            // would reject them as patterns (they're `def`s, not
            // constructors).
            ctx.write(&format!(
                "| Option.some {} =>",
                escape::escape_identifier(binding)
            ));
            ctx.indent(true);
            render_if_branch(some_branch, ctx, reg);
            ctx.dedent(false);
            ctx.newline();
            ctx.write("| Option.none =>");
            ctx.indent(true);
            render_if_branch(none_branch, ctx, reg);
            ctx.dedent(false);
            ctx.dedent(false);
        }

        IRNode::Inhabited => {
            ctx.write("default");
        }

        IRNode::Abort { code } => {
            // Spec rendering: an `abort` inhabits any return type via
            // `sorry`. The `--test` pipeline routes abort observation
            // through Option-shape `.aborts` companions, but the
            // impl-side body still contains the abort site — when a
            // test directly evaluates the body (via the per-test driver
            // calling the impl, not the `.aborts`), reaching `sorry`
            // panics the Lean executable with `INTERNAL PANIC: executed
            // 'sorry'`. In test mode emit `MoveAbort.raiseAbort` instead;
            // it panics with a parseable stderr message the driver picks
            // up to convert into a structured abort verdict.
            //
            // The module argument is the Move `<package>::<module>` of
            // the function containing the `abort`; the per-test driver
            // uses it to report abort origin so `#[expected_failure(
            // abort_code=N, location=<module>)]` annotations check
            // against the right module.
            ctx.write("MoveAbort.raiseAbort ");
            if let Some(code) = code {
                render_with_parens_if_needed(code, ctx, reg);
                ctx.write(".toNat");
            } else {
                ctx.write("0");
            }
            ctx.write(" MoveAbort.AbortSource.userAssert ");
            let module = ctx.program.modules.get(ctx.current_module_id);
            ctx.write(&format!("\"{}::{}\"", module.package_name, module.name));
        }

        IRNode::WriteBack {
            child,
            parent,
            edge,
        } => {
            let parent_is_mutable = reg.contains(parent)
                && matches!(reg.get_type(parent), Type::MutableReference(_, _));
            let child_is_mutable =
                reg.contains(child) && matches!(reg.get_type(child), Type::MutableReference(_, _));

            // `WriteBackEdge::Field` is the field-reconstruct form. The
            // IR translator only emits it for the Reserve / Asset family
            // (Hyper(DF, Index) where the parent's UID was BorrowField'd
            // earlier in the same block). For wrapper functions like
            // `Bag.borrow_mut` whose Lean result is already
            // `Mutable<V, ParentStruct>`, the translator stays on
            // `WriteBackEdge::Direct` and we fall through to the legacy
            // `Mutable.apply child` rendering below.
            //
            // After dynamic-field rewriting (Phase 1), a borrow_mut on
            // `parent.id` is replaced with a `MutableBorrow` whose
            // reconstruct produces the parent struct directly — so the
            // child's anchor type is the parent struct, not its `id`
            // field's type. The pre-existing `WriteBackEdge::Field
            // { parent_struct, id_index }` becomes redundant: applying
            // `Mutable.apply child` already yields the full parent. Treat
            // such an edge as `Direct` so we emit `Mutable.apply child`
            // instead of the broken `{ parent with id := Mutable.apply
            // child }` (which would assign a struct value into a UID slot).
            let field_edge = if let WriteBackEdge::Field {
                struct_id,
                field_index,
            } = edge
            {
                // Two distinct collapse triggers, both producing the same
                // `Mutable.apply child` rendering:
                //
                // (1) Registry-confirmed: the child mutref's anchor matches
                //     `struct_id`, so `Mutable.apply child` already yields
                //     a fully-reconstructed parent struct. Fires for the
                //     in-function case (e.g. inside `get_asset_balance`)
                //     where Phase 1 directly rewrote the borrow_mut.
                //
                // (2) Convention-based: the edge writes into `parent.id`
                //     (a Sui `Object.UID` slot at field 0) and the parent
                //     struct has at least one ghost `dynamic_fields_*`
                //     field. After Phase 1's pre-threading rewrite, no
                //     mutref produced in our pipeline is UID-anchored —
                //     they're all anchored on parent structs. The legacy
                //     `{ parent with id := <UID> }` reconstruction was
                //     correct only when the child mutref still had a UID
                //     anchor; post-Phase-1 it never does. Fires for the
                //     cross-function case (caller destructures a
                //     `&mut Self`-returning helper into `t_tN` whose
                //     signature-level state is a placeholder).
                let registry_match = child_is_mutable
                    && matches!(
                        reg.get_type(child),
                        Type::MutableReference(_, ref state)
                            if matches!(
                                state.as_ref(),
                                Type::Struct { struct_id: sid, .. } if *sid == *struct_id
                            )
                    );
                let convention_match = {
                    let struct_def = ctx.program.structs.get(*struct_id);
                    let has_dynamic_fields = struct_def.fields.iter().any(|f| {
                        f.name == "dynamic_fields" || f.name.starts_with("dynamic_fields_")
                    });
                    let field0_is_id = *field_index == 0
                        && struct_def
                            .fields
                            .first()
                            .map(|f| f.name == "id")
                            .unwrap_or(false);
                    child_is_mutable && has_dynamic_fields && field0_is_id
                };
                if registry_match || convention_match {
                    None
                } else {
                    Some((*struct_id, *field_index))
                }
            } else {
                None
            };

            if let Some((struct_id, field_index)) = field_edge {
                let struct_def = ctx.program.structs.get(struct_id);
                let field_name = &struct_def.fields[field_index].name;
                let apply_or_id = if child_is_mutable {
                    format!("Mutable.apply {}", escape::escape_identifier(child))
                } else {
                    escape::escape_identifier(child).to_string()
                };
                if parent_is_mutable {
                    // Parent itself is a Mutable wrapper — reconstruct via
                    // `Mutable.set parent ({ Mutable.val parent with f := ... })`.
                    ctx.write("Mutable.set ");
                    ctx.write(&escape::escape_identifier(parent));
                    ctx.write(" ({ (Mutable.val ");
                    ctx.write(&escape::escape_identifier(parent));
                    ctx.write(") with ");
                    ctx.write(&escape::escape_identifier(field_name));
                    ctx.write(" := ");
                    ctx.write(&apply_or_id);
                    ctx.write(" })");
                } else {
                    ctx.write("{ ");
                    ctx.write(&escape::escape_identifier(parent));
                    ctx.write(" with ");
                    ctx.write(&escape::escape_identifier(field_name));
                    ctx.write(" := ");
                    ctx.write(&apply_or_id);
                    ctx.write(" }");
                }
            } else if parent_is_mutable && child_is_mutable {
                ctx.write("Mutable.set ");
                ctx.write(&escape::escape_identifier(parent));
                ctx.write(" (Mutable.apply ");
                ctx.write(&escape::escape_identifier(child));
                ctx.write(")");
            } else if parent_is_mutable {
                ctx.write("Mutable.set ");
                ctx.write(&escape::escape_identifier(parent));
                ctx.write(" ");
                ctx.write(&escape::escape_identifier(child));
            } else if child_is_mutable {
                ctx.write("Mutable.apply ");
                ctx.write(&escape::escape_identifier(child));
            } else {
                // Both parent and child are plain — just a variable copy
                ctx.write(&escape::escape_identifier(child));
            }
        }

        IRNode::MutableCompose { inner, outer } => {
            ctx.write("Mutable.compose ");
            ctx.write(&escape::escape_identifier(inner));
            ctx.write(" ");
            ctx.write(&escape::escape_identifier(outer));
        }

        IRNode::MoveAbortValue { source, code } => {
            let source_name = match source {
                intermediate_theorem_format::AbortSource::UserAssert => "userAssert",
                intermediate_theorem_format::AbortSource::Arithmetic => "arithmetic",
            };
            // Lean can't always infer `MoveAbort` from the surrounding
            // `Option MoveAbort` context — explicit annotation is safest.
            // The `module` field carries the Move `<package>::<module>`
            // name where the abort originated; the per-test driver
            // forwards it to the harness so `#[expected_failure(
            // location=<module>)]` annotations compare correctly.
            let module = ctx.program.modules.get(ctx.current_module_id);
            ctx.write(&format!(
                "(({{ source := MoveAbort.AbortSource.{}, code := (",
                source_name
            ));
            render(code, ctx, reg);
            ctx.write(&format!(
                ").toNat, module := \"{}::{}\" }} : MoveAbort))",
                module.package_name, module.name
            ));
        }

        IRNode::ArithOverflowCheck { op, lhs, rhs } => {
            let helper = match op {
                BinOp::Add => "BoundedNat.add_overflows",
                BinOp::Sub => "BoundedNat.sub_underflows",
                BinOp::Mul => "BoundedNat.mul_overflows",
                _ => panic!("ArithOverflowCheck only supports Add/Sub/Mul, got {:?}", op),
            };
            ctx.write("(");
            ctx.write(helper);
            ctx.write(" ");
            render_with_parens_if_needed(lhs, ctx, reg);
            ctx.write(" ");
            render_with_parens_if_needed(rhs, ctx, reg);
            ctx.write(")");
        }
    }
}

/// Extract the StructID from a match scrutinee's type.
fn scrutinee_struct_id<'a, W: Write>(
    scrutinee: &IRNode,
    ctx: &RenderCtx<'a, W>,
    reg: &VariableRegistry<'a>,
) -> StructID {
    // For Field nodes, we can directly get the struct_id from the field's type
    if let IRNode::Field {
        struct_id,
        field_index,
        ..
    } = scrutinee
    {
        let s = ctx.program.structs.get(struct_id);
        let field_type = &s.fields[*field_index].field_type;
        return extract_struct_id_from_type(field_type);
    }

    let ty = match scrutinee {
        IRNode::Var(name) => reg.get_type(name).clone(),
        other => panic!("match scrutinee must be a Var or Field, got {:?}", other),
    };
    extract_struct_id_from_type(&ty)
}

/// Extract StructID from a type, handling references
fn extract_struct_id_from_type(ty: &Type) -> StructID {
    match ty {
        Type::Struct { struct_id, .. } => *struct_id,
        Type::Reference(inner) | Type::MutableReference(inner, _) => match inner.as_ref() {
            Type::Struct { struct_id, .. } => *struct_id,
            _ => panic!(
                "match scrutinee reference inner must be Struct, got {:?}",
                inner
            ),
        },
        _ => panic!("match scrutinee must have Struct type, got {:?}", ty),
    }
}

/// Check if an IR expression has MutableReference type (is a Mutable wrapper).
/// When true, struct field access and update need `.val` to unwrap the Mutable.
fn is_mutable_ref_expr<'a, W: Write>(
    ir: &IRNode,
    ctx: &RenderCtx<'a, W>,
    reg: &VariableRegistry<'a>,
) -> bool {
    match ir {
        IRNode::Var(name) => {
            if !reg.contains(name) {
                return false;
            }
            matches!(reg.get_type(name), Type::MutableReference(_, _))
        }
        IRNode::MutableBorrow { .. } => true,
        IRNode::Call { function, .. } => {
            let func = ctx.program.functions.get(function);
            matches!(func.signature.return_type, Type::MutableReference(_, _))
        }
        _ => false,
    }
}

/// Render an expression that is used as a struct base (for field access or update).
/// If the expression has MutableReference type, uses explicit `Mutable.val` to unwrap.
fn render_struct_base<'a, W: Write>(
    ir: &IRNode,
    ctx: &mut RenderCtx<'a, W>,
    reg: &mut VariableRegistry<'a>,
) {
    let needs_val = is_mutable_ref_expr(ir, ctx, reg);
    if needs_val {
        ctx.write("(Mutable.val ");
        render_with_parens_if_needed(ir, ctx, reg);
        ctx.write(")");
    } else {
        render_with_parens_if_needed(ir, ctx, reg);
    }
}

/// Check if a Let value expression needs wrapping in parentheses.
/// Projection path for index `idx` in an n-element Lean nested pair.
/// Lean encodes (a, b, c, d) as (a, (b, (c, d))), so:
///   idx=0 → ".1", idx=1 → ".2.1" (if n>2) or ".2" (if n=2),
///   idx=2 → ".2.2.1" (if n>3) or ".2.2" (if n=3), etc.
fn tuple_projection_path(idx: usize, n: usize) -> String {
    assert!(n >= 2 && idx < n);
    if idx == 0 {
        ".1".to_string()
    } else {
        // Navigate through .2 chains: for each step past index 0,
        // we go one level deeper into the nested pair
        let mut path = String::new();
        for _ in 0..idx {
            path.push_str(".2");
        }
        // If this isn't the last element, we need a final .1
        if idx < n - 1 {
            path.push_str(".1");
        }
        path
    }
}

/// Multi-line control flow (If, Match) as Let values cause Lean parsing ambiguity
/// when the next statement also starts with a keyword like `if` or `match`.
fn needs_let_value_parens(node: &IRNode) -> bool {
    matches!(
        node,
        IRNode::If { .. } | IRNode::Match { .. } | IRNode::MatchOption { .. }
    )
}

fn render_with_parens_if_needed<'a, W: Write>(
    ir: &IRNode,
    ctx: &mut RenderCtx<'a, W>,
    reg: &mut VariableRegistry<'a>,
) {
    if ir.is_atomic() {
        render(ir, ctx, reg);
    } else {
        ctx.write("(");
        render(ir, ctx, reg);
        ctx.write(")");
    }
}

/// Render a `Forall`/`Exists` quantifier as a native Lean binder
/// `∀ (x : T), <body>` / `∃ (x : T), <body>`. The body is a proposition: a
/// nested quantifier renders natively (recursion), any other Bool predicate is
/// coerced once with `= true`. `forall!`/`exists!` are always Prop, so this is
/// the only rendering path for them — there is no opaque fallback.
fn render_quantifier_native<'a, W: Write>(
    node: &IRNode,
    ctx: &mut RenderCtx<'a, W>,
    reg: &mut VariableRegistry<'a>,
) {
    let IRNode::Quantifier {
        kind,
        callback,
        lambda_param,
        lambda_type,
        ..
    } = node
    else {
        return;
    };
    let binder = if matches!(kind, QuantifierKind::Forall) {
        "\u{2200}"
    } else {
        "\u{2203}"
    };
    ctx.write(binder);
    ctx.write(" (");
    ctx.write(&escape::escape_identifier(lambda_param));
    ctx.write(" : ");
    render_type(lambda_type, ctx);
    ctx.write("), ");
    reg.register(lambda_param.clone(), lambda_type.clone());
    // The body is a proposition: a Prop expression (nested quantifier, logical
    // connective) renders directly; a Bool predicate is coerced once `= true`.
    if matches!(callback.get_type(reg), Type::Prop) {
        render(callback, ctx, reg);
    } else {
        ctx.write("(");
        render(callback, ctx, reg);
        ctx.write(" = true)");
    }
}

/// Emit ` : <StructType>` annotation when the let-bound value is a struct
/// `UpdateField` (rendered as `{ x with field := v }`) and the pattern is a
/// single variable. Lean can't always infer the struct type from `with`
/// syntax — without the annotation, the elaborator leaves the type as a
/// metavariable, which then breaks downstream field projections.
fn write_update_field_type_annotation<W: Write>(
    value: &IRNode,
    pattern: &[Rc<str>],
    ctx: &mut RenderCtx<W>,
    reg: &VariableRegistry,
) {
    let IRNode::UpdateField { struct_id, .. } = value else {
        return;
    };
    if pattern.len() != 1 {
        return;
    }
    let struct_def = ctx.program.structs.get(*struct_id);
    let type_args = if reg.contains(&pattern[0]) {
        match reg.get_type(&pattern[0]) {
            Type::Struct {
                type_args,
                struct_id: sid,
            } if *sid == *struct_id => Some(type_args.clone()),
            _ => None,
        }
    } else {
        None
    };
    let type_args = type_args.unwrap_or_else(|| {
        (0..struct_def.type_params.len())
            .map(|i| Type::TypeParameter(i as u16))
            .collect()
    });
    ctx.write(" : ");
    render_type(
        &Type::Struct {
            struct_id: *struct_id,
            type_args,
        },
        ctx,
    );
}

/// Extract Let bindings from an IR node, returning the extracted lets and the remaining expression.
/// This is used to hoist let bindings out of argument positions where they can't be rendered inline.
/// Iterative to avoid stack overflow on deep Let chains.
fn extract_lets(ir: &IRNode) -> (Vec<(Vec<Rc<str>>, IRNode)>, IRNode) {
    let mut lets = Vec::new();
    let mut current = ir;
    while let IRNode::Let {
        pattern,
        value,
        body,
    } = current
    {
        // Check if the value itself has lets to extract (value nesting is shallow)
        let (inner_lets, inner_value) = extract_lets_value(value);
        lets.extend(inner_lets);
        lets.push((pattern.clone(), inner_value));
        current = body;
    }
    (lets, current.clone())
}

/// Extract Let bindings from a value position only (not the body chain).
/// Value nesting is typically shallow so recursion is safe here.
fn extract_lets_value(ir: &IRNode) -> (Vec<(Vec<Rc<str>>, IRNode)>, IRNode) {
    match ir {
        IRNode::Let {
            pattern,
            value,
            body,
        } => {
            let (inner_lets, inner_value) = extract_lets_value(value);
            let mut lets = inner_lets;
            lets.push((pattern.clone(), inner_value));
            let (body_lets, final_value) = extract_lets_value(body);
            lets.extend(body_lets);
            (lets, final_value)
        }
        _ => (Vec::new(), ir.clone()),
    }
}

/// Check if a node is a bare value expression that doesn't produce a Let binding.
/// These are invalid in non-last position of a let sequence.
fn is_bare_value_expression(ir: &IRNode) -> bool {
    match ir {
        IRNode::Var(_) | IRNode::Const(_) | IRNode::Tuple(_) => true,
        IRNode::BinOp { .. } | IRNode::UnOp { .. } => true,
        // Don't skip Call - they might have side effects
        _ => false,
    }
}

/// Render an if/else branch, ensuring it ends with a value expression.
/// - Empty blocks get explicit ()
/// - Blocks/Lets ending with a Let get a trailing ()
fn render_if_branch<'a, W: Write>(
    branch: &IRNode,
    ctx: &mut RenderCtx<'a, W>,
    reg: &mut VariableRegistry<'a>,
) {
    if is_empty_block(branch) {
        ctx.write("()");
    } else {
        render(branch, ctx, reg);
        if body_ends_with_let(branch) {
            ctx.newline();
            ctx.write("()");
        }
    }
}

/// Check if an IR node is an empty block (renders as nothing meaningful).
fn is_empty_block(ir: &IRNode) -> bool {
    matches!(ir, IRNode::Tuple(v) if v.is_empty())
}

/// Check if an IR body ends with an empty block.
/// Iteratively follows Let bodies to find the final expression.
fn body_ends_with_empty(ir: &IRNode) -> bool {
    let mut current = ir;
    loop {
        match current {
            IRNode::Tuple(v) if v.is_empty() => return true,
            IRNode::Let { body, .. } => current = body,
            _ => return false,
        }
    }
}

/// Check if a non-last block child needs `let _ :=` wrapping.
/// Returns true for expressions that render as bare values without their own `let` prefix.
/// Excludes: Let (already has let), WriteRef (renders with let _ := internally),
/// If/Match (valid as statements in Lean's do-notation style), and bare values (skipped entirely).
fn needs_let_discard(ir: &IRNode) -> bool {
    matches!(
        ir,
        IRNode::Call { .. }
            | IRNode::If { .. }
            | IRNode::Match { .. }
            | IRNode::MatchOption { .. }
            | IRNode::Pack { .. }
    )
}

/// Check if an expression needs multi-line rendering.
/// This is true for expressions containing Let bindings.
fn needs_multiline(ir: &IRNode) -> bool {
    match ir {
        IRNode::Let { .. } => true,
        IRNode::If {
            then_branch,
            else_branch,
            ..
        } => needs_multiline(then_branch) || needs_multiline(else_branch),
        IRNode::BinOp { lhs, rhs, .. } => needs_multiline(lhs) || needs_multiline(rhs),
        _ => false,
    }
}

fn render_const<W: Write>(c: &Const, ctx: &mut RenderCtx<W>) {
    match c {
        Const::Bool(b) => {
            // Always render as Bool true/false. When a Bool needs to be
            // lifted to Prop, the ToProp wrapper handles it (= true).
            ctx.write(if *b { "true" } else { "false" })
        }
        Const::UInt { bits, value } => {
            ctx.write(&format!("({} : BoundedNat (2^{}))", value, bits));
        }
        Const::Address(addr) => ctx.write(&addr.to_string()),
        Const::Vector { elems, elem_type } => {
            if elems.is_empty() {
                ctx.write("([] : List (");
                render_type(elem_type, ctx);
                ctx.write("))");
            } else {
                ctx.write("[");
                for (i, e) in elems.iter().enumerate() {
                    if i > 0 {
                        ctx.write(", ");
                    }
                    render_const(e, ctx);
                }
                ctx.write("]");
            }
        }
    }
}

/// Get the symbol for a binary operator.
/// All operators use their Bool/computational forms. Prop lifting is
/// handled by ToProp wrappers in the IR, not by operator selection.
fn binop_symbol(op: BinOp) -> &'static str {
    match op {
        BinOp::Add => " + ",
        BinOp::Sub => " - ",
        BinOp::Mul => " * ",
        BinOp::Div => " / ",
        BinOp::Mod => " % ",
        BinOp::BitAnd => " &&& ",
        BinOp::BitOr => " ||| ",
        BinOp::BitXor => " ^^^ ",
        BinOp::Shl => " <<< ",
        BinOp::Shr => " >>> ",
        BinOp::And => " && ",
        BinOp::Or => " || ",
        BinOp::Eq => " == ",
        BinOp::Neq => " != ",
        BinOp::Lt => " < ",
        BinOp::Le => " \u{2264} ",
        BinOp::Gt => " > ",
        BinOp::Ge => " \u{2265} ",
    }
}

/// Extract the variable name from the base expression of an UpdateField.
/// For `Var(name)`, returns Some(name). Otherwise None.
fn find_base_var_name(base: &IRNode) -> Option<&str> {
    match base {
        IRNode::Var(name) => Some(name),
        _ => None,
    }
}

fn bounded_nat_type(bits: usize) -> String {
    format!("BoundedNat (2^{})", bits)
}

/// Check if a body ends with a let-like binding (needs a continuation expression appended).
/// This includes Let nodes (whose body chain we recurse into) and WriteBack nodes.
/// WriteRef is intentionally NOT a terminal trigger here. WriteRef on a Mutable
/// renders as `Mutable.set X v` which IS a value (returns Mutable α State); a
/// trailing `()` would be a function-application syntax error in Lean. WriteRef
/// on a non-Mutable renders as `()` which itself is a value — also no
/// continuation needed. The original sequence-step shape that needed the
/// trailing `()` was always `Let([], WriteRef, body=()`, where the recursion
/// into the Let body already returns false on `Tuple([])`.
///
/// Note: If/Match nodes are NOT included because render_if_branch already handles
/// adding trailing () to branches that end with let. The If expression itself
/// always returns a complete value, so no continuation is needed after it.
pub fn body_ends_with_let(ir: &IRNode) -> bool {
    match ir {
        IRNode::Let { body, .. } => body_ends_with_let(body),
        IRNode::WriteBack { .. } => true,
        _ => false,
    }
}
