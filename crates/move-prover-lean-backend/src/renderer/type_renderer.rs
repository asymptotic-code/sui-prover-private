// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Renders TheoremType to Lean syntax.
//! Pure translation - no logic, just pattern matching.

use super::context::RenderCtx;
use crate::escape;
use intermediate_theorem_format::{Program, Type};
use std::fmt::Write;

/// Render a type to Lean syntax.
pub fn render_type<W: Write>(ty: &Type, ctx: &mut RenderCtx<W>) {
    match ty {
        Type::Bool => {
            ctx.write("Bool");
        }
        Type::Prop => {
            ctx.write("Prop");
        }
        Type::UInt(width) => ctx.write(&format!("BoundedNat (2^{})", width)),
        Type::Address => ctx.write("Address"),

        Type::Struct {
            struct_id,
            type_args,
        } => {
            let struct_def = ctx.program.structs.get(*struct_id);
            let module_def = ctx.program.modules.get(struct_def.module_id);
            let escaped_name = escape::escape_struct_name(&struct_def.name);

            // Heterogeneous bags are modeled over the per-project closed
            // universe `TyCode` (see Prelude/Universe.lean + Generated/).
            // `bag::Bag` / `object_bag::ObjectBag` carry no type param in Move
            // but the Lean model is `Bag (U : Type)`, so we apply the concrete
            // project universe `_root_.TyCode` explicitly.
            if struct_def.qualified_name == "bag::Bag"
                || struct_def.qualified_name == "object_bag::ObjectBag"
            {
                let namespace = ctx
                    .program
                    .namespace_overrides
                    .get(&struct_def.module_id)
                    .cloned()
                    .unwrap_or_else(|| escape::module_name_to_namespace(&module_def.name));
                ctx.write(&format!(
                    "(_root_.{}.{} _root_.TyCode",
                    namespace, escaped_name
                ));
                for arg in type_args {
                    ctx.write(" (");
                    render_type(arg, ctx);
                    ctx.write(")");
                }
                ctx.write(")");
                return;
            }

            // Don't qualify Lean built-in types
            let qualified_name = if escape::is_lean_builtin(&struct_def.name) {
                escaped_name
            } else {
                let namespace = ctx
                    .program
                    .namespace_overrides
                    .get(&struct_def.module_id)
                    .cloned()
                    .unwrap_or_else(|| escape::module_name_to_namespace(&module_def.name));
                // Don't qualify if we're in the same module
                if ctx.current_module_namespace == Some(namespace.as_str()) {
                    escaped_name
                } else {
                    format!("{}.{}", namespace, escaped_name)
                }
            };

            if type_args.is_empty() {
                ctx.write(&qualified_name);
            } else {
                ctx.write(&format!("({}", qualified_name));
                for arg in type_args {
                    ctx.write(" (");
                    render_type(arg, ctx);
                    ctx.write(")");
                }
                ctx.write(")");
            }
        }

        Type::Vector(elem) => {
            ctx.write("(List (");
            render_type(elem, ctx);
            ctx.write("))");
        }

        // Immutable references are erased in pure functional Lean
        Type::Reference(inner) => {
            render_type(inner, ctx);
        }

        // Mutable references render as Mutable (T) s when a state variable is set
        // (for parameters where s is a type variable), otherwise render with the
        // concrete state type.
        Type::MutableReference(inner, state) => {
            if let Some(ref state_var) = ctx.mutable_state_var {
                let state_var = state_var.clone();
                ctx.write("(Mutable (");
                render_type(inner, ctx);
                ctx.write(") ");
                ctx.write(&state_var);
                ctx.write(")");
            } else {
                ctx.write("(Mutable (");
                render_type(inner, ctx);
                ctx.write(") (");
                render_type(state, ctx);
                ctx.write("))");
            }
        }

        Type::TypeParameter(idx) => {
            // Use the actual type parameter name from the current function if available
            if let Some(type_params) = ctx.type_params {
                if let Some(name) = type_params.get(*idx as usize) {
                    ctx.write(&escape::escape_identifier(name));
                } else {
                    // Index is out of bounds - this happens when inlined bytecode
                    // references type parameters from a callee's context (e.g.,
                    // option::none<T> inlined into a non-generic function).
                    // Use _ to let Lean infer the correct type.
                    ctx.write("_");
                }
            } else {
                // No type params in context (e.g., rendering struct field types)
                ctx.write(&format!("tv{}", idx));
            }
        }

        Type::Tuple(types) => {
            if types.is_empty() {
                ctx.write("Unit");
            } else if types.len() == 1 {
                render_type(&types[0], ctx);
            } else {
                ctx.write("(");
                for (i, ty) in types.iter().enumerate() {
                    if i > 0 {
                        ctx.write(" × ");
                    }
                    render_type(ty, ctx);
                }
                ctx.write(")");
            }
        }

        Type::Option(inner) => {
            ctx.write("(Option (");
            render_type(inner, ctx);
            ctx.write("))");
        }

        Type::MoveAbort => {
            ctx.write("MoveAbort");
        }
    }
}

/// Check if a type renders as multiple tokens (needs parens when used as a function argument).
fn type_needs_parens(ty: &Type) -> bool {
    match ty {
        // BoundedNat (2^N) is two tokens
        Type::UInt(_) => true,
        // Struct types are already wrapped in parens by render_type when they have args
        Type::Struct { .. } => false,
        // Tuples with 2+ elements have × operators
        Type::Tuple(types) => types.len() >= 2,
        // Immutable references delegate to inner (erased)
        Type::Reference(inner) => type_needs_parens(inner),
        // Mutable references always need parens since they render as (Mutable T s)
        Type::MutableReference(_, _) => true,
        // Everything else is a single token
        _ => false,
    }
}

/// Render a type as a function argument, wrapping in parens if it's multi-token.
pub fn render_type_as_arg<W: Write>(ty: &Type, ctx: &mut RenderCtx<W>) {
    if type_needs_parens(ty) {
        ctx.write("(");
        render_type(ty, ctx);
        ctx.write(")");
    } else {
        render_type(ty, ctx);
    }
}

/// Render a type to a string.
pub fn type_to_string(ty: &Type, program: &Program, current_module: Option<&str>) -> String {
    type_to_string_with_params(ty, program, current_module, None)
}

pub fn type_to_string_with_params(
    ty: &Type,
    program: &Program,
    current_module: Option<&str>,
    type_params: Option<&[String]>,
) -> String {
    type_to_string_full_with_mut(ty, program, current_module, type_params, None)
}

pub fn type_to_string_full_with_mut(
    ty: &Type,
    program: &Program,
    current_module: Option<&str>,
    type_params: Option<&[String]>,
    mutable_state_var: Option<&str>,
) -> String {
    let mut s = String::new();
    use super::lean_writer::LeanWriter;
    use std::collections::HashSet;
    let writer = LeanWriter::new(&mut s);
    let mut ctx = RenderCtx::new(
        program,
        0, // ModuleID is just usize
        current_module,
        writer,
        HashSet::new(),
    );
    if let Some(params) = type_params {
        ctx.with_type_params(params);
    }
    if let Some(state_var) = mutable_state_var {
        ctx.mutable_state_var = Some(state_var.to_string());
    }
    render_type(ty, &mut ctx);
    s
}

/// Get the Lean type name for a UInt width (e.g., 64 -> "UInt64").
pub fn uint_type_name(bits: usize) -> &'static str {
    match bits {
        8 => "UInt8",
        16 => "UInt16",
        32 => "UInt32",
        64 => "UInt64",
        128 => "UInt128",
        256 => "UInt256",
        _ => panic!("Unsupported UInt width: {}", bits),
    }
}

/// Get the Lean conversion function name for a UInt width (e.g., 64 -> "toUInt64").
pub fn uint_cast_func(bits: usize) -> String {
    format!("to{}", uint_type_name(bits))
}
