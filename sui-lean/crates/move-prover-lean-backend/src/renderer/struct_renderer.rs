// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Renders TheoremStruct to Lean structure definitions.

use super::lean_writer::LeanWriter;
use super::type_renderer::type_to_string_with_params;
use crate::escape;
use intermediate_theorem_format::{Program, Struct};
use std::fmt::Write;

/// Render a struct definition (or enum as inductive type).
pub fn render_struct<W: Write>(
    struct_def: &Struct,
    program: &Program,
    current_module: &str,
    w: &mut LeanWriter<W>,
) {
    if struct_def.variants.is_some() {
        render_enum(struct_def, program, current_module, w);
    } else {
        render_regular_struct(struct_def, program, current_module, w);
    }
}

/// Render a regular struct definition.
fn render_regular_struct<W: Write>(
    struct_def: &Struct,
    program: &Program,
    current_module: &str,
    w: &mut LeanWriter<W>,
) {
    // Comment header
    w.write("-- Struct: ");
    w.line(&struct_def.qualified_name);

    // Structure declaration
    let struct_name = escape::escape_struct_name(&struct_def.name);
    w.write("structure ");
    w.write(&struct_name);

    // Type parameters - use plain Type (no universe polymorphism needed since Move
    // types are always at Type 0, and native functions expect Type)
    for type_param in &struct_def.type_params {
        let escaped_param = escape::escape_identifier(type_param);
        w.write(" (");
        w.write(&escaped_param);
        w.write(" : Type)");
    }

    w.line(" where");

    // Fields
    w.indent(false);
    // Convert type_params from Vec<Rc<String>> to Vec<String> for the type renderer
    let type_params_strings: Vec<String> = struct_def
        .type_params
        .iter()
        .map(|s| s.as_ref().clone())
        .collect();
    for field in &struct_def.fields {
        let type_str = type_to_string_with_params(
            &field.field_type,
            program,
            Some(current_module),
            Some(&type_params_strings),
        );
        w.write(&escape::escape_identifier(&field.name));
        w.write(" : ");
        w.line(&type_str);
    }
    w.dedent(false);

    // Type class instances needed by generic functions.
    // Derive BEq (needed for == comparisons). Provide Inhabited manually because
    // `deriving Inhabited` fails for BoundedNat fields (expensive `by decide` proof).
    w.line("deriving BEq");
    let struct_name = escape::escape_struct_name(&struct_def.name);
    // For generic structs, add type class constraints on type parameters
    if struct_def.type_params.is_empty() {
        w.write(&format!(
            "instance : Inhabited {} where default := \u{27E8}",
            struct_name
        ));
    } else {
        w.write("instance");
        for type_param in &struct_def.type_params {
            let escaped_param = escape::escape_identifier(type_param);
            w.write(&format!(" [Inhabited {}]", escaped_param));
        }
        w.write(&format!(" : Inhabited ({}", struct_name));
        for type_param in &struct_def.type_params {
            let escaped_param = escape::escape_identifier(type_param);
            w.write(&format!(" {}", escaped_param));
        }
        w.write(") where default := \u{27E8}");
    }
    for (i, _) in struct_def.fields.iter().enumerate() {
        if i > 0 {
            w.write(", ");
        }
        w.write("default");
    }
    w.line("\u{27E9}");
    w.newline();
}

/// Render an enum as a Lean inductive type.
fn render_enum<W: Write>(
    struct_def: &Struct,
    program: &Program,
    current_module: &str,
    w: &mut LeanWriter<W>,
) {
    let variants = struct_def.variants.as_ref().expect("called on enum");

    // Comment header
    w.write("-- Enum: ");
    w.line(&struct_def.qualified_name);

    let enum_name = escape::escape_struct_name(&struct_def.name);

    // Convert type_params from Vec<Rc<String>> to Vec<String> for the type renderer
    let type_params_strings: Vec<String> = struct_def
        .type_params
        .iter()
        .map(|s| s.as_ref().clone())
        .collect();

    // Inductive declaration
    w.write("inductive ");
    w.write(&enum_name);

    // Type parameters
    for type_param in &struct_def.type_params {
        let escaped_param = escape::escape_identifier(type_param);
        w.write(" (");
        w.write(&escaped_param);
        w.write(" : Type)");
    }

    w.line(" where");
    w.indent(false);

    // Variants
    for variant in variants {
        w.write("| ");
        w.write(&escape::escape_identifier(&variant.name));

        // Variant fields as constructor arguments
        for field in &variant.fields {
            let type_str = type_to_string_with_params(
                &field.field_type,
                program,
                Some(current_module),
                Some(&type_params_strings),
            );
            w.write(" (");
            w.write(&escape::escape_identifier(&field.name));
            w.write(" : ");
            w.write(&type_str);
            w.write(")");
        }
        w.newline();
    }

    w.dedent(false);
    w.line("deriving BEq, Inhabited");
    w.newline();
}
