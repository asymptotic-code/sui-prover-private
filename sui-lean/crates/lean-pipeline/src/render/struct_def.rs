//! `Struct` -> Lean `structure` or `inductive`.

use std::fmt::Write;

use crate::ir::{Program, Struct, Type};

use super::escape;
use super::ty;
use super::writer::LeanWriter;
use super::{context::RenderContext, RenderError, RenderResult};

pub fn render_struct<W: Write>(
    s: &Struct,
    context: &RenderContext<'_>,
    current_module: Option<&str>,
    w: &mut LeanWriter<W>,
) -> RenderResult<()> {
    if s.variants.is_some() {
        render_enum(s, context.program, current_module, w)
    } else {
        render_plain_struct(s, context, current_module, w)
    }
}

fn render_plain_struct<W: Write>(
    s: &Struct,
    context: &RenderContext<'_>,
    current_module: Option<&str>,
    w: &mut LeanWriter<W>,
) -> RenderResult<()> {
    let program = context.program;
    w.write("-- Struct: ");
    w.line(&s.qualified_name);

    let struct_name = escape::escape_struct_name(&s.name);
    w.write("structure ");
    w.write(&struct_name);
    for tp in &s.type_params {
        let tp_esc = escape::escape_identifier(tp);
        w.write(" (");
        w.write(&tp_esc);
        w.write(" : Type)");
    }
    w.line(" where");

    w.indent(false);
    for field in &s.fields {
        let tystr = ty::type_to_string(
            &field.field_type,
            program,
            current_module,
            Some(&s.type_params),
        );
        w.write(&escape::escape_identifier(&field.name));
        w.write(" : ");
        w.write(&tystr);
        if s.qualified_name == crate::stage_07_dejumps::option_aborts::ABORT_CODE_QUALIFIED_NAME
            && matches!(field.name.as_str(), "origin_tag" | "error_kind")
            && program.abort_provenance.mode == crate::ir::AbortPayloadMode::ObservedTest
        {
            w.write(" := 0");
        }
        w.newline();
    }
    w.dedent(false);

    // #6: a struct used as a CONCRETE derived-object key needs a `Repr`
    // instance so the `[Repr key]` hypothesis on `derive_address` (which
    // folds `(repr key).pretty`) resolves at the call site. A non-generic
    // VALUE key (real fields, e.g. `AccountKey`) gets value-dependent
    // `deriving Repr`. Generic/phantom keys get a constant instance below
    // (a `deriving Repr` would cascade `[Repr T]` onto the phantom param).
    let is_do_key = context.is_derived_object_key_struct(&s.qualified_name);
    ensure_struct_fields_support_decidable_eq(s, program)?;
    if is_do_key && s.type_params.is_empty() {
        w.line("deriving DecidableEq, Repr");
    } else {
        w.line("deriving DecidableEq");
    }
    // Inhabited via mk: each field defaults via its own Inhabited
    // instance. For generic params we need [Inhabited T] constraints.
    if s.type_params.is_empty() {
        w.write("instance : Inhabited ");
        w.write(&struct_name);
        w.write(" where default := \u{27E8}");
    } else {
        w.write("instance");
        for tp in &s.type_params {
            let tp_esc = escape::escape_identifier(tp);
            w.write(&format!(" [Inhabited {}]", tp_esc));
        }
        w.write(" : Inhabited (");
        w.write(&struct_name);
        for tp in &s.type_params {
            let tp_esc = escape::escape_identifier(tp);
            w.write(" ");
            w.write(&tp_esc);
        }
        w.write(") where default := \u{27E8}");
    }
    for (i, _) in s.fields.iter().enumerate() {
        if i > 0 {
            w.write(", ");
        }
        w.write("default");
    }
    w.line("\u{27E9}");
    w.newline();

    // `funds_accumulator::redeem<T>` reconstructs the redeemed funds value from
    // the amount the `Withdrawal` recorded (`Withdrawal.limit`). For
    // `balance::Balance` -- the funds type the accumulator holds -- that value IS
    // the balance's single `value` field, so emit a `FromAccumValue` instance
    // that wraps the recorded amount into a `Balance`. Without it, redeem falls
    // back to the value-blind default (value 0) in `Prelude.Helpers` and every
    // `assert!(value > 0)` on a redeemed balance over-aborts.
    if s.qualified_name == "balance::Balance" && s.fields.len() == 1 {
        let val_field = escape::escape_identifier(&s.fields[0].name);
        w.write("instance");
        for tp in &s.type_params {
            w.write(&format!(" {{{} : Type}}", escape::escape_identifier(tp)));
        }
        w.write(" : FromAccumValue (");
        w.write(&struct_name);
        for tp in &s.type_params {
            w.write(" ");
            w.write(&escape::escape_identifier(tp));
        }
        w.write(") where ofValue v := { ");
        w.write(&val_field);
        w.line(" := BoundedNat.convert v }");
        w.newline();

        // Dual instance for the deposit direction: `add_impl` /
        // `add_to_accumulator_address` project a deposited `Balance`'s
        // `value` field into the World accumulator ledger via
        // `ToAccumValue.toValue`. Without it deposits fall back to the
        // value-blind 0 in `Prelude.Helpers` and the ledger undercounts.
        w.write("instance");
        for tp in &s.type_params {
            w.write(&format!(" {{{} : Type}}", escape::escape_identifier(tp)));
        }
        w.write(" : ToAccumValue (");
        w.write(&struct_name);
        for tp in &s.type_params {
            w.write(" ");
            w.write(&escape::escape_identifier(tp));
        }
        w.write(") where toValue b := BoundedNat.convert b.");
        w.line(&val_field);
        w.newline();
    }

    // #6: a GENERIC/phantom derived-object key (e.g. `CurrencyKey T`) gets
    // a CONSTANT `Repr` instance -- value-independent, ignoring the phantom
    // param -- so the `[Repr key]` hypothesis resolves without cascading a
    // `[Repr T]` requirement onto the param. The key's TYPE is already
    // folded into the address via #23 (`Universe.typeName`), so a constant
    // value-repr loses no discrimination for these single-per-type keys.
    if is_do_key && !s.type_params.is_empty() {
        w.write("instance");
        for tp in &s.type_params {
            w.write(&format!(" {{{} : Type}}", escape::escape_identifier(tp)));
        }
        w.write(" : Repr (");
        w.write(&struct_name);
        for tp in &s.type_params {
            w.write(" ");
            w.write(&escape::escape_identifier(tp));
        }
        w.write(") := \u{27E8}fun _ _ => Std.Format.text \"");
        w.write(&struct_name);
        w.line("\"\u{27E9}");
        w.newline();
    }

    // `Object.HasObjectId` for `key`-ability objects (first field is
    // `id : object::UID`). Emitted with the struct -- where the imports
    // are already in scope -- so EVERY object the program calls
    // `Object.id` on has an instance, not only those that reach the
    // ObjType universe through a transfer / storage callsite. The
    // ObjType-universe emitter handles the native object structs
    // (`Coin` etc.) that have no rendered definition; see
    // `obj_type_universe::struct_has_uid_first_field`.
    if super::obj_type_universe::struct_has_uid_first_field(s, program) {
        let id_field = escape::escape_identifier(&s.fields[0].name);
        w.write("instance");
        for tp in &s.type_params {
            w.write(&format!(" {{{} : Type}}", escape::escape_identifier(tp)));
        }
        w.write(" : _root_.Object.HasObjectId ");
        if s.type_params.is_empty() {
            w.write(&struct_name);
        } else {
            w.write("(");
            w.write(&struct_name);
            for tp in &s.type_params {
                w.write(" ");
                w.write(&escape::escape_identifier(tp));
            }
            w.write(")");
        }
        w.write(" where uid s := s.");
        w.line(&id_field);
        w.newline();
    }
    Ok(())
}

fn render_enum<W: Write>(
    s: &Struct,
    program: &Program,
    current_module: Option<&str>,
    w: &mut LeanWriter<W>,
) -> RenderResult<()> {
    let variants = s.variants.as_ref().expect("called on enum");

    w.write("-- Enum: ");
    w.line(&s.qualified_name);

    let enum_name = escape::escape_struct_name(&s.name);
    w.write("inductive ");
    w.write(&enum_name);
    for tp in &s.type_params {
        let tp_esc = escape::escape_identifier(tp);
        w.write(" (");
        w.write(&tp_esc);
        w.write(" : Type)");
    }
    // Pin the result universe for a parameterless enum: with no type param to
    // fix it, Lean leaves the inductive universe-polymorphic and a concrete
    // struct field (e.g. the defunctionalized loop-step `cont`) elaborates with
    // an unsolved universe metavariable. Generic enums take their universe from
    // the type param, so only annotate the parameterless case.
    if s.type_params.is_empty() {
        w.write(" : Type");
    }
    w.line(" where");

    w.indent(false);
    for v in variants {
        w.write("| ");
        w.write(&escape::escape_identifier(&v.name));
        for field in &v.fields {
            let tystr = ty::type_to_string(
                &field.field_type,
                program,
                current_module,
                Some(&s.type_params),
            );
            w.write(" (");
            w.write(&escape::escape_identifier(&field.name));
            w.write(" : ");
            w.write(&tystr);
            w.write(")");
        }
        w.newline();
    }
    w.dedent(false);
    // A defunctionalized loop-step inductive carries impl-level payloads (e.g.
    // `World`, mutation / object structs) that have no `BEq` / `Inhabited`
    // instance -- and needs none: it is only constructed and matched inside the
    // total `loop_step` and the `partial_fixpoint` matcher. Skip the derive so
    // instance synthesis is never attempted over those payloads.
    if !crate::stage_07_dejumps::aborts_defunctionalize::is_loop_step_struct(s) {
        ensure_struct_fields_support_decidable_eq(s, program)?;
        w.line("deriving DecidableEq, Inhabited");
    } else {
        // A step function that falls back to `partial def` needs its return
        // type to be `Nonempty` (deepbook `math::quick_sort.aborts.while_0_step`:
        // "could not prove that the type ... is nonempty"). `Nonempty` is a
        // Prop: unlike `Inhabited` it compiles no code in the surrounding
        // `noncomputable section`, and its derivation only needs one
        // constructor with nonempty fields.
        w.line("deriving Nonempty");
    }
    if s.qualified_name == crate::stage_07_dejumps::option_aborts::OPTION_QUALIFIED_NAME {
        w.line("universe u");
        w.line("@[simp] theorem AbortResult.match_noAbort");
        w.line("    {T : Type} {motive : AbortResult T -> Sort u}");
        w.line("    (noAbort : motive AbortResult.NoAbort)");
        w.line("    (aborted : (code : T) -> motive (AbortResult.Aborted code)) :");
        w.line("    (match (AbortResult.NoAbort : AbortResult T) with");
        w.line("     | .NoAbort => noAbort");
        w.line("     | .Aborted code => aborted code) = noAbort := rfl");
        w.newline();
        w.line("@[simp] theorem AbortResult.match_aborted");
        w.line("    {T : Type} {motive : AbortResult T -> Sort u}");
        w.line("    (code : T)");
        w.line("    (noAbort : motive AbortResult.NoAbort)");
        w.line("    (aborted : (code : T) -> motive (AbortResult.Aborted code)) :");
        w.line("    (match (AbortResult.Aborted code) with");
        w.line("     | .NoAbort => noAbort");
        w.line("     | .Aborted code => aborted code) = aborted code := rfl");
    }
    w.newline();
    Ok(())
}

fn ensure_struct_fields_support_decidable_eq(s: &Struct, program: &Program) -> RenderResult<()> {
    let mut visiting = std::collections::BTreeSet::new();
    if let Some(variants) = &s.variants {
        for variant in variants {
            for field in &variant.fields {
                ensure_type_supports_decidable_eq(
                    &field.field_type,
                    program,
                    &mut visiting,
                    &s.qualified_name,
                    &field.name,
                )?;
            }
        }
    } else {
        for field in &s.fields {
            ensure_type_supports_decidable_eq(
                &field.field_type,
                program,
                &mut visiting,
                &s.qualified_name,
                &field.name,
            )?;
        }
    }
    Ok(())
}

fn ensure_type_supports_decidable_eq(
    ty: &Type,
    program: &Program,
    visiting: &mut std::collections::BTreeSet<crate::ir::StructId>,
    root_struct: &str,
    root_field: &str,
) -> RenderResult<()> {
    match ty {
        Type::Unit | Type::Bool | Type::UInt(_) | Type::Address | Type::TypeParam(_) => Ok(()),
        Type::Prop => Err(RenderError::InvalidStructFieldType {
            struct_name: root_struct.to_string(),
            field_name: root_field.to_string(),
            reason: "Move struct fields must not have Prop type",
        }),
        Type::Vector(inner) => {
            ensure_type_supports_decidable_eq(inner, program, visiting, root_struct, root_field)
        }
        Type::Reference(_) => Err(RenderError::InvalidStructFieldType {
            struct_name: root_struct.to_string(),
            field_name: root_field.to_string(),
            reason: "Move struct fields must not contain references",
        }),
        Type::MutableRef { .. } => Err(RenderError::InvalidStructFieldType {
            struct_name: root_struct.to_string(),
            field_name: root_field.to_string(),
            reason: "Move struct fields must not contain mutable references after stage 3",
        }),
        Type::Tuple(types) => {
            for inner in types {
                ensure_type_supports_decidable_eq(
                    inner,
                    program,
                    visiting,
                    root_struct,
                    root_field,
                )?;
            }
            Ok(())
        }
        Type::Struct {
            struct_id,
            type_args,
        } => {
            let Some(struct_def) = program.structs.get(struct_id) else {
                return Err(RenderError::UnknownStructId { id: *struct_id });
            };
            if struct_def.qualified_name == crate::stage_04_effects::WORLD_QUALIFIED_NAME {
                return Err(RenderError::InvalidStructFieldType {
                    struct_name: root_struct.to_string(),
                    field_name: root_field.to_string(),
                    reason: "Move struct fields must not contain the synthetic World type",
                });
            }
            for inner in type_args {
                ensure_type_supports_decidable_eq(
                    inner,
                    program,
                    visiting,
                    root_struct,
                    root_field,
                )?;
            }
            if !visiting.insert(*struct_id) {
                return Err(RenderError::InvalidStructFieldType {
                    struct_name: root_struct.to_string(),
                    field_name: root_field.to_string(),
                    reason: "Move struct fields must not be recursively typed",
                });
            }
            if let Some(variants) = &struct_def.variants {
                for variant in variants {
                    for field in &variant.fields {
                        ensure_type_supports_decidable_eq(
                            &field.field_type,
                            program,
                            visiting,
                            root_struct,
                            root_field,
                        )?;
                    }
                }
            } else {
                for field in &struct_def.fields {
                    ensure_type_supports_decidable_eq(
                        &field.field_type,
                        program,
                        visiting,
                        root_struct,
                        root_field,
                    )?;
                }
            }
            visiting.remove(struct_id);
            Ok(())
        }
    }
}

#[cfg(test)]
mod abort_payload_tests {
    use super::*;
    use crate::ir::{AbortPayloadMode, AbortProvenance};
    use crate::stage_07_dejumps::option_aborts::{ensure_aborts_types, ABORT_CODE_QUALIFIED_NAME};

    fn rendered_abort_code(mode: AbortPayloadMode) -> String {
        let mut program = Program::default();
        AbortProvenance::configure(&mut program, mode).unwrap();
        ensure_aborts_types(&mut program);
        let abort_code = program
            .structs
            .values()
            .find(|value| value.qualified_name == ABORT_CODE_QUALIFIED_NAME)
            .unwrap();
        let context = super::RenderContext::new(
            &program,
            crate::render::loop_termination::LoopRenderContext::default(),
        );
        let mut writer = LeanWriter::new(String::new());
        render_struct(abort_code, &context, Some("Abort"), &mut writer).unwrap();
        writer.into_inner()
    }

    #[test]
    fn proof_payload_keeps_the_original_one_field_shape() {
        let rendered = rendered_abort_code(AbortPayloadMode::Proof);
        assert!(rendered.contains("code : BoundedNat (2^64)"));
        assert!(!rendered.contains("origin_tag"));
    }

    #[test]
    fn observed_payload_defaults_origin_for_legacy_native_literals() {
        let rendered = rendered_abort_code(AbortPayloadMode::ObservedTest);
        assert!(rendered.contains("origin_tag : BoundedNat (2^64) := 0"));
        assert!(rendered.contains("error_kind : BoundedNat (2^64) := 0"));
    }
}
