//! Deterministic Lean declarations for first-class program globals.
//!
//! Global state itself is threaded before rendering: `thread_globals`
//! replaces `BorrowGlobal` / `GlobalRoot` with ordinary hidden parameters:
//! mutations for writable globals and erased immutable references for readonly
//! globals. The existing mut-to-let pass carries writable updates through
//! calls and returns. These declarations are boundary helpers only. They give
//! an external caller the stable `Loc.global` mutation wrapper expected by a
//! threaded writable entry without ambient mutable Lean state.

use std::fmt::Write;

use crate::ir::validate::ValidationErrorKind;
use crate::ir::visit::{walk_expr_default, Visitor};
use crate::ir::{GlobalDefinition, GlobalId, ModId, Program, StaticValue, StructId, Type};

use super::ty;
use super::writer::LeanWriter;
use super::{RenderError, RenderResult};

/// Reject frontend global operations before any function-specific renderer can
/// quarantine an error behind a `sorry` fallback or skip a stub body.
pub(in crate::render) fn ensure_threaded(program: &Program) -> RenderResult<()> {
    crate::ir::validate::validate_global_declarations(program).map_err(|error| {
        match error.kind {
            ValidationErrorKind::UnknownModuleId(id) => RenderError::UnknownModId { id },
            ValidationErrorKind::UnknownStructId(id) => RenderError::UnknownStructId { id },
            ValidationErrorKind::GlobalStructTypeArgumentArityMismatch {
                global,
                struct_id,
                expected,
                actual,
            } => RenderError::InvalidGlobalStructTypeArity {
                global,
                struct_id,
                expected,
                actual,
            },
            ValidationErrorKind::InvalidGlobalStorageType { global, kind } => {
                RenderError::InvalidGlobalStorageType { global, kind }
            }
            ValidationErrorKind::GlobalTypeParameter { .. } => RenderError::UnsupportedConstruct {
                what: "program global has a function type parameter",
            },
            ValidationErrorKind::GlobalInitializerTypeMismatch { .. } => {
                RenderError::UnsupportedConstruct {
                    what: "program global initializer type mismatch",
                }
            }
            ValidationErrorKind::GlobalInitializerScalarOutOfRange { .. } => {
                RenderError::UnsupportedConstruct {
                    what: "program global initializer scalar out of range",
                }
            }
            ValidationErrorKind::GlobalInitializerArityMismatch { .. } => {
                RenderError::UnsupportedConstruct {
                    what: "program global initializer arity mismatch",
                }
            }
            ValidationErrorKind::GlobalInitializerStructMismatch { .. } => {
                RenderError::UnsupportedConstruct {
                    what: "program global initializer struct mismatch",
                }
            }
            _ => RenderError::UnsupportedConstruct {
                what: "invalid program global declaration",
            },
        }
    })?;

    #[derive(Default)]
    struct FirstResidual(Option<(&'static str, GlobalId)>);

    impl Visitor for FirstResidual {
        fn visit_expr(&mut self, expr: &crate::ir::Expr) {
            if self.0.is_some() {
                return;
            }
            match expr {
                crate::ir::Expr::BorrowGlobal(id) => self.0 = Some(("BorrowGlobal", *id)),
                crate::ir::Expr::WriteBack {
                    node: crate::ir::BorrowNode::GlobalRoot(id),
                    ..
                } => self.0 = Some(("GlobalRoot writeback", *id)),
                crate::ir::Expr::IsParent {
                    node: crate::ir::BorrowNode::GlobalRoot(id),
                    ..
                } => self.0 = Some(("GlobalRoot IsParent", *id)),
                _ => walk_expr_default(self, expr),
            }
        }
    }

    for function in program.functions.values() {
        let mut residual = FirstResidual::default();
        residual.visit_block(&function.body);
        if let Some((operation, id)) = residual.0 {
            return Err(RenderError::UnthreadedGlobal { operation, id });
        }
    }
    Ok(())
}

/// Emit the globals owned by `module_id` into a reserved nested
/// `C2LeanGlobals` namespace.
///
/// Identifiers are ID-based rather than source-name-based. C/LLVM symbol
/// names may contain punctuation that is not a Lean identifier, while the
/// numeric `GlobalId` is already the program's deterministic identity.
pub(in crate::render) fn render_module_globals<W: Write>(
    program: &Program,
    module_id: ModId,
    current_namespace: &str,
    w: &mut LeanWriter<W>,
) -> RenderResult<()> {
    let globals: Vec<(GlobalId, &crate::ir::Global)> = program
        .globals
        .iter()
        .filter(|(_, global)| global.module_id == module_id)
        .map(|(id, global)| (*id, global))
        .collect();
    if globals.is_empty() {
        return Ok(());
    }

    w.line("namespace C2LeanGlobals");
    w.newline();
    for (id, global) in globals {
        let stem = format!("g{id}");
        w.line(&format!("def {stem}Id : Nat := {id}"));
        w.line(&format!(
            "def {stem}Mutable : Bool := {}",
            if global.mutable { "true" } else { "false" }
        ));

        if let GlobalDefinition::Defined { startup_value } = &global.definition {
            w.write(&format!("def {stem}Initial : "));
            ty::render_type(&global.ty, program, Some(current_namespace), None, w);
            w.write(" := ");
            render_static_value(startup_value, &global.ty, program, current_namespace, w)?;
            w.newline();
        }

        if global.mutable {
            w.write(&format!("def {stem}Root {{Key : Type}} (value : "));
            ty::render_type(&global.ty, program, Some(current_namespace), None, w);
            w.write(") : Prover.Mutation.Mutation Key (");
            ty::render_type(&global.ty, program, Some(current_namespace), None, w);
            w.line(") :=");
            w.write("  @Prover.Mutation.Mutation.ofGlobal Key (");
            ty::render_type(&global.ty, program, Some(current_namespace), None, w);
            w.line(&format!(") {stem}Id value"));
        } else {
            // Immutable references are erased to their value type by the
            // existing renderer, so their boundary adapter is deliberately
            // just identity rather than a fake writable Mutation.
            w.write(&format!("def {stem}Ref (value : "));
            ty::render_type(&global.ty, program, Some(current_namespace), None, w);
            w.write(") : ");
            ty::render_type(&global.ty, program, Some(current_namespace), None, w);
            w.line(" := value");
        }
        if matches!(global.definition, GlobalDefinition::Defined { .. }) {
            if global.mutable {
                w.write(&format!("def {stem}InitialRoot {{Key : Type}} : "));
                w.write("Prover.Mutation.Mutation Key (");
                ty::render_type(&global.ty, program, Some(current_namespace), None, w);
                w.line(") :=");
                w.line(&format!("  {stem}Root {stem}Initial"));
            } else {
                w.write(&format!("def {stem}InitialRef : "));
                ty::render_type(&global.ty, program, Some(current_namespace), None, w);
                w.line(&format!(" := {stem}Ref {stem}Initial"));
            }
        }
        w.newline();
    }
    w.line("end C2LeanGlobals");
    w.newline();
    Ok(())
}

fn render_static_value<W: Write>(
    value: &StaticValue,
    expected: &Type,
    program: &Program,
    current_namespace: &str,
    w: &mut LeanWriter<W>,
) -> RenderResult<()> {
    match (value, expected) {
        (StaticValue::Unit, Type::Unit) => w.write("()"),
        (StaticValue::Bool(value), Type::Bool) => w.write(if *value { "true" } else { "false" }),
        (StaticValue::UInt { bits, value }, Type::UInt(expected_bits)) if bits == expected_bits => {
            w.write(&format!("({value} : BoundedNat (2^{bits}))"));
        }
        (StaticValue::Address(value), Type::Address) => {
            w.write(&format!("(Address.ofNat {value})"));
        }
        (StaticValue::Vector(elements), Type::Vector(element_type)) => {
            w.write("[");
            for (index, element) in elements.iter().enumerate() {
                if index > 0 {
                    w.write(", ");
                }
                render_static_value(element, element_type, program, current_namespace, w)?;
            }
            w.write("]");
        }
        (StaticValue::Repeat { value, count }, Type::Vector(element_type)) => {
            w.write(&format!("(List.replicate {count} "));
            render_static_value(value, element_type, program, current_namespace, w)?;
            w.write(")");
        }
        (StaticValue::Tuple(elements), Type::Tuple(element_types)) => {
            if elements.is_empty() {
                w.write("()");
            } else if elements.len() == 1 {
                render_static_value(
                    &elements[0],
                    &element_types[0],
                    program,
                    current_namespace,
                    w,
                )?;
            } else {
                w.write("(");
                for (index, (element, element_type)) in
                    elements.iter().zip(element_types).enumerate()
                {
                    if index > 0 {
                        w.write(", ");
                    }
                    render_static_value(element, element_type, program, current_namespace, w)?;
                }
                w.write(")");
            }
        }
        (
            StaticValue::Struct {
                struct_id,
                variant,
                fields,
            },
            Type::Struct {
                struct_id: expected_struct,
                type_args,
            },
        ) if struct_id == expected_struct => {
            render_static_struct(
                *struct_id,
                *variant,
                fields,
                type_args,
                program,
                current_namespace,
                w,
            )?;
        }
        // `ensure_threaded` validates every startup value before this
        // renderer is entered. Keep a defensive error here so future direct
        // callers cannot silently emit an ill-typed declaration.
        _ => {
            return Err(RenderError::UnsupportedConstruct {
                what: "ill-typed program global initializer",
            });
        }
    }
    Ok(())
}

fn render_static_struct<W: Write>(
    struct_id: StructId,
    variant: Option<usize>,
    fields: &[StaticValue],
    type_args: &[Type],
    program: &Program,
    current_namespace: &str,
    w: &mut LeanWriter<W>,
) -> RenderResult<()> {
    let declaration = program
        .structs
        .get(&struct_id)
        .ok_or(RenderError::UnknownStructId { id: struct_id })?;

    let field_declarations = if let Some(tag) = variant {
        let variant = declaration
            .variant_by_tag(tag)
            .ok_or(RenderError::UnknownVariant {
                struct_id,
                variant: tag,
            })?;
        let module =
            program
                .modules
                .get(&declaration.module_id)
                .ok_or(RenderError::UnknownModId {
                    id: declaration.module_id,
                })?;
        let namespace = super::escape::module_render_namespace(&module.package_name, &module.name);
        let qualified = if namespace == current_namespace {
            super::escape::escape_struct_name(&declaration.name)
        } else {
            format!(
                "{namespace}.{}",
                super::escape::escape_struct_name(&declaration.name)
            )
        };
        w.write("(");
        w.write(&qualified);
        w.write(".");
        w.write(&super::escape::escape_identifier(&variant.name));
        for (value, field) in fields.iter().zip(&variant.fields) {
            w.write(" ");
            let expected =
                crate::ir::validate::instantiate_global_field_type(&field.field_type, type_args)
                    .map_err(|_| RenderError::UnsupportedConstruct {
                        what: "global initializer contains an unbound type parameter",
                    })?;
            w.write("(");
            render_static_value(value, &expected, program, current_namespace, w)?;
            w.write(")");
        }
        w.write(")");
        return Ok(());
    } else {
        &declaration.fields
    };

    w.write("⟨");
    for (index, (value, field)) in fields.iter().zip(field_declarations).enumerate() {
        if index > 0 {
            w.write(", ");
        }
        let expected =
            crate::ir::validate::instantiate_global_field_type(&field.field_type, type_args)
                .map_err(|_| RenderError::UnsupportedConstruct {
                    what: "global initializer contains an unbound type parameter",
                })?;
        render_static_value(value, &expected, program, current_namespace, w)?;
    }
    w.write("⟩");
    Ok(())
}
