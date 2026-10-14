//! `Type` -> Lean syntax.
//!
//! Mapping (matches the legacy `type_renderer` for compatibility with
//! the existing Prelude/natives):
//!
//! - `Unit`              -> `Unit`
//! - `Bool`              -> `Bool`
//! - `Prop`              -> `Prop`
//! - `UInt(n)`           -> `BoundedNat (2^n)`
//! - `Address`           -> `Address`
//! - `Vector(t)`         -> `(List t)`
//! - `Tuple([t1, ...])`  -> `Unit` / `t` / `(t1 x t2 x ...)` (Lean uses `\u{00D7}`)
//! - `Struct{id, args}`  -> `<Namespace>.<Name> arg1 arg2 ...`
//! - `Reference(t)`      -> erased to inner type
//! - `MutableRef{i, r}`  -> `(Mutation i)` (per-package `Mutation := Prover.Mutation.Mutation AnyKey`)
//! - `TypeParam(i)`      -> the i-th type param name in the current context

use std::fmt::Write;

use crate::ir::{Program, Type};

use super::escape;
use super::writer::LeanWriter;

#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct WorldTypeOverrides {
    pub object: Option<String>,
    pub df_entry: Option<String>,
    pub bag_entry: Option<String>,
}

#[derive(Clone, Copy)]
pub struct TypeRenderContext<'a> {
    pub program: &'a Program,
    pub current_module: Option<&'a str>,
    pub type_params: Option<&'a [String]>,
    pub world: &'a WorldTypeOverrides,
}

impl<'a> TypeRenderContext<'a> {
    pub fn new(
        program: &'a Program,
        current_module: Option<&'a str>,
        type_params: Option<&'a [String]>,
        world: &'a WorldTypeOverrides,
    ) -> Self {
        Self {
            program,
            current_module,
            type_params,
            world,
        }
    }
}

/// Render `ty` into `w` in the context of `current_module` (used to skip
/// namespace qualification on same-module struct references) and
/// `type_params` (used to resolve `Type::TypeParam(i)` to its declared
/// name).
pub fn render_type<W: Write>(
    ty: &Type,
    program: &Program,
    current_module: Option<&str>,
    type_params: Option<&[String]>,
    w: &mut LeanWriter<W>,
) {
    let world = WorldTypeOverrides::default();
    render_type_in(
        ty,
        &TypeRenderContext::new(program, current_module, type_params, &world),
        w,
    );
}

pub fn render_type_in<W: Write>(ty: &Type, context: &TypeRenderContext<'_>, w: &mut LeanWriter<W>) {
    match ty {
        Type::Unit => w.write("Unit"),
        Type::Bool => w.write("Bool"),
        Type::Prop => w.write("Prop"),
        Type::UInt(width) => w.write(&format!("BoundedNat (2^{})", width)),
        Type::Address => w.write("Address"),

        Type::Vector(elem) => {
            w.write("(List ");
            render_type_as_arg_in(elem, context, w);
            w.write(")");
        }

        Type::Reference(inner) => {
            render_type_in(inner, context, w);
        }

        Type::MutableRef { inner, .. } => {
            // Render to the typed-Mutation prelude. `Mutation` is the
            // per-package abbreviation defined in
            // `<Package>/Generated/AnyKey.lean` (`abbrev Mutation :=
            // Prover.Mutation.Mutation AnyKey`). The Boogie-style
            // `root` is no longer at the Lean type level -- it lives
            // in the value's `loc` field.
            w.write("(Mutation ");
            render_type_as_arg_in(inner, context, w);
            w.write(")");
        }

        Type::TypeParam(idx) => {
            if let Some(params) = context.type_params {
                if let Some(name) = params.get(*idx as usize) {
                    w.write(&escape::escape_identifier(name));
                } else {
                    w.write("_");
                }
            } else {
                w.write(&format!("tv{}", idx));
            }
        }

        Type::Tuple(types) => {
            if types.is_empty() {
                w.write("Unit");
            } else if types.len() == 1 {
                render_type_in(&types[0], context, w);
            } else {
                w.write("(");
                for (i, t) in types.iter().enumerate() {
                    if i > 0 {
                        w.write(" \u{00D7} ");
                    }
                    render_type_in(t, context, w);
                }
                w.write(")");
            }
        }

        Type::Struct {
            struct_id,
            type_args,
        } => {
            let struct_def = context
                .program
                .structs
                .get(struct_id)
                .expect("render_type: unknown struct id");
            // Stage 4 registers a synthetic `Prover::World::World`
            // struct. The renderer maps it to the per-package
            // `abbrev World := Prover.World.World AnyEvent AnyObject`
            // emitted in `Generated/World.lean`, not to the
            // structural form (which would print as `World.World`).
            if struct_def.qualified_name == crate::stage_04_effects::WORLD_QUALIFIED_NAME {
                let obj_ovr = context.world.object.as_deref();
                let df_ovr = context.world.df_entry.as_deref();
                let be_ovr = context.world.bag_entry.as_deref();
                match (obj_ovr, df_ovr, be_ovr) {
                    (None, None, None) => w.write("World"),
                    (obj, df, be) => {
                        // Compose the Object / DfEntry / BagEntry slot
                        // overrides. A function may pin ANY subset --
                        // transfer natives pin the Object slot to
                        // `Bag.Entry __ObjU`; df store natives pin the
                        // DfEntry slot to `Bag.Entry __TyU` -- and any
                        // un-pinned slot falls back to the file-scoped
                        // polymorphic variable the per-module `World`
                        // notation declares (`__WorldObject` /
                        // `__WorldDfEntry` / `__WorldBagEntry`). df-store
                        // lemma functions are not obj-tainted in practice,
                        // so the `__WorldObject` fallback is in scope.
                        let obj_s = obj.unwrap_or("__WorldObject");
                        let df_s = df.unwrap_or("__WorldDfEntry");
                        let be_s = be.unwrap_or("__WorldBagEntry");
                        w.write(&format!(
                            "(Prover.World.World __WorldEvent ({}) ({}) ({}))",
                            obj_s, df_s, be_s
                        ));
                    }
                }
                return;
            }
            // Heterogeneous-storage natives `Sui.Bag.Bag` and
            // `Sui.ObjectBag.ObjectBag` are defined as
            // `structure Bag (U : Type) [Universe U]`. A struct's `Bag`
            // field is typed over the SEPARATE `BagU` bag universe (NOT
            // `TyCode`, the df universe): this is what lets a
            // Bag-CONTAINING struct also be a `TyCode` (df) value
            // without the `_Types -> TyCodeInterp -> _Types` cycle. The
            // `[Universe BagU]` instance the field type requires comes
            // from the `_Types` file's `import Generated.BagUInterp`
            // (added by `render::mod` for Bag-containing modules); BagU
            // excludes Bag-containing structs, so BagUInterp never
            // imports this `_Types` back -- the graph is a DAG. See
            // `plans/lean-pipeline/split-bag-df-universes.md`.
            //
            // The IR still represents these as 0-arity types
            // (`Type::Struct { type_args: [] }`), so we append
            // `_root_.BagU` here at print time.
            if struct_def.qualified_name == "bag::Bag"
                || struct_def.qualified_name == "object_bag::ObjectBag"
            {
                let escaped_name = escape::escape_struct_name(&struct_def.name);
                let module = context
                    .program
                    .modules
                    .get(&struct_def.module_id)
                    .expect("render_type: struct's module is missing");
                let namespace = escape::module_render_namespace(&module.package_name, &module.name);
                w.write("(_root_.");
                w.write(&namespace);
                w.write(".");
                w.write(&escaped_name);
                w.write(" _root_.BagU");
                for arg in type_args {
                    w.write(" ");
                    render_type_as_arg_in(arg, context, w);
                }
                w.write(")");
                return;
            }
            let module = context
                .program
                .modules
                .get(&struct_def.module_id)
                .expect("render_type: struct's module is missing");
            let escaped_name = escape::escape_struct_name(&struct_def.name);
            let namespace = escape::module_render_namespace(&module.package_name, &module.name);
            // Cross-module struct types: prefix with `_root_.` so the
            // qualified path can't be shadowed by a local binding of
            // the package's first-segment name. Concrete case from
            // current-lending: `x_oracle::X_oracle::get_price` takes
            // `(x_oracle: x_oracle::X_oracle::XOracle)` and
            // `(base_token: x_oracle::X_oracle::BaseToken)`. After
            // Lean binds the `x_oracle` parameter, the bare type
            // `x_oracle.X_oracle.BaseToken` on the next param parses
            // as `(x_oracle).X_oracle.BaseToken` -- field access on
            // the bound parameter, not a namespace lookup -- and
            // fails because `XOracle` doesn't have an `X_oracle`
            // field. Forcing `_root_.x_oracle.X_oracle.BaseToken`
            // starts the lookup at the global root, bypassing the
            // local shadow.
            //
            // Same-module struct types skip `_root_.` -- they're
            // resolved relative to the surrounding `namespace`
            // block; adding `_root_.` to those would still resolve,
            // but the bare form keeps the rendered Lean compact
            // and matches the convention for same-module function
            // calls in `render_call` (which similarly skips
            // `_root_.` for same-module dispatch).
            let qualified = if context.current_module == Some(namespace.as_str()) {
                escaped_name
            } else {
                format!("_root_.{}.{}", namespace, escaped_name)
            };

            if type_args.is_empty() {
                w.write(&qualified);
            } else {
                w.write("(");
                w.write(&qualified);
                for arg in type_args {
                    w.write(" ");
                    render_type_as_arg_in(arg, context, w);
                }
                w.write(")");
            }
        }
    }
}

/// Render `ty` as a positional argument: wrap in parens when its surface
/// syntax is multi-token (`UInt`, `Tuple`, `MutableRef`, parameterised
/// `Struct`).
pub fn render_type_as_arg<W: Write>(
    ty: &Type,
    program: &Program,
    current_module: Option<&str>,
    type_params: Option<&[String]>,
    w: &mut LeanWriter<W>,
) {
    let world = WorldTypeOverrides::default();
    render_type_as_arg_in(
        ty,
        &TypeRenderContext::new(program, current_module, type_params, &world),
        w,
    );
}

pub fn render_type_as_arg_in<W: Write>(
    ty: &Type,
    context: &TypeRenderContext<'_>,
    w: &mut LeanWriter<W>,
) {
    if needs_parens(ty) {
        w.write("(");
        render_type_in(ty, context, w);
        w.write(")");
    } else {
        render_type_in(ty, context, w);
    }
}

fn needs_parens(ty: &Type) -> bool {
    match ty {
        Type::UInt(_) | Type::MutableRef { .. } => true,
        Type::Tuple(types) => types.len() >= 2,
        Type::Reference(inner) => needs_parens(inner),
        Type::Struct { type_args, .. } => !type_args.is_empty(),
        _ => false,
    }
}

/// Convenience: render `ty` into a fresh `String`.
pub fn type_to_string(
    ty: &Type,
    program: &Program,
    current_module: Option<&str>,
    type_params: Option<&[String]>,
) -> String {
    let world = WorldTypeOverrides::default();
    type_to_string_in(
        ty,
        &TypeRenderContext::new(program, current_module, type_params, &world),
    )
}

pub fn type_to_string_in(ty: &Type, context: &TypeRenderContext<'_>) -> String {
    super::writer::render_to_string(|w| {
        render_type_in(ty, context, w);
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::Struct;

    #[test]
    fn world_overrides_are_explicit_and_reentrant() {
        let mut program = Program::default();
        program.structs.insert(
            0,
            Struct {
                module_id: 0,
                name: "World".to_string(),
                qualified_name: crate::stage_04_effects::WORLD_QUALIFIED_NAME.to_string(),
                type_params: Vec::new(),
                fields: Vec::new(),
                variants: None,
                is_native: true,
            },
        );
        let world_ty = Type::Struct {
            struct_id: 0,
            type_args: Vec::new(),
        };
        let first = WorldTypeOverrides {
            object: Some("FirstObject".to_string()),
            ..WorldTypeOverrides::default()
        };
        let second = WorldTypeOverrides {
            df_entry: Some("SecondDf".to_string()),
            ..WorldTypeOverrides::default()
        };
        let none = WorldTypeOverrides::default();

        let render = |overrides| {
            type_to_string_in(
                &world_ty,
                &TypeRenderContext::new(&program, None, None, overrides),
            )
        };
        let first_render = render(&first);
        let second_render = render(&second);
        let first_again = render(&first);
        let default_render = render(&none);

        assert!(first_render.contains("(FirstObject)"), "{first_render}");
        assert!(!first_render.contains("SecondDf"), "{first_render}");
        assert!(second_render.contains("(SecondDf)"), "{second_render}");
        assert_eq!(first_again, first_render);
        assert_eq!(default_render, "World");
    }
}
