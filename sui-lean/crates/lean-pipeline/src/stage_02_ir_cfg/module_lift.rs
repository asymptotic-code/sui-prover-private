//! Module-level lifting: creates [`Module`] entries and lifts
//! struct / enum definitions into [`Struct`] entries.
//!
//! Composes with [`super::function_lift`] (per-function lifting) and
//! [`super::natives`] (the per-thing native classification) at the
//! pipeline-driver layer.
//!
//! ## Native-vs-translated dispatch
//!
//! - **Per-struct**: every struct in [`natives::NATIVE_STRUCTS`]
//!   (queried via [`super::natives::is_native_struct`]) is lifted via
//!   [`lift_struct`] with `is_native = true` -- the renderer maps the
//!   struct type back to a prelude definition and skips its body.
//!   Other structs are lifted with `is_native = false`.
//! - **Per-function**: every function for which
//!   [`super::natives::is_native_function`] returns `true` is
//!   registered as a [`crate::ir::NativeDecl`] in
//!   `program.natives.decls` so call sites resolve; its body is
//!   never translated. Other functions are left for
//!   [`super::function_lift`] to translate later.
//! - **Module `is_native` flag**: derived per-thing from
//!   [`super::natives::is_native_function`] +
//!   [`super::natives::is_native_struct`]: a module is native iff
//!   every struct / enum is native AND every function is native.
//!   The renderer reads this flag to decide whether to emit a stub
//!   that forwards to the `<Module>Natives.lean` sibling or a full
//!   module body.

use move_model::model::{ModuleEnv, StructEnv};

use crate::ir::{Field, Module, ProgramBuilder, Struct, Variant};

use super::natives::{
    has_ext_pure, has_ext_world, has_spec_only, is_injected_stub_native, is_native_function,
    is_native_struct, native_effects, native_has_aborts_companion,
};
use super::types::translate_type;
use super::Stage2Error;

/// Lift a Move [`ModuleEnv`] into a [`Module`] entry plus all of its
/// struct / enum definitions.
///
/// `package_name` is the IR-side package label (matches
/// `natives::NativeFunctionModule::package` for natives; for user code, it
/// is the Move-package name as seen in `Move.toml`).
///
/// On a native module, only the [`Module`] is inserted (with
/// `is_native: true`) plus a [`crate::ir::NativeDecl`] entry per
/// declared function; the struct definitions are skipped because
/// the prelude owns them. `program.functions` is body-only and
/// gets nothing from `module_lift` -- the per-function lifter
/// handles translated user code.
///
/// Holds-pruning policy: every Move function declared in the
/// module surfaces as a `NativeDecl` if it's native (so call sites
/// resolve regardless of the holder). Translated functions are
/// handled separately by the per-function lift (`function_lift`),
/// which IS holder-gated -- pruned non-natives never get a body
/// inserted and therefore never appear in `program.functions`.
pub fn lift_module(
    module_env: &ModuleEnv,
    package_name: &str,
    prog: &mut ProgramBuilder,
) -> Result<(), Stage2Error> {
    let env = module_env.env;
    let pool = env.symbol_pool();
    let module_name = pool.string(module_env.get_name().name()).to_string();
    // Module-level `is_native` flag powers the renderer's
    // user-package emit filter ("emit framework modules alongside
    // user-package modules so user code can import them"). Derived
    // per the per-thing classification: true iff every struct in
    // the module is native AND every function is native. A mixed
    // module (some translated, some native) gets `is_native: false`
    // so the renderer emits its full namespace body (with the
    // natives sibling imported alongside, per the renderer's
    // per-thing dispatch).
    let all_structs_native = module_env.get_structs().all(|s| {
        let n = pool.string(s.get_name()).to_string();
        is_native_struct(package_name, &module_name, &n)
    });
    let all_enums_native = module_env.get_enums().all(|e| {
        let n = pool.string(e.get_name()).to_string();
        is_native_struct(package_name, &module_name, &n)
    });
    let all_functions_native = module_env.get_functions().all(|f| {
        let n = pool.string(f.get_name()).to_string();
        is_native_function(package_name, &module_name, &n, f.is_native())
    });
    let is_native = all_structs_native && all_enums_native && all_functions_native;

    let mod_id = prog.module_id(module_env.get_id());
    prog.insert_module(
        mod_id,
        Module {
            name: module_name.clone(),
            package_name: package_name.to_string(),
            // 64-char zero-padded hex of the numeric defining address,
            // matching Move's canonical 32-byte address form.
            address: format!("{:064x}", module_env.get_name().addr()),
            required_imports: Vec::new(),
            is_native,
        },
    );

    // Per-struct dispatch: prelude-replaced structs get header-only
    // stubs (the renderer maps qualified references like
    // `Tx_context.TxContext` to the prelude type and never emits a
    // body); non-native structs are lifted in full. Recording the
    // header even for prelude-replaced structs keeps the empty-name
    // stubs that get-or-allocate via `prog.struct_id(qid)` from
    // dangling without a `name` / `qualified_name`.
    for struct_env in module_env.get_structs() {
        let struct_name = pool.string(struct_env.get_name()).to_string();
        let is_native = is_native_struct(package_name, &module_name, &struct_name);
        lift_struct(&struct_env, prog, is_native)?;
    }
    for enum_env in module_env.get_enums() {
        let enum_name = pool.string(enum_env.get_name()).to_string();
        if is_native_struct(package_name, &module_name, &enum_name) {
            lift_native_enum_header(&enum_env, prog)?;
        } else {
            lift_enum(&enum_env, prog)?;
        }
    }

    // Insert NativeDecl entries for every native callee. Translated
    // (non-native) functions get their entries from `function_lift`
    // (phase 2 in pipeline.rs); `module_lift` is purely the
    // native-registration phase per
    // `plans/lean-pipeline/no-stubs-templated-natives.md`.
    //
    // No Function stub is ever inserted -- `program.functions` is
    // body-only after step 5.
    for func_env in module_env.get_functions() {
        let func_qid = move_model::model::QualifiedId {
            module_id: module_env.get_id(),
            id: func_env.get_id(),
        };
        let func_name = pool.string(func_env.get_name()).to_string();
        let decl_is_native =
            is_native_function(package_name, &module_name, &func_name, func_env.is_native());
        if !decl_is_native {
            continue; // function_lift handles translated functions
        }
        let fid = prog.function_id(func_qid);
        if prog.program().natives.decls.contains_key(&fid) {
            continue; // already registered (forward-reference path)
        }
        let signature = super::function_lift::lift_signature(&func_env, prog)?;
        // `#[ext(pure)]` / `#[ext(world)]` on a Move function are
        // explicit user classifications for spec/verification purposes,
        // overriding the framework-native allowlist:
        //   * `#[ext(pure)]`  -> [`Effects::PURE`]  (value-level
        //     invariant predicates, e.g. `nodeInv`).
        //   * `#[ext(world)]` -> [`Effects::WORLD`] (world-reading
        //     invariant predicates over df-backed state, e.g. `sl_inv`):
        //     `GlobalMut` seeds `compute_needs_world` so `world` threads
        //     through every caller, while `Total`/`Det` keep it
        //     abort-free and deterministic.
        // With neither annotation, consult the explicit per-entry
        // classification table; missing entries default to
        // [`Effects::CONSERVATIVE`].
        let func_has_ext_pure = has_ext_pure(&func_env);
        let func_has_ext_world = has_ext_world(&func_env);
        let decl_effects = if func_has_ext_pure {
            crate::ir::Effects::PURE
        } else if func_has_ext_world {
            crate::ir::Effects::WORLD
        } else {
            native_effects(package_name, &module_name, &func_name)
        };
        // User-declared `native fun`: the Move `native` keyword on a
        // function NOT covered by the framework allowlist. Its Lean
        // definition is hand-written (the pipeline emits no stub, and
        // the renderer imports a `<Module>Natives.lean` sibling). The
        // `#[spec_only]` bit distinguishes authored specification
        // vocabulary, which the native-model audit accepts automatically,
        // from runtime native models that need an explicit trust rule.
        // `is_native_function(.., false)`
        // consults only the allowlist (no `move_native` shortcut), so
        // this excludes framework natives whose keyword also trips
        // `is_native()`. See [`crate::ir::NativeDecl::user_native`].
        let move_native = func_env.is_native();
        let allowlisted = is_native_function(package_name, &module_name, &func_name, false);
        // sui-prover's `add_stub_module` injects a placeholder
        // `native fun __stub_placeholder` into the ROOT package (modules
        // `ghost` / `prover` / `log`) for packages that depend on Sui
        // explicitly. It is a compiler-injected artifact, not a
        // hand-defined datatype-invariant predicate: exempt it from the
        // user-native overlay machinery. Unreferenced placeholders are omitted;
        // any unexpected reference still reaches the native-model audit and fails
        // because no model exists.
        let user_native: Option<bool> =
            if move_native && !allowlisted && !is_injected_stub_native(&func_name) {
                Some(has_spec_only(&func_env, module_env))
            } else {
                None
            };
        let has_aborts_companion =
            native_has_aborts_companion(package_name, &module_name, &func_name);
        let aborts_label = if has_aborts_companion {
            Some(format!(
                "{}::{}::{}",
                package_name,
                module_name,
                crate::ir::names::aborts_name(&func_name)
            ))
        } else {
            None
        };
        let aborts_name = if has_aborts_companion {
            Some(crate::ir::names::aborts_name(&func_name))
        } else {
            None
        };
        let aborts_signature = if has_aborts_companion {
            Some(crate::ir::Signature {
                type_params: signature.type_params.clone(),
                params: signature.params.clone(),
                return_type: crate::ir::Type::Bool,
            })
        } else {
            None
        };
        let decl = crate::ir::NativeDecl {
            module: mod_id,
            name: func_name,
            signature,
            effects: decl_effects,
            explicit_pure: func_has_ext_pure,
            is_framework: is_native,
            spec_target: None,
            user_native,
        };
        prog.insert_native(fid, decl);

        // Register a synthetic `.aborts` companion for natives that
        // ship one in their `lemmas/natives/<Pkg>/<Mod>Natives.lean`
        // file. Stage 7's `aborts_map` collection picks up entries
        // whose `spec_target` references this base, so the
        // compose-callee path in `expr_aborts` emits a precise
        // `Call(<companion fid>, args)` instead of the coarse
        // `bool_lit(true)` fallback for `AbortBit::Partial` natives.
        if let (Some(label), Some(name), Some(sig)) = (aborts_label, aborts_name, aborts_signature)
        {
            let aborts_fid = prog.synthetic_function_id(&label);
            if !prog.program().natives.decls.contains_key(&aborts_fid) {
                let aborts_decl = crate::ir::NativeDecl {
                    module: mod_id,
                    name,
                    signature: sig,
                    effects: crate::ir::Effects::PURE,
                    explicit_pure: true,
                    is_framework: is_native,
                    spec_target: Some(fid),
                    user_native: None,
                };
                prog.insert_native(aborts_fid, aborts_decl);
            }
        }
    }

    Ok(())
}

/// Lift a Move struct into a [`Struct`] entry. `is_native` marks a struct
/// in a native module: the renderer skips its body (the prelude /
/// `<Mod>Natives.lean` sibling owns the Lean `structure`), but the field
/// metadata is still translated and recorded -- a direct field access on a
/// native struct (e.g. `std::string::String`'s `bytes`) must resolve to
/// the right field name, so the header carries the real fields.
fn lift_struct(
    struct_env: &StructEnv,
    prog: &mut ProgramBuilder,
    is_native: bool,
) -> Result<(), Stage2Error> {
    let env = struct_env.module_env.env;
    let pool = env.symbol_pool();
    let qid = move_model::model::QualifiedId {
        module_id: struct_env.module_env.get_id(),
        id: struct_env.get_id(),
    };
    let struct_id = prog.struct_id(qid);
    let module_id = prog.module_id(struct_env.module_env.get_id());

    let name = pool.string(struct_env.get_name()).to_string();
    let qualified_name = format!(
        "{}::{}",
        pool.string(struct_env.module_env.get_name().name()),
        name
    );
    let type_params: Vec<String> = struct_env
        .get_type_parameters()
        .iter()
        .map(|tp| pool.string(tp.0).to_string())
        .collect();
    let fields = struct_env
        .get_fields()
        .map(|f| {
            Ok::<_, Stage2Error>(Field {
                name: pool.string(f.get_name()).to_string(),
                field_type: translate_type(&f.get_type(), prog)?,
            })
        })
        .collect::<Result<Vec<_>, _>>()?;

    prog.insert_struct(
        struct_id,
        Struct {
            module_id,
            name,
            qualified_name,
            type_params,
            fields,
            variants: None,
            is_native,
        },
    );
    Ok(())
}

/// Lift a Move enum into a [`Struct`] entry with `variants: Some(...)`.
fn lift_enum(
    enum_env: &move_model::model::EnumEnv,
    prog: &mut ProgramBuilder,
) -> Result<(), Stage2Error> {
    let env = enum_env.module_env.env;
    let pool = env.symbol_pool();
    let qid = move_model::model::QualifiedId {
        module_id: enum_env.module_env.get_id(),
        id: enum_env.get_id(),
    };
    let struct_id = prog.struct_id(qid);
    let module_id = prog.module_id(enum_env.module_env.get_id());

    let name = pool.string(enum_env.get_name()).to_string();
    let qualified_name = format!(
        "{}::{}",
        pool.string(enum_env.module_env.get_name().name()),
        name
    );
    let type_params: Vec<String> = enum_env
        .get_named_type_parameters()
        .iter()
        .map(|tp| pool.string(tp.0).to_string())
        .collect();
    let variants: Vec<Variant> = enum_env
        .get_variants()
        .map(|v| {
            let v_name = pool.string(v.get_name()).to_string();
            let tag = v.get_tag();
            let fields = v
                .get_fields()
                .map(|f| {
                    Ok::<_, Stage2Error>(Field {
                        name: pool.string(f.get_name()).to_string(),
                        field_type: translate_type(&f.get_type(), prog)?,
                    })
                })
                .collect::<Result<Vec<_>, _>>()?;
            Ok(Variant {
                name: v_name,
                tag,
                fields,
            })
        })
        .collect::<Result<Vec<Variant>, Stage2Error>>()?;

    prog.insert_struct(
        struct_id,
        Struct {
            module_id,
            name,
            qualified_name,
            type_params,
            fields: Vec::new(),
            variants: Some(variants),
            is_native: false,
        },
    );
    Ok(())
}

/// Header-only lifter for an enum in a native module. Like a native
/// [`lift_struct`] but emits an empty `variants: Some(...)` (a
/// placeholder); the prelude owns the actual variants.
fn lift_native_enum_header(
    enum_env: &move_model::model::EnumEnv,
    prog: &mut ProgramBuilder,
) -> Result<(), Stage2Error> {
    let env = enum_env.module_env.env;
    let pool = env.symbol_pool();
    let qid = move_model::model::QualifiedId {
        module_id: enum_env.module_env.get_id(),
        id: enum_env.get_id(),
    };
    let struct_id = prog.struct_id(qid);
    let module_id = prog.module_id(enum_env.module_env.get_id());
    let name = pool.string(enum_env.get_name()).to_string();
    let qualified_name = format!(
        "{}::{}",
        pool.string(enum_env.module_env.get_name().name()),
        name
    );
    let type_params: Vec<String> = enum_env
        .get_named_type_parameters()
        .iter()
        .map(|tp| pool.string(tp.0).to_string())
        .collect();
    prog.insert_struct(
        struct_id,
        Struct {
            module_id,
            name,
            qualified_name,
            type_params,
            fields: Vec::new(),
            variants: Some(Vec::new()),
            is_native: true,
        },
    );
    Ok(())
}
