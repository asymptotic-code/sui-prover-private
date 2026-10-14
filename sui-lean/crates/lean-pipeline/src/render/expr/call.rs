//! Call / pack / match rendering (split from `expr/mod.rs`,
//! `plans/lean-pipeline/renderer-split.md`).

use super::*;
use crate::ir::analysis::type_of::strip_singleton_tuple;
use crate::ir::{Expr, MatchArm};
use crate::render::escape;
use crate::render::writer::LeanWriter;
use crate::render::{RenderError, RenderResult};
use std::fmt::Write;

fn needs_mutkey_named_implicit(
    fun: crate::ir::FunId,
    callee: crate::ir::CalleeRef<'_>,
    ctx: &ExprCtx<'_>,
) -> bool {
    if callee.is_native() || fun == ctx.current_fn_id {
        return false;
    }
    let crate::ir::CalleeRef::Translated(translated) = callee else {
        return false;
    };
    let callee_in_lemma_package = ctx
        .program
        .modules
        .get(&translated.module)
        .map(|module| escape::is_lemma_package(&module.package_name))
        .unwrap_or(false);
    callee_in_lemma_package
        && ctx.mutation_users.contains(&fun)
        && !signature_has_mutable_param(callee.signature())
}

pub(in crate::render) fn render_call<W: Write>(
    fun: crate::ir::FunId,
    type_args: &[crate::ir::Type],
    args: &[Expr],
    ctx: &ExprCtx<'_>,
    w: &mut LeanWriter<W>,
) -> RenderResult<()> {
    // Resolve callee via the unified registry: translated Functions
    // in `program.functions`, natives (framework + stage-10 synth)
    // in `program.natives.decls`. Both render as `<Pkg>.<Module>.<name>`.
    let callee = ctx
        .program
        .lookup_callee(fun)
        .ok_or(RenderError::UnknownFunId { id: fun })?;
    let callee_is_native = callee.is_native();
    // Stage-10 BoundedU{N}_<op> natives bypass the generic
    // `<module>.<name>` path -- the renderer maps them to width-
    // agnostic `BoundedNat.<op>` calls (Lean infers `bound` from
    // operand types). See `render::bounded_nat`.
    if let crate::ir::CalleeRef::Native(decl) = callee {
        if crate::render::bounded_nat::try_render_call(fun, decl, args, ctx, w)? {
            return Ok(());
        }
        // `std::bcs::to_bytes::<TypeName>(tn)` -- the generic
        // `Bcs.to_bytes` is a `[]` stub (BCS is value-dependent and
        // unmodeled), but a `TypeName`'s BCS bytes ARE its name bytes,
        // which coin canonical-ordering (`create_pool::check_coin_order`)
        // byte-compares. Route to `Type_name.to_bytes` (returns
        // `tn.name.bytes`) so the comparison is meaningful and -- with
        // `Type_name.get` now emitting the Move FQN -- matches Move's
        // coin order. Other `bcs::to_bytes` uses keep the `[]` stub.
        {
            let is_bcs = crate::render::native_models::is_bcs_to_bytes_model(ctx.program, fun);
            let arg_is_type_name = type_args
                .first()
                .map(|t| is_type_name_struct(t, ctx.program))
                .unwrap_or(false);
            if is_bcs && arg_is_type_name {
                if let Some(arg) = args.first() {
                    w.write("(_root_.Type_name.to_bytes ");
                    render_expr(arg, ctx, w)?;
                    w.write(")");
                    return Ok(());
                }
            }
        }
        // (The former render-time ghost-TypedMap substitution for
        // `Sui::dynamic_field::*` calls was deleted in step-2 slice C;
        // `route_df_to_world` rewrites every df/dof op IR-side.)
        // `Mutation.uninit` lowers to the typed `Prover.Mutation` prelude
        // (see `stage_02_ir_cfg::mutation_natives` for the registration
        // and `lemmas/Prelude/Mutation.lean` for the def). Default render
        // path produces `Prelude.Prelude.Mutation.uninit T i` with T as an
        // explicit positional arg, but the prelude declares T implicit, so
        // we must use `@` syntax and explicitly bind the AnyKey/T/i triple.
        if callee.name() == "Mutation.uninit" {
            w.write("(@Prover.Mutation.Mutation.uninit ");
            w.write(&key_slot(ctx));
            w.write(" ");
            if let Some(t) = type_args.first() {
                ctx.render_type_as_arg(t, w);
            } else {
                w.write("_");
            }
            w.write(" ");
            // The slot index arg comes through as a `Const::UInt { bits: 64 }`,
            // which `render_expr` would render as `(6 : BoundedNat (2^64))`.
            // The Lean def takes a `(i : Nat)`, so we extract the literal
            // and emit it directly.
            match args.first() {
                Some(Expr::Const(crate::ir::Const::UInt { value, .. })) => {
                    w.write(&value.to_string());
                }
                _ => w.write("0"),
            }
            // The `[Inhabited T]` instance arg comes after `(i : Nat)`
            // in `Mutation.uninit`'s signature. With `@`, Lean does
            // NOT auto-insert typeclass instance arguments -- they're
            // treated like any other implicit and must be provided
            // positionally. Emitting `_` lets the elaborator synthesize
            // the instance from the surrounding `[Inhabited T]` constraint
            // on the enclosing function. Without this `_`, the call
            // partially-applies and downstream callers see a
            // `[Inhabited T] -> Mutation K T` value where they expected
            // `Mutation K T`, with errors like:
            //   `@Mutation.uninit AnyKey (Node T) 12 has type
            //    [Inhabited (Node T)] -> Mutation AnyKey (Node T)
            //    but is expected to have type Mutation AnyKey (Node T)`
            w.write(" _)");
            return Ok(());
        }
    }
    let module_id = callee.module();
    let module = ctx
        .program
        .modules
        .get(&module_id)
        .ok_or(RenderError::UnknownModId { id: module_id })?;
    let namespace = escape::module_render_namespace(&module.package_name, &module.name);
    let mut escaped_name = escape::escape_identifier(callee.name());
    // Ghost-writing natives have a hand-written `<name>__ghost` variant
    // (threaded ghost params + the ghost write) alongside the plain static
    // def. Route the call to it exactly when this native is ghost-threaded in
    // THIS program (`program.ghost_vars` carries the native's FunId -- set by
    // `stage_04_ghost`). Non-ghost programs render the plain `<name>`, so the
    // shared static def stays un-threaded for callers without the markers.
    if callee_is_native && ctx.program.ghost_vars.contains_key(&fun) {
        escaped_name.push_str("__ghost");
    }
    // Default: drop the namespace prefix for same-module calls.
    // Exception: if `escaped_name` itself contains a `.` (a `.aborts`
    // companion or stage-7 loop helper like `insert.while_0`), Lean's
    // parser is liable to interpret `<leaf>.<suffix>` as dot-syntax
    // field access on a same-named local variable rather than as the
    // intended sibling function call. Concrete case: a function
    // `split_coin` and a parameter `split_coin : Coin.Coin t_tv0` in
    // the same scope -- the bare call `split_coin.aborts ...` resolves
    // to `(split_coin : Coin.Coin).aborts` -> `Coin.Coin.aborts` and
    // fails. Fully-qualifying as `<pkg>.<mod>.split_coin.aborts`
    // bypasses the shadow because the qualified path can't match a
    // local. With the SCC-aware emission ensuring `<pkg>.<mod>.X` is
    // in scope by the time `X.suffix` is referenced (see
    // `render::emit_function_sccs`), the qualified lookup succeeds.
    //
    // Cross-module calls additionally get a `_root_.` prefix:
    // namespace prefixes like `oracle` (the package name) can
    // themselves collide with a local binding of the same name
    // (e.g. `def version_verification (oracle : PriceOracle)`),
    // and bare `oracle.Oracle_version.X` resolves to
    // `(oracle : PriceOracle).Oracle_version.X` -> field-not-found.
    // `_root_.oracle.Oracle_version.X` forces Lean to start lookup
    // at the global root, bypassing the local.
    // Always emit the namespace prefix for same-module calls.
    // Lean's name resolution prefers locals over namespace lookups,
    // so a bare `split_coin` call inside a function with a
    // `split_coin : Coin.Coin T` parameter resolves to the local
    // (a struct, not a function) -- the rendered code then fails
    // with `Function expected at`. Qualifying as `<pkg>.<mod>.split_coin`
    // bypasses the local shadow because the qualified path can't
    // match a local name. Cross-module additionally gets `_root_.`
    // to bypass package-prefix shadows; the intra-module case
    // skips `_root_.` so it still works inside `mutual ... end`
    // blocks where `_root_.<path>` doesn't resolve until the
    // block's defs are committed.
    //
    // **Exception (same-module + shadowed package segment):** when
    // the package's first segment appears as a parameter name in
    // the surrounding function (e.g. `x_oracle::User_oracle::get_price`
    // takes a parameter `x_oracle : XOracle`), the bare
    // `x_oracle.User_oracle.<fn>` qualifier resolves through the
    // local parameter (`(x_oracle).User_oracle.<fn>` -- field
    // access on XOracle) and fails. Use `_root_.` here too. This
    // is only safe outside `mutual ... end` blocks for same-block
    // forward references, but in practice the local-shadow only
    // arises for cross-call patterns where the callee isn't in
    // the surrounding SCC -- and even when it is, the package's
    // first segment matching a param name is rare enough that the
    // mutual-block tradeoff favours correctness here.
    let pkg_first_segment = namespace.split('.').next().unwrap_or("");
    let package_shadowed_by_param =
        !pkg_first_segment.is_empty() && ctx.var_overrides.values().any(|n| n == pkg_first_segment);
    let qualified = if ctx.current_module == Some(namespace.as_str()) && !package_shadowed_by_param
    {
        format!("{}.{}", namespace, escaped_name)
    } else {
        format!("_root_.{}.{}", namespace, escaped_name)
    };

    let needs_outer_parens = !args.is_empty() || !type_args.is_empty();
    if needs_outer_parens {
        w.write("(");
    }
    w.write(&qualified);
    // Cross-Mutation-scope bridge: a cross-function lemma-package
    // callee can carry an auto-bound `{__MutKey : Type}` without
    // exposing a MutableRef parameter that determines it at this call site.
    // A result alone is insufficient in discarded or unannotated contexts.
    // Pin the implicit with `(__MutKey := AnyKey)`;
    // reading `AnyKey` also makes the caller auto-bind `__MutKey`
    // from its file-scoped variable when necessary.
    //
    // Slice 4 of item B (plans/lean-pipeline/item-b-real-anykey-work-plan.md)
    // attempted to remove this bridge: post-slice-2, every call
    // that flows a Mutation now references `AnyKey` textually
    // (either via `key_slot(ctx)` = "AnyKey" in the type ascription
    // or via a real `(AnyKey.k_<mangled> ...)` wrap), which should
    // be enough for `variable {__MutKey}` to auto-bind on the
    // caller. In practice the removal regressed
    // `navi-lending:volo_liquid_staking` -- the very package the
    // bridge was originally introduced to fix. Specifically, the
    // `Priority_queue.new` body calls the loop helper
    // `Priority_queue.new.while_0` (a Mutation user) without ever
    // referencing AnyKey itself; auto-bind never fires on `new`'s
    // def, so the implicit is unresolved at the call site.
    //
    // Slice 4 deferred. To remove the bridge cleanly, the body of
    // `new` would need an AnyKey reference -- e.g. via slice 3's
    // real insert lambda or by threading the loop helper's
    // signature with an explicit AnyKey arg. Both are larger than
    // slice 4's scope.
    //
    // Gates:
    // 1. Callee is in a LEMMA package (Sui / MoveStdlib / Prover).
    //    Only lemma packages declare `variable {__MutKey : Type}`
    //    at file scope; user packages use the concrete `AnyKey`
    //    inductive from `Generated/AnyKey.lean` and have no
    //    `__MutKey` implicit on their defs. Emitting the named
    //    binding for user-package callees triggers Lean's
    //    'Invalid argument name `__MutKey`' error.
    // 2. Callee is a Mutation user, so its rendered def has the
    //    `{__MutKey}` implicit auto-bound -- directly (Mutation in its
    //    own body) or transitively (it calls a loop / continuation
    //    helper that does).
    // 3. The callee exposes NO `MutableRef` (`Mutation`) parameter. A
    //    MutableRef argument pins the key. A MutableRef result does not
    //    reliably do so: discarded and unannotated let-bound calls have no
    //    expected result type while Lean elaborates the call. Keying on the
    //    parameter list (rather than the caller's body, the historical
    //    `!caller_body_uses_mutation` gate) covers the continuation
    //    pattern where the caller uses Mutation but the specific call
    //    passes no Mutation argument -- e.g. `Sui.Display`
    //    `new_with_fields.aborts.cont_0 -> cont_0.cont_0`, which needs
    //    `__MutKey` only internally for a `while_0` it calls.
    // 4. The call is NOT a recursive self-call. Lean auto-threads the
    //    enclosing def's auto-bound `{__MutKey}` to a recursive
    //    reference and REJECTS a named `(__MutKey := ...)` on it
    //    ("Invalid argument name `__MutKey`"). The self-call resolves
    //    `__MutKey` on its own, so the bridge is both unnecessary and
    //    invalid there -- e.g. the recursive `...while_0` call inside
    //    `Sui.Display new_with_fields.aborts.while_0`.
    if needs_mutkey_named_implicit(fun, callee, ctx) {
        w.write(" (__MutKey := AnyKey)");
    }
    // `Type_name.{with_defining_ids, with_original_ids, get,
    // get_with_original_ids}` are universe-generic in `U`. Their
    // signatures take a `[HasCode U T]` constraint but the call
    // sites only know `T` -- no value-level param fixes `U`. To
    // make Lean's instance synthesis succeed deterministically
    // (and avoid ambiguous matches between `HasCode TyCode T` and
    // `HasCode ObjType T`), pin `U := _root_.TyCode` explicitly
    // at the call site. `TyCode` is the closed-form universe over
    // every type that flows through heterogeneous storage --
    // exactly the universe whose `reprStr` we encode as the
    // TypeName bytes.
    if callee_is_native {
        let cname = callee.name();
        let cmod = ctx.program.modules.get(&callee.module());
        let is_type_name_mod = cmod
            .map(|m| m.package_name == "MoveStdlib" && m.name == "type_name")
            .unwrap_or(false);
        // `bag::new` / `bag::new.aborts` are universe-generic in `U`
        // (`new {U} [Universe U] (ctx) : Bag U x TxContext`), but `U`
        // is fixed by NO argument -- a freshly-created Bag is empty, so
        // its element universe is undetermined at the call site and
        // `[Universe U]` synthesis gets stuck ("typeclass instance
        // problem is stuck" / "pattern variable contains metavariables"
        // on the discarded `Bag U` slot; cetus-clmm Partner / Rewarder
        // `create_*_for_test`). Pin `U` the same way as the type_name
        // natives.
        // `object_bag::new` shares Bag's shape exactly (`ObjectBag U` is
        // field-rendered over `_root_.BagU` and excluded from the df
        // universe the same way `bag::Bag` is -- see `render::ty` and
        // `dyn_type_universe`), so it needs the same pin (first caller:
        // ika `ika_system::display::create` -> `object_bag::new`).
        let is_bag_new = cmod
            .map(|m| m.package_name == "Sui" && (m.name == "bag" || m.name == "object_bag"))
            .unwrap_or(false)
            && matches!(cname, "new" | "new.aborts");
        // `sui::types::is_one_time_witness<T>(&w)` is universe-generic: it
        // decides OTW-ness structurally from `Universe.typeName` of `T`'s
        // code (Sui's rule: simple type name == module name upper-cased), so
        // no value arg fixes the universe. Pin it like the type_name natives.
        // The only caller is `package::claim` (a lemma fn carrying its own
        // abstract `{__TyU}`), so this resolves to `(U := __TyU)`.
        let is_types_otw = cmod
            .map(|m| m.package_name == "Sui" && m.name == "types")
            .unwrap_or(false)
            && cname == "is_one_time_witness";
        // `bcs::to_bytes<X>` (the GENERIC case -- `comparator::compare<X>`)
        // is universe-generic: `Bcs.to_bytes {U} [Universe U] (X)
        // [HasCode U X] (v)` dispatches via `Universe.serialize`, but no
        // value arg fixes `U`, so `[HasCode U X]` synthesis gets stuck.
        // Pin `U` like the type_name natives. (The `bcs::to_bytes<TypeName>`
        // case was already routed to `Type_name.to_bytes` and returned
        // above, so this only fires for the generic stub path.)
        let is_bcs_to_bytes = crate::render::native_models::is_bcs_to_bytes_model(ctx.program, fun);
        let needs_tycode_pin = (is_type_name_mod
            && matches!(
                cname,
                "get" | "with_defining_ids" | "get_with_original_ids" | "with_original_ids"
            ))
            || is_types_otw
            || is_bcs_to_bytes;
        if is_bag_new {
            // A freshly-created `Bag` is empty, so its element universe
            // is undetermined by any argument. Pin it to the BAG
            // universe `BagU` -- the universe a struct's `Bag` field is
            // typed over -- NOT `TyCode` (the df universe). User-package
            // callers pin the concrete `_root_.BagU` (they carry
            // `[HasCode _root_.BagU T]` on bag-tainted params and import
            // BagUInterp via `Generated.World`); lemma-package callers
            // pin their abstract bag universe `__BagU` (bound on the
            // function by render::function for bag-tainted lemma fns).
            // See `plans/lean-pipeline/split-bag-df-universes.md`.
            //
            // A lemma module that OWNS a `Bag` struct field already
            // imports `Generated.BagUInterp` (so `_root_.BagU` is in
            // scope) and renders that field as `Bag.Bag _root_.BagU`. A
            // fresh `bag::new` whose result flows into such a field must
            // therefore pin the concrete `_root_.BagU` too -- pinning the
            // abstract `__BagU` there would clash with the concrete field
            // type (e.g. generated `coin_registry::new_currency` storing
            // an empty `extra_fields` Bag). No new import / cycle: the
            // BagUInterp import already exists for the struct field.
            if ctx.caller_is_lemma_pkg && !ctx.caller_module_has_bag_struct {
                w.write(" (U := __BagU)");
            } else {
                w.write(" (U := _root_.BagU)");
            }
        } else if needs_tycode_pin {
            // The native is universe-generic with a non-outParam
            // `U`, so `U` MUST be pinned -- Lean can't infer it from
            // the `[HasCode U T]` constraint (type_name) alone.
            // User-package callers pin the concrete `_root_.TyCode`
            // (they carry `[HasCode _root_.TyCode T]` and import
            // TyCodeInterp). Lemma-package callers pin their own
            // abstract universe param `__TyU` (bound as `{__TyU}
            // [Universe __TyU] [Repr __TyU] ... [HasCode __TyU T]` on
            // the function, see render::function); the concrete
            // `TyCode` resolution then happens at the user call site,
            // avoiding a TyCodeInterp import / render cycle in the
            // lemma module.
            if ctx.caller_is_lemma_pkg {
                w.write(" (U := __TyU)");
            } else {
                w.write(" (U := _root_.TyCode)");
            }
        }
    }
    // Pin the universe `__TyU` of calls to translated tycode-tainted
    // lemma functions (e.g. `package::claim`, `package::from_module`,
    // `display::new_with_fields`, and the `.aborts` continuations split
    // out by stage 7). Those callees bind their own `{__TyU}` implicit
    // which Lean can't infer (HasCode.U is not an outParam), so without
    // a pin `HasCode ?__TyU T` synthesis gets stuck. The pin value
    // depends on the CALLER:
    //   * lemma caller carrying its own abstract `{__TyU}`
    //     (`caller_has_tycode_universe`): forward it -> `(__TyU := __TyU)`;
    //     concrete resolution happens at the eventual user call site.
    //   * user-package caller: pin the concrete closed universe
    //     `_root_.TyCode`. Every user `.lean` file imports
    //     `Generated.TyCodeInterp` (so `_root_.TyCode` + its `Universe` /
    //     `HasCode` instances are in scope) and every user type param
    //     already carries `[HasCode _root_.TyCode T]`. Without this,
    //     cetus-clmm `Pool` (`init` / `set_display` calling
    //     `Package.claim` / `from_module` / `Display.new_with_fields`,
    //     both base and `.aborts` variants) fails to compile -> the
    //     whole pool/factory/swap test cluster reports code-2000.
    //   * lemma caller WITHOUT its own `__TyU` (not tycode-tainted):
    //     leave unpinned -- such a module does NOT import TyCodeInterp
    //     (TyCodeInterp imports those lemma modules; pinning `_root_.TyCode`
    //     here would need the instances and form a cycle), and there is no
    //     `__TyU` to forward.
    if !callee_is_native {
        if let crate::ir::CalleeRef::Translated(_translated) = callee {
            // A translated callee that binds the abstract `{__TyU}` in its
            // signature needs the universe pinned by the caller. This fires
            // for BOTH a tainted type param AND a concrete tycode-native /
            // df-store reason -- `binds_tycode_universe` is the single
            // source of truth mirroring `render_function`'s `{__TyU}`
            // emission gate. The earlier check only saw tainted type
            // params, so callees like `coin_registry::finalize` (which bind
            // `{__TyU}` for a concrete `type_name::with_original_ids<bool>`)
            // were left unpinned -> "typeclass instance problem is stuck".
            let callee_has_tycode =
                crate::render::function::binds_tycode_universe(ctx.render_context, fun);
            if callee_has_tycode {
                if ctx.caller_has_tycode_universe {
                    w.write(" (__TyU := __TyU)");
                } else if !ctx.caller_is_lemma_pkg {
                    w.write(" (__TyU := _root_.TyCode)");
                }
            }
        }
    }
    for ta in type_args {
        w.write(" ");
        ctx.render_type_as_arg(ta, w);
    }
    let param_types: Vec<&crate::ir::Type> =
        callee.signature().params.iter().map(|p| &p.ty).collect();
    for (i, arg) in args.iter().enumerate() {
        w.write(" ");
        let expected = if callee_is_native {
            ExpectedForm::Value
        } else {
            match param_types.get(i).map(|ty| strip_singleton_tuple(ty)) {
                Some(crate::ir::Type::MutableRef { inner, .. }) => ExpectedForm::Mutation {
                    value_target: Some(inner),
                    slot: MutationSlot::DerivedFromExpr,
                },
                _ => ExpectedForm::Value,
            }
        };
        render_in_form(
            arg,
            expected,
            ExprSyntax::Contextual,
            ExprSyntax::Contextual,
            ctx,
            w,
        )?;
    }
    if needs_outer_parens {
        w.write(")");
    }
    Ok(())
}

pub(in crate::render) fn render_pack<W: Write>(
    struct_id: crate::ir::StructId,
    type_args: &[crate::ir::Type],
    variant: Option<usize>,
    fields: &[Expr],
    ctx: &ExprCtx<'_>,
    w: &mut LeanWriter<W>,
) -> RenderResult<()> {
    let struct_def = ctx
        .program
        .structs
        .get(&struct_id)
        .ok_or(RenderError::UnknownStructId { id: struct_id })?;
    let module =
        ctx.program
            .modules
            .get(&struct_def.module_id)
            .ok_or(RenderError::UnknownModId {
                id: struct_def.module_id,
            })?;
    let namespace = escape::module_render_namespace(&module.package_name, &module.name);
    let struct_name = escape::escape_struct_name(&struct_def.name);
    let qualified = if ctx.current_module == Some(namespace.as_str()) {
        struct_name.clone()
    } else {
        format!("{}.{}", namespace, struct_name)
    };

    if let Some(variant_tag) = variant {
        // Enum variant: `Namespace.Enum.Variant arg1 arg2 ...`.
        if struct_def.variants.is_none() {
            return Err(RenderError::PackVariantOnNonEnum { id: struct_id });
        }
        let v = struct_def
            .variant_by_tag(variant_tag)
            .ok_or(RenderError::UnknownVariant {
                struct_id,
                variant: variant_tag,
            })?;
        w.write("(");
        w.write(&qualified);
        w.write(".");
        w.write(&escape::escape_identifier(&v.name));
        // For a defunctionalized loop-step (`<Loop>_Step`) `cont` variant whose
        // fields preserve the loop's `Mutation`-typed `&mut` params verbatim
        // (see `aborts_defunctionalize.rs`), coerce each value-form arg up to
        // `Mutation` with `Mutation.ofLocal` so the pack type-checks. A genuine
        // `Mutation` arg is passed through unchanged, preserving its borrow
        // `loc` + `path` (the whole point of carrying `Mutation` here): the
        // matcher then threads it straight into the loop's recursive call,
        // keeping aliased `&mut`s in sync for in-loop conditional writebacks.
        // Scoped to loop-step structs so other packs render unchanged.
        let is_loop_step =
            crate::stage_07_dejumps::aborts_defunctionalize::is_loop_step_struct(struct_def);
        for (i, arg) in fields.iter().enumerate() {
            w.write(" ");
            let field_is_mut = is_loop_step
                && v.fields.get(i).map_or(false, |f| {
                    matches!(f.field_type, crate::ir::Type::MutableRef { .. })
                });
            if field_is_mut {
                render_in_form(
                    arg,
                    ExpectedForm::Mutation {
                        value_target: None,
                        slot: MutationSlot::DerivedFromExpr,
                    },
                    ExprSyntax::Contextual,
                    ExprSyntax::Contextual,
                    ctx,
                    w,
                )?;
            } else {
                render_with_parens_if_needed(arg, ctx, w)?;
            }
        }
        w.write(")");
        Ok(())
    } else {
        // Plain struct: anonymous constructor `{ f1 := v1, ... }` with
        // type ascription so Lean knows which structure we mean.
        //
        // Field values MUST go through `render_with_parens_if_needed`:
        // a bare `Expr::If` / `Expr::Match` / `Expr::BinOp` / Call
        // emits multi-token surface syntax whose tail (e.g. the
        // `else` arm of an if) would happily eat the trailing
        // `, <next field>` of the struct literal as part of its own
        // expression. Wrapping non-atomic field values in parens
        // gives Lean an unambiguous closing point so the comma
        // resumes the struct-literal parse.
        //
        // Surfaced on `scallop-lending:contracts/protocol`
        // (X/Ac_table.lean:122) -- a `Pack` whose `keys` field was an
        // `if ... then ... else MoveOption.none ...` produced
        // `..., keys := if c then a else b, with_keys := ... }`,
        // which Lean rejected with `unexpected identifier; expected
        // '}'` at the `with_keys` token.
        w.write("({ ");
        for (i, (f, v)) in struct_def.fields.iter().zip(fields.iter()).enumerate() {
            if i > 0 {
                w.write(", ");
            }
            w.write(&escape::escape_identifier(&f.name));
            w.write(" := ");
            render_with_parens_if_needed(v, ctx, w)?;
        }
        w.write(" : ");
        if type_args.is_empty() {
            w.write(&qualified);
        } else {
            w.write(&qualified);
            for ta in type_args {
                w.write(" ");
                ctx.render_type_as_arg(ta, w);
            }
        }
        w.write(" })");
        Ok(())
    }
}

pub(in crate::render) fn render_match<W: Write>(
    struct_id: crate::ir::StructId,
    selector: &Expr,
    cases: &[MatchArm],
    ctx: &ExprCtx<'_>,
    w: &mut LeanWriter<W>,
) -> RenderResult<()> {
    let struct_def = ctx
        .program
        .structs
        .get(&struct_id)
        .ok_or(RenderError::UnknownStructId { id: struct_id })?;
    if struct_def.variants.is_none() {
        return Err(RenderError::MatchOnNonEnum { id: struct_id });
    }
    let selector_type_args = match_selector_type_args(struct_id, selector, ctx);
    let target_ty = unify_match_arm_types(struct_id, selector, cases, ctx);

    w.write("match ");
    render_expr(selector, ctx, w)?;
    w.write(" with");
    w.indent(true);
    for arm in cases {
        let v = struct_def
            .variant_by_tag(arm.variant)
            .ok_or(RenderError::UnknownVariant {
                struct_id,
                variant: arm.variant,
            })?;
        w.write("| .");
        w.write(&escape::escape_identifier(&v.name));
        for b in &arm.bindings {
            w.write(" ");
            w.write(&escape::escape_identifier(b));
        }
        w.write(" =>");
        w.indent(true);
        let result = with_match_arm_binding_types(
            &arm.bindings,
            &v.fields,
            &selector_type_args,
            ctx,
            || {
                if let Some(target) = &target_ty {
                    render_inner_block_with_target_ty(&arm.body, target, ctx, w)
                } else {
                    render_inner_block(&arm.body, ctx, w)
                }
            },
        );
        w.dedent(false);
        result?;
        w.newline();
    }
    w.dedent(false);
    Ok(())
}

pub(in crate::render) fn match_selector_type_args(
    struct_id: crate::ir::StructId,
    selector: &Expr,
    ctx: &ExprCtx<'_>,
) -> Vec<crate::ir::Type> {
    rendered_match_selector_type_args(struct_id, selector, ctx.program, &ctx.var_types.borrow())
}

pub(in crate::render) fn with_match_arm_binding_types<T>(
    bindings: &[crate::ir::VarId],
    fields: &[crate::ir::Field],
    type_args: &[crate::ir::Type],
    ctx: &ExprCtx<'_>,
    render: impl FnOnce() -> RenderResult<T>,
) -> RenderResult<T> {
    let previous = {
        let mut var_types = ctx.var_types.borrow_mut();
        match_arm_binding_types(bindings, fields, type_args)
            .into_iter()
            .map(|(binding, ty)| {
                let previous = var_types.insert(binding.clone(), ty);
                (binding, previous)
            })
            .collect::<Vec<_>>()
    };

    let result = render();
    let mut var_types = ctx.var_types.borrow_mut();
    for (binding, prior) in previous.into_iter().rev() {
        if let Some(ty) = prior {
            var_types.insert(binding, ty);
        } else {
            var_types.remove(&binding);
        }
    }
    result
}

pub(in crate::render) fn fresh_generated_binders(
    ctx: &ExprCtx<'_>,
    count: usize,
    active: impl IntoIterator<Item = String>,
) -> Vec<String> {
    let mut reserved = std::collections::BTreeSet::new();
    reserved.extend(
        ctx.var_types
            .borrow()
            .keys()
            .map(|binding| escape::escape_identifier(binding.as_ref())),
    );
    reserved.extend(
        ctx.var_overrides
            .values()
            .map(|binding| escape::escape_identifier(binding)),
    );
    reserved.extend(active);

    let mut binders = Vec::with_capacity(count);
    let mut index = 0;
    while binders.len() < count {
        let candidate = format!("__f{index}");
        index += 1;
        if reserved.insert(candidate.clone()) {
            binders.push(candidate);
        }
    }
    binders
}

/// Emit a variant-aware update for an `EnumField` writeback. Produces
/// `match <parent> with | .<VariantName> f0 ... fN => .<VariantName> f0
/// ... (field_index := <new>) ... fN | _ => <parent>`. The fallthrough
/// case preserves the parent unchanged when the runtime variant
/// doesn't match -- borrow-checked Move code shouldn't hit that path,
/// but having it makes the Lean output total.
pub(in crate::render) fn render_enum_field_update<W: Write>(
    struct_id: crate::ir::StructId,
    variant_tag: usize,
    field_index: usize,
    parent: &Expr,
    new_value: &Expr,
    ctx: &ExprCtx<'_>,
    w: &mut LeanWriter<W>,
) -> RenderResult<()> {
    let struct_def = ctx
        .program
        .structs
        .get(&struct_id)
        .ok_or(RenderError::UnknownStructId { id: struct_id })?;
    if struct_def.variants.is_none() {
        return Err(RenderError::MatchOnNonEnum { id: struct_id });
    }
    let v = struct_def
        .variant_by_tag(variant_tag)
        .ok_or(RenderError::UnknownVariant {
            struct_id,
            variant: variant_tag,
        })?;
    if field_index >= v.fields.len() {
        return Err(RenderError::UnsupportedConstruct {
            what: "EnumField writeback: field_index out of range",
        });
    }
    let vname = escape::escape_identifier(&v.name);
    let bindings = fresh_generated_binders(ctx, v.fields.len(), std::iter::empty());
    w.write("(match ");
    render_val_unwrap_if_mutable_inline(parent, ctx, w)?;
    w.write(" with");
    w.indent(true);
    w.write(&format!("| .{}", vname));
    for b in &bindings {
        w.write(" ");
        w.write(b);
    }
    w.write(" => .");
    w.write(&vname);
    for (i, b) in bindings.iter().enumerate() {
        w.write(" ");
        if i == field_index {
            render_val_unwrap_if_mutable_inline(new_value, ctx, w)?;
        } else {
            w.write(b);
        }
    }
    w.newline();
    w.write("| other => other");
    w.dedent(false);
    w.write(")");
    Ok(())
}
