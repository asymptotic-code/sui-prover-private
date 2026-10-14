//! Small render utilities (split from `expr/mod.rs`,
//! `plans/lean-pipeline/renderer-split.md`).

use super::{render_expr, render_in_form, ExpectedForm, ExprCtx, ExprSyntax, RuntimeBorrowSource};
use crate::ir::{BorrowEdge, BorrowNode, Expr, Program, VarId};
use crate::render::escape;
use crate::render::writer::LeanWriter;
use crate::render::{RenderError, RenderResult};
use std::fmt::Write;

/// Render a `BorrowNode` as the underlying mutation value at an
/// `IsParent` callsite -- both `LocalRoot(name)` and `Reference(name)`
/// map to the local with that name.
/// For `IsParent` on a `BorrowNode::SpecGlobalRoot`, the renderer
/// emits a literal `false` instead of trying to construct a Mutation
/// value -- ghost variables aren't valid parents of local-rooted
/// borrows in any well-typed Move program. For LocalRoot / Reference
/// nodes, returns the underlying VarId name; the caller wraps in
/// `Mutation.isParent`.
///
/// Returns `Ok(true)` iff the caller should emit a full
/// `Mutation.isParent <parent> <edge> <child>` shape, or `Ok(false)`
/// if a literal Bool has already been written.
pub(in crate::render) fn render_borrow_node_as_mutation_local<W: Write>(
    node: &BorrowNode,
    ctx: &ExprCtx<'_>,
    w: &mut LeanWriter<W>,
) -> RenderResult<bool> {
    let _ = ctx;
    match node {
        BorrowNode::LocalRoot(name) | BorrowNode::Reference(name) => {
            w.write(&escape::escape_identifier(name));
            Ok(true)
        }
        BorrowNode::GlobalRoot(id) => Err(RenderError::UnthreadedGlobal {
            operation: "GlobalRoot IsParent",
            id: *id,
        }),
        BorrowNode::SpecGlobalRoot { .. } => {
            // Ghost vars are never structurally a parent of a
            // local-rooted Mutation. Emit `false` as the whole
            // IsParent expression.
            w.write("false");
            Ok(false)
        }
    }
}

/// Render a `BorrowEdge` as an `Edge` literal value for `IsParent`
/// callsites. Runtime keys / indices are stamped with `default`
/// placeholders -- they're never inspected by `isParent`'s structural
/// comparison except via the constructor tag.
pub(in crate::render) fn render_edge_literal<W: Write>(
    edge: &BorrowEdge,
    ctx: &ExprCtx<'_>,
    w: &mut LeanWriter<W>,
) -> RenderResult<()> {
    match edge {
        BorrowEdge::Direct => {
            w.write(&format!("(@Prover.Mutation.Edge.direct {})", key_slot(ctx)));
            Ok(())
        }
        BorrowEdge::StructField {
            struct_id,
            field_index,
        } => {
            w.write(&format!(
                "(@Prover.Mutation.Edge.structField {} {} {})",
                key_slot(ctx),
                crate::render::struct_idx::struct_tag_ref(*struct_id, ctx.program),
                field_index
            ));
            Ok(())
        }
        BorrowEdge::EnumField {
            struct_id,
            variant,
            field_index,
        } => {
            w.write(&format!(
                "(@Prover.Mutation.Edge.enumField {} {} {} {})",
                key_slot(ctx),
                crate::render::struct_idx::struct_tag_ref(*struct_id, ctx.program),
                variant,
                field_index
            ));
            Ok(())
        }
        BorrowEdge::VecIndex => {
            w.write(&format!(
                "(@Prover.Mutation.Edge.vecIndex {} 0)",
                key_slot(ctx)
            ));
            Ok(())
        }
        BorrowEdge::MapKey { .. } => {
            // Placeholder AnyKey -- see BorrowMapKey case at top of file.
            w.write(&format!(
                "(@Prover.Mutation.Edge.mapKey {} {})",
                key_slot(ctx),
                key_unit_val(ctx)
            ));
            Ok(())
        }
        BorrowEdge::Hyper(_) => {
            // Unreachable in well-formed IR: the only caller is the
            // `Expr::IsParent` arm above, which routes Hyper edges
            // to `render_edge_chain_literal` (emitting a Lean
            // `List (Edge Key)` for `Mutation.isParentHyper`).
            // Stage 2's `normalize_borrow_edge` also collapses any
            // `Hyper([single])` chain before we get here. Surface
            // the violation explicitly rather than emitting silent
            // garbage Lean.
            Err(RenderError::UnsupportedConstruct {
                what: "render_edge_literal called on Hyper edge -- callers must dispatch to render_edge_chain_literal",
            })
        }
    }
}

/// Render a list of `BorrowEdge`s as a Lean `List (Edge Key)` literal
/// for `IsParent`-on-Hyper callsites. Each element goes through
/// `render_edge_literal`, so static edges become typed
/// `Edge.<ctor>` values and dynamic edges (`vecIndex` / `mapKey`)
/// get placeholder payloads -- same convention and same pre-existing
/// payload-imprecision as the single-edge case.
///
/// Stage 2's `normalize_borrow_edge` guarantees nested Hypers have
/// already been flattened and interior `Direct` edges dropped, but
/// we defensively re-flatten here in case future IR mutations
/// re-introduce them.
pub(in crate::render) fn render_edge_chain_literal<W: Write>(
    edges: &[BorrowEdge],
    ctx: &ExprCtx<'_>,
    w: &mut LeanWriter<W>,
) -> RenderResult<()> {
    fn flatten<'a>(es: &'a [BorrowEdge], out: &mut Vec<&'a BorrowEdge>) {
        for e in es {
            match e {
                BorrowEdge::Hyper(inner) => flatten(inner, out),
                _ => out.push(e),
            }
        }
    }
    let mut flat: Vec<&BorrowEdge> = Vec::with_capacity(edges.len());
    flatten(edges, &mut flat);
    // Drop native-map content-placeholder StructFields (`.S#<Map>.f<size>`
    // immediately preceding a `.mapKey`): the runtime Mutation path built by
    // `borrowMapKey` does NOT materialize them, and `Mutation.isParentHyper`
    // is LENGTH-gated (`child.path.length == parent.path.length + es.length`),
    // so an extra template edge makes the ancestor check FALSE and the gated
    // conditional writeback silently drops (ledger item 34 (ii) pending /
    // (iii) candidate). Canonical convention: NEITHER the isParentHyper
    // template nor the runtime path carries the placeholder -- kept in
    // lockstep with `render_encodable_df_writeback`'s runtime-path pattern.
    let mut kept: Vec<&BorrowEdge> = Vec::with_capacity(flat.len());
    for i in 0..flat.len() {
        let is_placeholder = match flat[i] {
            BorrowEdge::StructField { struct_id, .. } => {
                crate::render::expr::writeback::native_map_ops_for_struct(*struct_id, ctx.program)
                    .is_some()
                    && matches!(flat.get(i + 1), Some(BorrowEdge::MapKey { .. }))
            }
            _ => false,
        };
        if !is_placeholder {
            kept.push(flat[i]);
        }
    }
    w.write("[");
    for (i, e) in kept.iter().enumerate() {
        if i > 0 {
            w.write(", ");
        }
        render_edge_literal(e, ctx, w)?;
    }
    w.write("]");
    Ok(())
}

/// Recover the runtime index `Expr` for a `WriteBack { edge: VecIndex, child }`.
/// Reads the function-renderer pre-walk's `borrow_sources` map. Falls back to
/// `0` if `child` isn't a `Var` we recorded -- the renderer can't synthesise a
/// real index in that case, and the resulting Lean will compile (the writeback
/// becomes a no-op) but won't match the source semantics. Stage 2 should ensure
/// every `&mut`-typed temp that flows into a `WriteBack { VecIndex }` has a
/// `BorrowVecIndex` binding in scope; this path is defensive.
///
/// The index is a `BoundedNat (2^N)` in our IR -- emit it as
/// `(<expr>).val` so the prelude's plain `Nat` argument accepts it.
/// Same unwrap as `Expr::BorrowVecIndex` / `Expr::UpdateVec`.
/// Resolve a writeback child var to the `VecIndex` borrow index it
/// ultimately came from -- directly (`child` IS the borrow result) or
/// through ONE `borrow_mut_derivatives` hop (`child` is the result of a
/// mutating-native passthrough like `vec_set::insert` applied to a
/// `borrowVecIndex`'d payload). The derivative map is built transitively
/// (`collect_borrow_mut_derivatives` follows existing derivatives), so a
/// single hop reaches the originating borrow source.
///
/// Covers the `MoveOption.borrow_mut` payload case: `option::borrow_mut`
/// borrows `vec[0]` (recorded as `VecIndex { index: 0 }`), and a wit_table
/// `.keys` update mutates it via `vec_set::insert` before writing back.
/// Without following the derivative the writeback fell through to the
/// path-recovering `writeBackVecIndex` with a path-less `ofLocal`
/// child -> no `.vecIndex` edge -> identity no-op -> the inserted key was
/// silently dropped (`wit_table::keys` stayed empty -> scallop
/// collateral_types/debt_types empty -> spurious borrow_too_much).
pub(in crate::render) fn resolve_vec_index_source<'a>(
    name: &VarId,
    ctx: &'a ExprCtx<'_>,
) -> Option<&'a Expr> {
    if let Some(RuntimeBorrowSource::VecIndex { index }) = ctx.borrow_sources.get(name) {
        return Some(index);
    }
    if let Some(src) = ctx.borrow_mut_derivatives.get(name) {
        if let Some(RuntimeBorrowSource::VecIndex { index }) = ctx.borrow_sources.get(src) {
            return Some(index);
        }
    }
    // Fall back to `mutref_rebind_source`: unlike
    // `borrow_mut_derivatives` it does not require the rebind's source
    // to be a recognized container borrow source, and it chases
    // through if-join phis (the conditional `table::remove` /
    // `table::add` rebind of a `vector::borrow_mut` element). Without
    // this hop the VecIndex writeback for such a child falls through
    // to the path-recovering `writeBackVecIndexLast` with a path-less
    // `ofLocal` wrap and silently drops the write.
    if let Some(src) = ctx.mutref_rebind_source.get(name) {
        if let Some(RuntimeBorrowSource::VecIndex { index }) = ctx.borrow_sources.get(src) {
            return Some(index);
        }
    }
    None
}

pub(in crate::render) fn render_vec_index_for_child<W: Write>(
    child: &Expr,
    ctx: &ExprCtx<'_>,
    w: &mut LeanWriter<W>,
) -> RenderResult<()> {
    if let Expr::Var(name) = child {
        if let Some(index) = resolve_vec_index_source(name, ctx) {
            w.write("(");
            render_expr(index, ctx, w)?;
            w.write(").val");
            return Ok(());
        }
    }
    w.write("0");
    Ok(())
}

/// True when the renderer would fall back to hardcoded `0` for the
/// vec-index recovery -- i.e. the child variable's borrow site isn't
/// in `ctx.borrow_sources` (typically because the borrow happened in
/// a parent function and the child was passed as a parameter). In
/// that case the caller should switch to `writeBackVecIndex`,
/// which recovers the index from `child.path` at runtime (matching
/// Boogie's `ReadVec($child->p, LenVec($parent->p))` semantics).
pub(in crate::render) fn vec_index_recoverable(child: &Expr, ctx: &ExprCtx<'_>) -> bool {
    if let Expr::Var(name) = child {
        resolve_vec_index_source(name, ctx).is_some()
    } else {
        false
    }
}

/// Does `ty` mention `TypeParameter(idx)` anywhere in its structure?
pub(in crate::render) fn ir_type_references_param(ty: &crate::ir::Type, idx: u16) -> bool {
    use crate::ir::Type;
    match ty {
        Type::TypeParam(i) => *i == idx,
        Type::Vector(inner) | Type::Reference(inner) => ir_type_references_param(inner, idx),
        Type::MutableRef { inner, root } => {
            ir_type_references_param(inner, idx) || ir_type_references_param(root, idx)
        }
        Type::Tuple(es) => es.iter().any(|t| ir_type_references_param(t, idx)),
        Type::Struct { type_args, .. } => {
            type_args.iter().any(|t| ir_type_references_param(t, idx))
        }
        _ => false,
    }
}

/// True iff `struct_id` is a plain struct with a PHANTOM type parameter
/// -- a type param that no field's type references. Lean's structure
/// update `{ x with f := v }` cannot infer such a param from the fields,
/// so it leaves a fresh metavar (`don't know how to synthesize implicit
/// argument t_tv0`). Struct-update sites for these structs must ascribe
/// the result type. (Move `struct Asset<phantom T>` is the canonical
/// case: T marks the asset's coin type but is stored in no field.)
pub(in crate::render) fn struct_has_phantom_param(
    struct_id: crate::ir::StructId,
    program: &Program,
) -> bool {
    let Some(s) = program.structs.get(&struct_id) else {
        return false;
    };
    if s.type_params.is_empty() {
        return false;
    }
    (0..s.type_params.len() as u16).any(|i| {
        !s.fields
            .iter()
            .any(|f| ir_type_references_param(&f.field_type, i))
    })
}

/// Recover the runtime map-key `Expr` for a `WriteBack { edge: MapKey, child }`.
/// Same fallback rule as `render_vec_index_for_child` -- `default` if the
/// `child` isn't recognised.
pub(in crate::render) fn render_map_key_for_child<W: Write>(
    child: &Expr,
    ctx: &ExprCtx<'_>,
    w: &mut LeanWriter<W>,
) -> RenderResult<()> {
    if let Expr::Var(name) = child {
        if let Some(RuntimeBorrowSource::MapKey { key, .. }) = ctx.borrow_sources.get(name) {
            render_with_parens_if_needed(key, ctx, w)?;
            return Ok(());
        }
    }
    w.write("default");
    Ok(())
}

/// Derive a deterministic `Loc.localRoot` slot index from a `VarId`.
///
/// Stage 2 names every Move temp `$tN` via `temp_name(t)`. We parse
/// `N` back out so distinct locals produce distinct slots in the
/// generated Lean (`Mutation.isParent` then returns `false` between
/// them as expected). For VarIds that don't match the `$tN` pattern
/// (e.g. user-named parameters introduced by stage 5 SSA) we fall
/// back to a stable djb2-style hash of the name modulo 2^31 -- the
/// hash space is large enough that collisions between distinct names
/// are vanishingly rare and the consequence of a collision is only a
/// spurious `isParent` equality, never a soundness issue.
pub(in crate::render) fn slot_from_var(name: &VarId) -> u32 {
    let s: &str = name;
    if let Some(rest) = s.strip_prefix("$t") {
        if let Ok(n) = rest.parse::<u32>() {
            return n;
        }
    }
    let mut h: u32 = 5381;
    for b in s.as_bytes() {
        h = h.wrapping_mul(33).wrapping_add(*b as u32);
    }
    h & 0x7fff_ffff
}

/// Render the `Key` slot for a `Mutation.*` prelude call.
pub(in crate::render) fn key_slot(_ctx: &ExprCtx<'_>) -> &'static str {
    // Always emit the polymorphic `AnyKey` notation. The earlier
    // conditional `Unit` substitution (for lemma functions whose
    // signature didn't reference Mutation, to dodge the Lean
    // "can't synthesize implicit __MutKey" error at downstream
    // callers) regressed 10 modules because cross-function lemma
    // calls couldn't unify a Unit-keyed Mutation with an
    // AnyKey-keyed one. Until a fuller solution lands (per-function
    // AnyKey monomorphisation, or explicit Key-at-call-site), keep
    // the polymorphic form. The MoveStdlib::Ascii / MoveOption
    // interaction that triggers the synthesis failure stays as a
    // known limitation -- see the scallop sweep report.
    "AnyKey"
}

/// Render a placeholder key value (used as the runtime key argument
/// for `borrowMapKey` / `writeBackMapKey` / `Edge.mapKey` calls when
/// the actual key is wrapped in the placeholder `AnyKey.unit`).
/// Mirrors `key_slot`: `AnyKey.unit` for signature-using-Mutation
/// functions (which carry the polymorphic Key via auto-bound
/// `__MutKey`), `()` (the unit value) otherwise.
pub(in crate::render) fn key_unit_val(_ctx: &ExprCtx<'_>) -> &'static str {
    // Constant `AnyKey.unit` -- mirror of `key_slot`. See that
    // function's docstring for why the conditional `()` substitution
    // was reverted. Used at sites where the key TYPE isn't concrete
    // enough to emit a real `AnyKey.k_<mangled>` constructor (struct
    // keys, generic-function bodies with `TypeParam` keys, the
    // `apply_edge_inner_only::Direct` cross-type bridge).
    //
    // Slice 2 of item B (see plans/lean-pipeline/item-b-real-anykey-work-plan.md)
    // migrated sites that DO have a concrete primitive `key_type` to
    // `render_anykey_wrap` below. Sites still calling `key_unit_val`
    // either don't have a key type (`Direct` cross-type bridge) or
    // have a non-concrete one (struct keys; deferred to slice 6).
    "AnyKey.unit"
}

/// Slice 2 of item B: emit a real `AnyKey.k_<mangled> <key_expr>`
/// wrap when `key_type` is a concrete primitive (per
/// `render::mutation::is_concrete_key_type`); fall back to
/// `AnyKey.unit` otherwise, discarding `key_expr`.
///
/// The mangle matches the constructor name emitted by
/// `render::mutation::render_any_key_file` for the same key type --
/// both functions consult `render::mutation::any_key_ctor_name` so
/// they can't drift.
///
/// `key_expr` is rendered with `render_with_parens_if_needed` so it
/// composes cleanly inside larger `(@Mutation.borrowMapKey ... <wrap> ...)`
/// emissions.
pub(in crate::render) fn render_anykey_wrap<W: Write>(
    key_expr: &Expr,
    key_type: &crate::ir::Type,
    ctx: &ExprCtx<'_>,
    w: &mut LeanWriter<W>,
) -> RenderResult<()> {
    if crate::render::mutation::is_concrete_key_payload(key_type) {
        if ctx.caller_is_lemma_pkg {
            // LEMMA package: `AnyKey` is the abstract `__MutKey` type
            // variable, which has no `k_<ctor>` constructors. Inject the
            // concrete key through the `IntoKey` typeclass instead; the
            // enclosing function carries `[IntoKey __MutKey <payload>]`
            // (emitted by `function.rs`) and the per-package
            // `Generated.AnyKey` supplies the instance at the user-package
            // call site. See `Prelude.Mutation.IntoKey`.
            w.write("(IntoKey.intoKey ");
            render_with_parens_if_needed(key_expr, ctx, w)?;
            w.write(")");
        } else {
            w.write(&format!(
                "({}.{} ",
                key_slot(ctx),
                crate::render::mutation::any_key_ctor_name(key_type, ctx.program)
            ));
            render_with_parens_if_needed(key_expr, ctx, w)?;
            w.write(")");
        }
    } else if let crate::ir::Type::TypeParam(_) = key_type {
        // Generic key type (e.g. `wit_table::borrow_mut`'s key param):
        // wrap the runtime key via the `ToAnyKey` typeclass. The
        // enclosing generic function carries `[ToAnyKey <param>]` (see
        // `typeparam_is_mapkey` / function.rs), so at the concrete
        // instantiation Lean resolves the real `AnyKey.k_<...>`
        // constructor instead of the `AnyKey.unit` placeholder. The
        // downstream `writeBackMapKey` recovery matches on that
        // constructor; with the placeholder it fell through to the
        // identity no-op and silently dropped the mutation.
        // In a LEMMA package the class is the prelude's `IntoKey` over the
        // abstract `__MutKey` (see function.rs); `ToAnyKey` is not in scope.
        w.write(if ctx.caller_is_lemma_pkg {
            "(IntoKey.intoKey "
        } else {
            "(ToAnyKey.toAnyKey "
        });
        render_with_parens_if_needed(key_expr, ctx, w)?;
        w.write(")");
    } else {
        // Non-concrete struct / aggregate key: keep the placeholder
        // (deferred -- slice 6 of item B).
        let _ = key_expr;
        w.write(key_unit_val(ctx));
    }
    Ok(())
}

pub(in crate::render) fn field_name(
    struct_id: crate::ir::StructId,
    field_index: usize,
    ctx: &ExprCtx<'_>,
) -> String {
    let s = ctx
        .program
        .structs
        .get(&struct_id)
        .unwrap_or_else(|| panic!("unknown struct id {}", struct_id));
    s.fields
        .get(field_index)
        .unwrap_or_else(|| {
            panic!(
                "field index {} out of range for struct {}",
                field_index, s.name
            )
        })
        .name
        .clone()
}

/// Render the struct's Lean type name with `_` placeholders for each
/// type parameter, suitable for a lambda binder annotation:
///
///   `(fun s : <Pkg>.<Mod>.<Struct> _ _ ... => s.<field>)`
///
/// The struct's qualified Lean name follows the same rules as
/// `render_type` for `Type::Struct`: same-module structs drop the
/// namespace prefix, cross-module structs are qualified with
/// `<package>.<module>.<Name>`. Type arguments are emitted as `_`
/// holes since we don't track per-call-site type-arg bindings on
/// `Expr::BorrowField`; Lean's elaborator unifies them with the
/// concrete `S` inferred from the surrounding `borrowField` call.
pub(in crate::render) fn render_struct_type_with_holes<W: Write>(
    struct_id: crate::ir::StructId,
    ctx: &ExprCtx<'_>,
    w: &mut LeanWriter<W>,
) {
    let s = ctx
        .program
        .structs
        .get(&struct_id)
        .unwrap_or_else(|| panic!("unknown struct id {}", struct_id));
    let module = ctx
        .program
        .modules
        .get(&s.module_id)
        .expect("render_struct_type_with_holes: struct's module is missing");
    let escaped_name = escape::escape_struct_name(&s.name);
    let namespace = escape::module_render_namespace(&module.package_name, &module.name);
    let qualified = if ctx.current_module == Some(namespace.as_str()) {
        escaped_name
    } else {
        format!("{}.{}", namespace, escaped_name)
    };
    if s.type_params.is_empty() {
        w.write(&qualified);
    } else {
        w.write("(");
        w.write(&qualified);
        for _ in &s.type_params {
            w.write(" _");
        }
        w.write(")");
    }
}

/// Wrap `e` in parens iff it would parse as multiple tokens at the
/// surrounding precedence level.
pub(in crate::render) fn render_with_parens_if_needed<W: Write>(
    e: &Expr,
    ctx: &ExprCtx<'_>,
    w: &mut LeanWriter<W>,
) -> RenderResult<()> {
    if needs_parens(e) {
        w.write("(");
        render_expr(e, ctx, w)?;
        w.write(")");
    } else {
        render_expr(e, ctx, w)?;
    }
    Ok(())
}

pub(in crate::render) fn needs_parens(e: &Expr) -> bool {
    // Atoms render as a single token. Everything else self-wraps.
    !matches!(
        e,
        Expr::Var(_)
            | Expr::Const(_)
            | Expr::Unit
            | Expr::Tuple(_)
            | Expr::Pack { .. }
            | Expr::Field { .. }
    )
}

/// Render `e` and append `.val` if `e`'s type is `Type::MutableRef`.
/// Used at field projection sites and as arguments to natives that
/// expect the underlying value rather than the wrapped Mutable.
///
/// Two cases handled:
///
/// - `Var(v)` where `v`'s declared type is `MutableRef`: the common
///   case (function parameter or post-stage-3 SSA rebind target).
/// - Any other expression whose `rendered_type_of` returns
///   `MutableRef`. This fires after stage-7 spec-extraction inlines
///   a `Stmt::Let { value: WriteRef(...) }` into a predicate -- the
///   inlined expression is a `WriteRef`, not a `Var`, but its type
///   is still `Mutation T`. Without this case, the renderer would
///   emit `(WriteRef-rendering).field` which Lean rejects because
///   Mutation has no such field (only `loc`, `path`, `val`).
pub(in crate::render) fn render_with_val_unwrap_if_mutable<W: Write>(
    e: &Expr,
    ctx: &ExprCtx<'_>,
    w: &mut LeanWriter<W>,
) -> RenderResult<()> {
    render_in_form(
        e,
        ExpectedForm::Value,
        ExprSyntax::Contextual,
        ExprSyntax::Contextual,
        ctx,
        w,
    )
}

/// Like `render_with_val_unwrap_if_mutable` but inline-only (no extra
/// parens around the expression). Used inside `{ X with field := v }`
/// rebuilds where the value position needs to be the unwrapped form
/// directly.
pub(in crate::render) fn render_val_unwrap_if_mutable_inline<W: Write>(
    e: &Expr,
    ctx: &ExprCtx<'_>,
    w: &mut LeanWriter<W>,
) -> RenderResult<()> {
    render_in_form(
        e,
        ExpectedForm::Value,
        ExprSyntax::Inline,
        ExprSyntax::Inline,
        ctx,
        w,
    )
}
