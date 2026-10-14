//! `Expr` / `Block` / `Stmt` / `BlockTail` -> Lean syntax.
//!
//! The renderer consumes normalized post-pipeline IR. Stage 7 eliminates
//! loops, jumps, and inner Returns by extracting recursive helpers; stage 8
//! only finalizes World-write effects over that helper graph. Encountering an
//! unlowered control-flow form is a pipeline invariant violation.
//! Mutable-reference operations render
//! through the typed `Prover.Mutation.Mutation` prelude model.

use std::fmt::Write;

use ethnum::U256;

use std::collections::BTreeMap;

use crate::ir::{BinOp, BitOp, BlockTail, BorrowEdge, Const, Expr, Program, Stmt, UnOp, VarId};

use super::escape;
use super::ty;
use super::writer::LeanWriter;
use super::{RenderError, RenderResult};

mod mutation_uses;
pub(super) use mutation_uses::*;
mod coercion;
pub(super) use coercion::*;
mod sources;
pub(super) use sources::*;
pub(crate) mod types;
pub(super) use types::*;
mod util;
pub(super) use util::*;
mod call;
pub(super) use call::*;
mod writeback;
pub(super) use writeback::*;
mod body;
pub(super) use body::*;

pub(super) const LARGE_UINT_OPAQUE_THRESHOLD: u128 = 4096;

/// Keep short vector literals readable while avoiding very large runs of the
/// same rendered constant in generated Lean.
const VECTOR_REPLICATE_THRESHOLD: usize = 4;

pub(super) fn opaque_uint_const_alias(bits: u32, value: &U256) -> Option<String> {
    if *value > U256::from(LARGE_UINT_OPAQUE_THRESHOLD) {
        Some(format!("large_uint_u{}_{}", bits, u256_to_decimal(value)))
    } else {
        None
    }
}

pub(super) fn collect_opaque_uint_const_aliases(
    c: &Const,
    out: &mut BTreeMap<String, (u32, String)>,
) {
    match c {
        Const::UInt { bits, value } => {
            if let Some(alias) = opaque_uint_const_alias(*bits, value) {
                out.insert(alias, (*bits, u256_to_decimal(value)));
            }
        }
        Const::Vector { elems, .. } => {
            for elem in elems {
                collect_opaque_uint_const_aliases(elem, out);
            }
        }
        _ => {}
    }
}

/// Per-function rendering context.
pub(super) struct ExprCtx<'a> {
    pub render_context: &'a super::context::RenderContext<'a>,
    pub program: &'a Program,
    pub current_module: Option<&'a str>,
    pub type_params: Option<&'a [String]>,
    /// Function's IR-level return type, used to insert
    /// `Mutation.ofLocal` wraps in tail-position tuples where the
    /// body builds a value-form slot but the return shape declares
    /// `Mutation T`. See
    /// `render_tail_tuple_coerced_to_return_type` for the bridge.
    pub function_return_type: Option<&'a crate::ir::Type>,
    /// Rendered name of the function's trailing `world : World`
    /// parameter, if it has one (set by the function renderer).
    /// `BlockTail::Abort` tails forward this instead of synthesizing
    /// an empty `default` World -- see `write_abort_tail_default`.
    pub world_param: Option<String>,
    /// `VarId` -> display name overrides. The function renderer
    /// populates this with each parameter's `(var, name)` pair so the
    /// body uses the user-visible parameter name (`a`) instead of the
    /// SSA temp the upstream pipeline picked (`$t0`).
    pub var_overrides: &'a BTreeMap<VarId, String>,
    /// `VarId` -> declared type. Initially populated from the
    /// function's params; the renderer updates it in place as it
    /// walks each `Stmt::Let` so a subsequent reference uses the
    /// type of the most recent binding (Move IR commonly shadows the
    /// same name with a different type after a call).
    pub var_types: std::cell::RefCell<BTreeMap<VarId, crate::ir::Type>>,
    /// `VarId` -> runtime borrow source. Populated by a pre-walk
    /// over the function body that records every
    /// `Stmt::Let { pattern: [v], value: Expr::BorrowVecIndex { index, .. } }`
    /// and `Stmt::Let { pattern: [v], value: Expr::BorrowMapKey { key, key_type, .. } }`.
    /// The `WriteBack` arms read this to recover the runtime index /
    /// key when rendering `Mutation.writeBackVecIndex` /
    /// `Mutation.writeBackMapKey` calls. Cf. Boogie's
    /// `ReadVec(child.p, ...)` pattern; we keep the recovery in the
    /// renderer because the IR carries the value on the borrow
    /// construction site, not on the writeback edge.
    pub borrow_sources: BTreeMap<VarId, RuntimeBorrowSource>,
    /// `VarId` -> origin of a 2-slot let-destructuring whose second
    /// slot is the `Mutation P` pass-through of a borrow_mut chain
    /// (`Dynamic_field.borrow_mut` or a Move wrapper like
    /// `linked_table::borrow_mut_node`). Populated by a pre-walk over
    /// the function body. Read by `apply_edge_inner_only`'s
    /// cross-type bridge branch to substitute the placeholder
    /// `writeBackMapKey` with a proper `Prelude.TypedMap.set` on the
    /// parent's ghost `dynamic_fields[_N]` field. See
    /// `BorrowMutOrigin` for the rationale.
    pub borrow_mut_origins: BTreeMap<VarId, BorrowMutOrigin>,
    /// `VarId` -> source borrowed-mut `VarId`: maps a let-bound
    /// variable whose RHS is `<mutating_native> <src>.val ...` to
    /// `src` (the borrowed Mutation that the new value logically
    /// replaces). Populated by `collect_borrow_mut_derivatives` at
    /// function-render entry.
    ///
    /// Used by `apply_edge_inner_only`'s writeback dispatch to
    /// route a derived value (e.g. the result of `Bag.add`) through
    /// the upstream borrow's `BorrowMutOrigin` even when the
    /// derived variable itself wasn't directly produced by
    /// `borrowMapKey`. Without this, the renderer wraps the value
    /// in `Mutation.ofLocal` (empty path) and the writeback can't
    /// recover the `.mapKey k` edge at runtime.
    ///
    /// Transitive: chained mutating-native calls all resolve to
    /// the original borrow source.
    pub borrow_mut_derivatives: BTreeMap<VarId, VarId>,
    /// `VarId` -> source borrowed-mut `VarId`: maps a let-bound
    /// variable whose RHS is a `&mut`-param mutating native
    /// (`table::add`, `bag::add`, ...) applied to a Mutation var
    /// `src` to that `src`. Unlike `borrow_mut_derivatives`, this is
    /// NOT gated on `src` being a recognized container borrow
    /// source -- any Mutation-typed first arg qualifies (e.g. a
    /// user function returning `&mut Table`, like
    /// `liquidity_miner::get_reward_table_mut`).
    ///
    /// Read ONLY by the `Expr::IsParent` child renderer: when the
    /// child is a value-form mutating-native rebind result, wrap it
    /// as `Mutation.set src child` (which preserves `src`'s borrow
    /// path) instead of `Mutation.ofLocal` (which resets loc+path
    /// and makes `isParent` always false -- silently dropping the
    /// conditional writeback). See `collect_mutref_rebind_sources`.
    pub mutref_rebind_source: BTreeMap<VarId, VarId>,
    /// True iff the function being rendered is a `.aborts` companion
    /// (its `name.ends_with(".aborts")`). The Class A peephole in
    /// `apply_edge_inner_only` skips its ghost-field rewrite in this
    /// case -- `.aborts` only needs a Bool result, and the let-bindings
    /// it lifts (`let t_K := MoveOption.borrow tail.prev`) may carry
    /// would-abort expressions that the function body's original
    /// if-guard kept from being evaluated. The baseline placeholder
    /// `writeBackMapKey (fun m _ _ => m)` ignores its key/value args
    /// (Lean DCEs them); the new ghost-field rewrite uses the key
    /// directly, which forces evaluation and panics on `sorry` when
    /// the key came from a `MoveOption.borrow none`. Skipping the
    /// rewrite preserves the baseline behavior for `.aborts` only --
    /// the regular function body still gets the correct rewrite.
    pub is_aborts: bool,
    /// `VarId` -> `VarId`: map a let-bound `BorrowLoc(x)` temp to
    /// its underlying source `x` when **every** use of the bound
    /// variable in the function body is a `ReadRef(Var(...))` (i.e.
    /// `.val` access). For such temps the `Mutation.ofLocal` wrap
    /// + `.val` unwrap is a pure round-trip that exists in the IR
    /// only because stage 3 didn't peephole the wrap away. The
    /// renderer drops the `Stmt::Let` and rewrites every
    /// `ReadRef(Var(v))` to the bare `Var(source)` -- eliminating
    /// the `Mutation.ofLocal AnyKey ...` reference. This also
    /// prevents Lean's auto-bound `__MutKey` from being attached to
    /// functions whose body has no genuine Mutation usage in its
    /// own signature (see the Ascii / MoveOption.destroy_some case
    /// in `lake-build-remaining-errors.md`).
    pub redundant_borrowloc: BTreeMap<VarId, VarId>,
    /// `VarId` -> declared "target type" inferred from how the var
    /// flows into the function's tail (or other expected-type
    /// context). Populated by `compute_var_target_types` before
    /// rendering: when the function body's tail is a Tuple whose
    /// `i`-th slot is `Var(v)` and the function return type's
    /// `i`-th slot is `Mutation T` (for some `T`), then
    /// `var_target_types[v] = Mutation T`. This lets `Stmt::Let`
    /// rendering propagate the target backward into a tuple-
    /// producing RHS (typically an `Expr::If` / `Expr::Match`) so
    /// each arm's tail tuple slot gets coerced to match.
    pub var_target_types: BTreeMap<VarId, crate::ir::Type>,
    /// Transitive set of FunIds whose Lean def carries the
    /// auto-bound `{__MutKey : Type}` implicit -- either directly
    /// (sig / body has Mutation IR ops) or via a transitive call
    /// to another set member. Computed from the whole program by
    /// `compute_mutation_users`. Used by `render_call` for the same
    /// gate.
    pub mutation_users: &'a std::collections::BTreeSet<crate::ir::FunId>,
    pub world_type_overrides: &'a ty::WorldTypeOverrides,
    /// True when the function being rendered lives in a lemma
    /// package (Sui, MoveStdlib, Prover, ...). Lemma-package callers
    /// of `type_name::*` natives are universe-POLYMORPHIC: their
    /// signature binds `{__TyU} [Universe __TyU] [HasCode __TyU T]`
    /// (see render::function), so the type_name call must NOT pin
    /// `(U := _root_.TyCode)` -- doing so would ignore `__TyU` and
    /// also require a TyCodeInterp import (render cycle). User-package
    /// callers DO pin (they carry `[HasCode _root_.TyCode T]` and
    /// import TyCodeInterp).
    pub caller_is_lemma_pkg: bool,
    /// True when the function being rendered binds the abstract
    /// universe `{__TyU}` (lemma package + at least one type param
    /// tainted by a `type_name::*` call). Used by `render_call` to
    /// thread `(__TyU := __TyU)` into calls to other tycode-tainted
    /// lemma functions (e.g. `.aborts` continuations), whose `{__TyU}`
    /// implicit Lean can't infer (HasCode.U is not an outParam).
    pub caller_has_tycode_universe: bool,
    /// True when the function being rendered lives in a module that
    /// imports `Generated.BagUInterp` -- i.e. the module has a struct
    /// with a `Bag` / `ObjectBag` field (`module_has_bag_struct`). In
    /// that module `_root_.BagU` is already in scope and the module's
    /// own bag fields render as the concrete `Bag.Bag _root_.BagU`, so a
    /// fresh `bag::new` must ALSO pin the concrete `_root_.BagU` (like a
    /// user package) -- NOT the abstract `__BagU`. Without this, a lemma
    /// module that owns a bag struct (e.g. generated `coin_registry`)
    /// pins `(U := __BagU)` on `bag::new` while its struct field expects
    /// `Bag.Bag _root_.BagU`, a type mismatch. No new import / cycle:
    /// the BagUInterp import already exists for the struct field.
    pub caller_module_has_bag_struct: bool,
    /// FunId of the function currently being rendered. Used by
    /// `render_call` to suppress the `(__MutKey := AnyKey)` bridge on
    /// a recursive self-call: Lean auto-threads the enclosing def's
    /// auto-bound `{__MutKey}` to the recursive reference and REJECTS a
    /// named `(__MutKey := ...)` on it ("Invalid argument name
    /// `__MutKey`"). The bridge is only valid/needed on cross-function
    /// calls.
    pub current_fn_id: crate::ir::FunId,
}

impl<'a> ExprCtx<'a> {
    pub fn type_render_context(&self) -> ty::TypeRenderContext<'a> {
        ty::TypeRenderContext::new(
            self.program,
            self.current_module,
            self.type_params,
            self.world_type_overrides,
        )
    }

    pub fn render_type_as_arg<W: Write>(&self, ty: &crate::ir::Type, w: &mut LeanWriter<W>) {
        ty::render_type_as_arg_in(ty, &self.type_render_context(), w);
    }

    pub fn type_to_string(&self, ty: &crate::ir::Type) -> String {
        ty::type_to_string_in(ty, &self.type_render_context())
    }
}

/// Runtime data recovered by the `borrow_sources` pre-walk -- one
/// per `&mut` temp that ultimately flows into a `WriteBack`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) enum RuntimeBorrowSource {
    /// Vector borrow: `vector::borrow_mut(v, i)`.
    VecIndex { index: Expr },
    /// Map borrow: `table::borrow_mut(t, k)` /
    /// `dynamic_field::borrow_mut(p, k)` / etc. `key_type` is the
    /// Move type used to look up the `AnyKey` constructor for
    /// wrapping `key` at the WriteBack callsite.
    MapKey {
        key: Expr,
        key_type: crate::ir::Type,
    },
}

/// Recorded at a `Stmt::Let { pattern: [_, Some(parent_alias)], value: Call(...) }`
/// destructuring whose second slot is a `Mutation P` pass-through that flows into
/// a later `WriteBack { node: Reference(parent_alias), edge: Direct, .. }` cross-
/// type bridge -- the classic shape of a `dynamic_field::borrow_mut` call (direct
/// or through a thin Move wrapper like `linked_table::borrow_mut_node`).
///
/// The IR loses the original map key across the borrow_mut call boundary, so by
/// the time `apply_edge_inner_only` reaches the cross-type bridge it can only
/// emit a placeholder `writeBackMapKey` that discards the mutation. This origin
/// table threads the key from the destructuring site forward so the bridge can
/// substitute a real `Prelude.TypedMap.set` on the parent's ghost
/// `dynamic_fields[_N]` field instead (ghost era; those render fns
/// were deleted 2026-06-11 -- the ghost shape is extinct since 2C).
#[derive(Debug, Clone)]
pub(super) struct BorrowMutOrigin {
    /// Key expression -- the last positional arg of the borrow_mut-shaped call.
    /// Works for both the native `Dynamic_field.borrow_mut(parent, key)` and
    /// for thin wrappers `wrap_fn(parent, key)` that ultimately delegate to it.
    pub key: Expr,
}

/// Render `e` into `w`. Atomic expressions render as-is; compound
/// expressions wrap themselves in parens where needed for unambiguous
/// parsing.
pub(super) fn render_expr<W: Write>(
    e: &Expr,
    ctx: &ExprCtx<'_>,
    w: &mut LeanWriter<W>,
) -> RenderResult<()> {
    match e {
        Expr::Borrow { step, base } => {
            use crate::ir::path::PathStep;
            match step {
                PathStep::Field {
                    struct_id,
                    field_index,
                } => {
                    // `(@Mutation.borrowField AnyKey _ _ <base> SID OFFSET (fun s => s.<f>))`.
                    // `borrowField` requires `base : Mutation Key S`. When
                    // `base` is a Mutation-typed Var, pass it directly.
                    // When it's a raw struct (e.g. the IR contains
                    // `Expr::BorrowField { base: Var(s), .. }` where `s` is
                    // a plain local rather than a `&mut` temp), wrap with
                    // `ofLocal 0 base` so the result is a valid Mutation.
                    // This preserves the legacy `Mutable.mk` permissiveness
                    // about base types while still flowing through the
                    // typed Mutation prelude. Real stage-2 output usually
                    // preceeds `BorrowField` with a `BorrowLoc`, but the
                    // wrapper makes the renderer robust to both shapes.
                    let field = field_name(*struct_id, *field_index, ctx);
                    let fld = escape::escape_identifier(&field);
                    // Peel a singleton tuple if present: stage 3's
                    // `augment_signatures` produces `Tuple([MutableRef T])`
                    // for functions whose only augmented return is a single
                    // `&mut` slot. The bare-`MutableRef` matches! would miss
                    // it; the renderer would then wrap the call in another
                    // `ofLocal`, producing `Mutation (Mutation T)` against
                    // `borrowField`'s `S` slot. Surfaced on Market.lean and
                    // Pending_active_set.lean for stage-7-inlined Calls
                    // used as a `BorrowField` base.
                    w.write(&format!(
                        "(@Prover.Mutation.Mutation.borrowField {} _ _ ",
                        key_slot(ctx)
                    ));
                    render_in_form(
                        base,
                        ExpectedForm::Mutation {
                            value_target: None,
                            slot: MutationSlot::DerivedFromExpr,
                        },
                        ExprSyntax::Contextual,
                        ExprSyntax::Contextual,
                        ctx,
                        w,
                    )?;
                    w.write(&format!(
                        " {} {} ",
                        crate::render::struct_idx::struct_tag_ref(*struct_id, ctx.program),
                        field_index
                    ));
                    // Annotate the lambda binder with the parent struct type
                    // so Lean doesn't fall back to `Mutation` when elaborating
                    // `s.<field>`. Without the annotation, deferred elaboration
                    // of `borrowField`'s implicit `S` (when the base passes
                    // through `Mutation.ofLocal _ _ (...)` with a complex
                    // value-form sub-expression) can cause Lean to default `s`
                    // to the outer `Mutation` type and reject the projection
                    // with `Mutation.<field> does not exist`. Pinning `s :
                    // <StructQualified> _ _ ...` (with one `_` per type
                    // param) tells the elaborator exactly which struct's
                    // field we're projecting; the type-arg placeholders are
                    // unified with whatever `S` resolves to.
                    w.write("(fun s : ");
                    render_struct_type_with_holes(*struct_id, ctx, w);
                    w.write(" => s.");
                    w.write(&fld);
                    w.write("))");
                    Ok(())
                }
                PathStep::VariantField {
                    struct_id,
                    variant,
                    field_index,
                } => {
                    let struct_def = ctx
                        .program
                        .structs
                        .get(struct_id)
                        .ok_or(RenderError::UnknownStructId { id: *struct_id })?;
                    if struct_def.variants.is_none() {
                        return Err(RenderError::MatchOnNonEnum { id: *struct_id });
                    }
                    let variant_def =
                        struct_def
                            .variant_by_tag(*variant)
                            .ok_or(RenderError::UnknownVariant {
                                struct_id: *struct_id,
                                variant: *variant,
                            })?;
                    if *field_index >= variant_def.fields.len() {
                        return Err(RenderError::UnsupportedConstruct {
                            what: "Borrow VariantField: field_index out of range",
                        });
                    }
                    let bindings = (0..variant_def.fields.len())
                        .map(|index| format!("__vf{index}"))
                        .collect::<Vec<_>>();
                    w.write(&format!(
                        "(@Prover.Mutation.Mutation.borrowEnumField {} _ _ ",
                        key_slot(ctx)
                    ));
                    render_in_form(
                        base,
                        ExpectedForm::Mutation {
                            value_target: None,
                            slot: MutationSlot::DerivedFromExpr,
                        },
                        ExprSyntax::Contextual,
                        ExprSyntax::Contextual,
                        ctx,
                        w,
                    )?;
                    w.write(&format!(
                        " {} {variant} {field_index} ",
                        crate::render::struct_idx::struct_tag_ref(*struct_id, ctx.program)
                    ));
                    w.write("(fun s : ");
                    render_struct_type_with_holes(*struct_id, ctx, w);
                    w.write(" => match s with | .");
                    w.write(&escape::escape_identifier(&variant_def.name));
                    for binding in &bindings {
                        w.write(" ");
                        w.write(binding);
                    }
                    w.write(" => ");
                    w.write(&bindings[*field_index]);
                    w.write(" | _ => default))");
                    Ok(())
                }
                PathStep::VecIndex(index) => {
                    // Prelude `borrowVecIndex : (m : Mutation Key (List T)) -> (i : Nat) -> ...`
                    // auto-binds `{Key}` and `{T}` from its argument types
                    // (`[Inhabited T]` is an instance arg, synthesised). So the
                    // `@`-form is `@borrowVecIndex {Key} {T} (m) (i)` = four
                    // positional args. Mirrors the `Mutation.set` shape
                    // (`AnyKey _ <parent> <value>`).
                    //
                    // The index is a `BoundedNat (2^64)` in our IR -- unwrap
                    // with `.val` to feed the prelude's plain `Nat`. Same
                    // adjustment as `Expr::UpdateVec` makes.
                    //
                    // The trailing `_` is the `[Inhabited T]` instance arg
                    // (exposed by `@` in Lean 4); Lean synthesises it.
                    //
                    // Auto-wrap a non-Mutation `base` with `Mutation.ofLocal`
                    // -- same idiom as `apply_edge_inner_only::VecIndex` and
                    // `BorrowField`. Stage-3 mut-to-let or a native return
                    // can leave `base` as a bare `List T` value where the
                    // prelude expects `Mutation Key (List T)`.
                    w.write(&format!(
                        "(@Prover.Mutation.Mutation.borrowVecIndex {} _ ",
                        key_slot(ctx)
                    ));
                    render_in_form(
                        base,
                        ExpectedForm::Mutation {
                            value_target: None,
                            slot: MutationSlot::DerivedFromExpr,
                        },
                        ExprSyntax::Contextual,
                        ExprSyntax::Contextual,
                        ctx,
                        w,
                    )?;
                    w.write(" (");
                    render_expr(index, ctx, w)?;
                    w.write(").val _)");
                    Ok(())
                }
                PathStep::MapKey {
                    key,
                    key_type,
                    value_type,
                    df_value,
                } => {
                    // Slice 2 of item B (plans/lean-pipeline/item-b-real-anykey-work-plan.md):
                    // for concrete primitive `key_type` we now emit a real
                    // `AnyKey.k_<mangled> key` wrap, threading the runtime key
                    // value through. For non-concrete keys (struct, TypeParam,
                    // or aggregates containing them) we fall back to
                    // `AnyKey.unit` and discard the key value (the original
                    // pre-slice-2 behaviour). `render_anykey_wrap` is the
                    // single point of dispatch.
                    // Placeholder AnyKey: the lookup lambda receives `k : AnyKey`
                    // / `()` which can't be cast to the container's concrete key.
                    // The sound stub is `(fun _ _ => default)` -- ignore both args
                    // and return `Inhabited.default` of the value type.
                    //
                    // **V must be passed explicitly.** The prelude signature is
                    // `borrowMapKey : Mutation Key S -> Key -> (S -> Key -> V) -> Mutation Key V`.
                    // With `S` inferred from `base : Mutation Key S` and the lookup
                    // body `default : V`, V is otherwise unconstrained until a
                    // `.val.<field>` projection on the result resolves it -- and
                    // Lean defaults V to S in the pre-projection elaboration,
                    // producing `<S>.<field>` not-a-field errors at every field
                    // access on a map-borrowed value. Pulling V from the IR's
                    // `value_type` constrains the call locally, so `default` and
                    // downstream projections see the correct concrete value type.
                    // Auto-wrap a non-Mutation `base` with `Mutation.ofLocal`
                    // -- same idiom as `apply_edge_inner_only::MapKey` and
                    // `BorrowField`. A bare `Bag.Bag` / `Table.Table` value
                    // (from a native return or `.val` projection) needs to
                    // be lifted to `Mutation Key S` before `borrowMapKey`
                    // applies.
                    w.write(&format!(
                        "(@Prover.Mutation.Mutation.borrowMapKey {} _ ",
                        key_slot(ctx)
                    ));
                    ctx.render_type_as_arg(value_type, w);
                    w.write(" ");
                    render_in_form(
                        base,
                        ExpectedForm::Mutation {
                            value_target: None,
                            slot: MutationSlot::DerivedFromExpr,
                        },
                        ExprSyntax::Contextual,
                        ExprSyntax::Contextual,
                        ctx,
                        w,
                    )?;
                    w.write(" ");
                    render_anykey_wrap(key, key_type, ctx, w)?;
                    // DF borrow (`df_value: Some(v)`): the borrowed value is
                    // supplied EXTERNALLY by `v` -- a prior `store_(bag_)borrow`
                    // read from World -- not by a lookup into `base.val`. This
                    // map-key borrow only EXTENDS the path (so the df key rides
                    // `child.path` for the escaping writeback to recover); the
                    // value is `v`. Skip the smart in-value lookup below.
                    if let Some(dfv) = df_value {
                        let v_text = render_expr_to_string(&Expr::Var(dfv.clone()), ctx)?;
                        w.write(&format!(" (fun _ _ => {}))", v_text));
                        return Ok(());
                    }
                    // SMART LOOKUP: when the base IS a Sui native map (Table,
                    // VecMap, Bag, ObjectTable, ObjectBag), emit the
                    // corresponding `<Native>.borrow` / `<Native>.get` from the
                    // native prelude; otherwise fall back to the placeholder
                    // `(fun _ _ => default)` -- only safe when the borrowed
                    // value isn't subsequently read (e.g. the borrow is purely
                    // structural for path tracking). (The former ghost
                    // `dynamic_fields[_N]` strategies were deleted in step-2
                    // slice C -- no struct carries ghost fields anymore.)
                    //
                    // Each native-map entry maps `(package, module, struct_name)`
                    // to the prelude function name that performs the real lookup.
                    // Bag and ObjectBag store an opaque `id: UID` + `size: u64`
                    // (their underlying associations live in World), so their
                    // `borrow` returns `default`. ObjectTable likewise. Listing
                    // them here anyway means the renderer chooses a NAMED native
                    // fn over the anonymous placeholder -- observably equivalent
                    // but easier to read and trivial to upgrade. VecMap and
                    // Table have real storage (`contents : List Entry`,
                    // `dynamic_fields : List (K x V)` respectively); their
                    // borrows do real lookups.
                    use crate::ir::Type as IRType;
                    let base_struct_info = (|| {
                        let base_ty = rendered_type_of(base, ctx.program, &ctx.var_types.borrow())?;
                        let inner_ty = match base_ty {
                            IRType::MutableRef { inner, .. } => *inner,
                            t => t,
                        };
                        let (struct_id, type_args) = match &inner_ty {
                            IRType::Struct {
                                struct_id,
                                type_args,
                            } => (*struct_id, type_args.clone()),
                            _ => return None,
                        };
                        let s = ctx.program.structs.get(&struct_id)?;
                        let m = ctx.program.modules.get(&s.module_id)?;
                        Some((s, type_args, m.package_name.clone(), m.name.clone()))
                    })();
                    // Strategy: base IS a Sui native map. The lookup function
                    // name follows the native's own naming convention (Move's
                    // `borrow` for Table/Bag/ObjectTable/ObjectBag, `get` for
                    // VecMap). The renderer emits `_root_.<Mod>.<fn> _ _ p k_v`.
                    let native_lookup = base_struct_info.as_ref().and_then(|(s, _, pkg, modn)| {
                        if pkg != "Sui" {
                            return None;
                        }
                        match (modn.as_str(), s.name.as_str()) {
                            ("table", "Table") => Some("_root_.Table.borrow"),
                            ("vec_map", "VecMap") => Some("_root_.Vec_map.get"),
                            ("bag", "Bag") => Some("_root_.Bag.borrow"),
                            ("object_table", "ObjectTable") => Some("_root_.Object_table.borrow"),
                            ("object_bag", "ObjectBag") => Some("_root_.Object_bag.borrow"),
                            _ => None,
                        }
                    });
                    // Phase 4-partial: if the key type doesn't have a real
                    // AnyKey constructor (struct payloads stay deferred --
                    // see `mutation::is_concrete_key_type`), fall back to
                    // the no-lookup form. Match patterns on a missing ctor
                    // would otherwise produce
                    // `Invalid pattern: Expected a constructor or constant
                    // marked with [match_pattern]`.
                    // Lemma packages (translated framework modules like
                    // Sui::table_vec) render `AnyKey` as the abstract
                    // `__MutKey` type variable, which has no `k_<ctor>`
                    // constructors -- a match pattern on it fails with the
                    // same `Invalid pattern` error as a missing ctor. Route
                    // them to the closure-capture form below: the key expr
                    // is always in scope at the borrow site, and looking it
                    // up directly is definitionally what the match arm
                    // would have extracted from `IntoKey.intoKey <key>`.
                    let key_has_ctor = super::mutation::is_concrete_key_payload(key_type)
                        && !ctx.caller_is_lemma_pkg;
                    if let Some(native_fn) = native_lookup {
                        if key_has_ctor {
                            let key_ctor = super::mutation::any_key_ctor_name(key_type, ctx.program);
                            w.write(&format!(
                        " (fun p k => match k with | {}.{} k_v => {} _ _ p k_v | _ => default))",
                        key_slot(ctx),
                        key_ctor,
                        native_fn,
                    ));
                        } else {
                            // Non-concrete key (struct payload deferred from
                            // AnyKey, e.g. TypeName for `bag::borrow_mut`).
                            // The AnyKey wrap is `.unit` so the lambda's `k`
                            // is useless. Capture the actual key VALUE in
                            // the closure so the getter does
                            // `native_fn K V _ _ p <captured_key>` and the
                            // borrow returns the real entry (read from the
                            // native's real storage, e.g. `Bag.storage`).
                            // Without this, the placeholder returns default
                            // and `bag::borrow_mut(bag, type_name).balance`
                            // reads default Balance instead of the stored
                            // balance (Cluster D root-cause path 1).
                            let key_text = render_expr_to_string(key, ctx)?;
                            w.write(" (fun p _ => ");
                            w.write(native_fn);
                            w.write(" ");
                            ctx.render_type_as_arg(key_type, w);
                            w.write(" ");
                            ctx.render_type_as_arg(value_type, w);
                            w.write(" p ");
                            w.write(&key_text);
                            w.write("))");
                        }
                    } else {
                        w.write(" (fun _ _ => default))");
                    }
                    Ok(())
                }
            }
        }
        Expr::Update { step, base, value } => {
            use crate::ir::path::PathStep;
            match step {
                PathStep::Field {
                    struct_id,
                    field_index,
                } => {
                    // `{ base with field := value }` -- base must be the
                    // underlying struct, so if it's a Mutable-typed Var,
                    // unwrap with `.val` first.
                    let field_name = field_name(*struct_id, *field_index, ctx);
                    w.write("{ ");
                    render_val_unwrap_if_mutable_inline(base, ctx, w)?;
                    w.write(" with ");
                    w.write(&escape::escape_identifier(&field_name));
                    w.write(" := ");
                    render_expr(value, ctx, w)?;
                    w.write(" }");
                    Ok(())
                }
                PathStep::VecIndex(index) => {
                    w.write("(List.set ");
                    render_with_parens_if_needed(base, ctx, w)?;
                    w.write(" ");
                    // Lean's List.set takes Nat; BoundedNat needs `.val`.
                    w.write("(");
                    render_expr(index, ctx, w)?;
                    w.write(").val ");
                    render_with_parens_if_needed(value, ctx, w)?;
                    w.write(")");
                    Ok(())
                }
                PathStep::VariantField {
                    struct_id,
                    variant,
                    field_index,
                } => render_enum_field_update(
                    *struct_id,
                    *variant,
                    *field_index,
                    base,
                    value,
                    ctx,
                    w,
                ),
                PathStep::MapKey {
                    key,
                    key_type,
                    value_type,
                    df_value,
                } => {
                    // In-value map set: `(<Native>.set K V base key value)`.
                    // Value-form mirror of `UpdateVec`'s `List.set` -- no
                    // Mutation wrapper and no AnyKey discrimination, the
                    // key is statically present on the step. Producers
                    // (the stage-4 WriteBack lowering) construct these
                    // only against Sui native maps; df-backed updates are
                    // World-routed and must never reach here.
                    if df_value.is_some() {
                        return Err(RenderError::UnsupportedConstruct {
                            what: "Update{MapKey} with df_value (df updates are World-routed)",
                        });
                    }
                    let Some(native_set) = native_map_set_for(base, ctx) else {
                        return Err(RenderError::UnsupportedConstruct {
                            what: "Update{MapKey} on a non-native-map base (no in-value set primitive)",
                        });
                    };
                    w.write(&format!("({} ", native_set));
                    ctx.render_type_as_arg(key_type, w);
                    w.write(" ");
                    ctx.render_type_as_arg(value_type, w);
                    w.write(" ");
                    render_with_parens_if_needed(base, ctx, w)?;
                    w.write(" ");
                    render_with_parens_if_needed(key, ctx, w)?;
                    w.write(" ");
                    render_with_parens_if_needed(value, ctx, w)?;
                    w.write(")");
                    Ok(())
                }
            }
        }
        Expr::Var(name) => {
            // Peephole: redirect a dropped `let v := BorrowLoc(x)`
            // temp back to its underlying source `x`. See
            // `ExprCtx::redundant_borrowloc` and the matching
            // `Stmt::Let` skip / `ReadRef` redirect for context.
            let resolved: &VarId = ctx.redundant_borrowloc.get(name).unwrap_or(name);

            if let Some(display) = ctx.var_overrides.get(resolved) {
                w.write(&escape::escape_identifier(display));
            } else {
                w.write(&escape::escape_identifier(resolved));
            }
            Ok(())
        }

        Expr::Const(c) => render_const(c, w),

        Expr::Unit => {
            w.write("()");
            Ok(())
        }

        Expr::BinOp { op, lhs, rhs } => render_binop(*op, lhs, rhs, ctx, w),

        Expr::UnOp { op, operand } => render_unop(*op, operand, ctx, w),

        Expr::BitOp(op) => render_bitop(op, ctx, w),

        Expr::Tuple(elems) => {
            if elems.is_empty() {
                w.write("()");
                Ok(())
            } else if elems.len() == 1 {
                render_expr(&elems[0], ctx, w)
            } else {
                w.write("(");
                for (i, e) in elems.iter().enumerate() {
                    if i > 0 {
                        w.write(", ");
                    }
                    render_expr(e, ctx, w)?;
                }
                w.write(")");
                Ok(())
            }
        }

        Expr::Call {
            fun,
            type_args,
            args,
        } => render_call(*fun, type_args, args, ctx, w),

        Expr::Pack {
            struct_id,
            type_args,
            variant,
            fields,
        } => render_pack(*struct_id, type_args, *variant, fields, ctx, w),

        Expr::Unpack {
            struct_id,
            variant,
            value,
        } => {
            // Move's `Option { vec } = t` (or `Pair { a, b } = t`)
            // destructures a struct into its fields. The IR emits an
            // `Unpack` expression; the renderer projects each field
            // and emits the tuple. For a single-field struct, this
            // collapses to `t.field`; for multi-field, `(t.f1, t.f2, ...)`.
            let struct_def = ctx
                .program
                .structs
                .get(struct_id)
                .ok_or(RenderError::UnknownStructId { id: *struct_id })?;
            // Enum variant unpack: the IR emits `unpack ::vN value` INSIDE the
            // matched arm to project the selected variant's payload (the
            // enclosing Match already chose the variant). Render it as a match
            // on `value` that binds the variant's fields and returns them; the
            // `_ => default` arm is unreachable (value IS that variant) but
            // keeps the match exhaustive. cetus-dlmm `restriction::is_blocked`
            // (`BlockEntity::USER(addr)` / `POSITION(ID)`).
            if struct_def.variants.is_some() {
                let variant_tag = variant.ok_or(RenderError::UnsupportedConstruct {
                    what: "Expr::Unpack on enum without a variant tag",
                })?;
                let v =
                    struct_def
                        .variant_by_tag(variant_tag)
                        .ok_or(RenderError::UnknownVariant {
                            struct_id: *struct_id,
                            variant: variant_tag,
                        })?;
                let module = ctx.program.modules.get(&struct_def.module_id).ok_or(
                    RenderError::UnknownModId {
                        id: struct_def.module_id,
                    },
                )?;
                let namespace = escape::module_render_namespace(&module.package_name, &module.name);
                let struct_name = escape::escape_struct_name(&struct_def.name);
                let qualified = if ctx.current_module == Some(namespace.as_str()) {
                    struct_name
                } else {
                    format!("{}.{}", namespace, struct_name)
                };
                let ctor = escape::escape_identifier(&v.name);
                let nfields = v.fields.len();
                let binders: Vec<String> = (0..nfields).map(|i| format!("__upk{i}")).collect();
                w.write("(match ");
                render_with_parens_if_needed(value, ctx, w)?;
                w.write(&format!(" with | {qualified}.{ctor}"));
                for b in &binders {
                    w.write(" ");
                    w.write(b);
                }
                w.write(" => ");
                if nfields == 0 {
                    w.write("()");
                } else if nfields == 1 {
                    w.write(&binders[0]);
                } else {
                    w.write("(");
                    w.write(&binders.join(", "));
                    w.write(")");
                }
                w.write(" | _ => default)");
                return Ok(());
            }
            let n = struct_def.fields.len();
            if n == 0 {
                w.write("()");
                return Ok(());
            }
            if n == 1 {
                let field = struct_def.fields[0].name.clone();
                render_with_parens_if_needed(value, ctx, w)?;
                w.write(".");
                w.write(&escape::escape_identifier(&field));
                return Ok(());
            }
            w.write("(");
            for (i, f) in struct_def.fields.iter().enumerate() {
                if i > 0 {
                    w.write(", ");
                }
                render_with_parens_if_needed(value, ctx, w)?;
                w.write(".");
                w.write(&escape::escape_identifier(&f.name));
            }
            w.write(")");
            Ok(())
        }

        Expr::Field {
            struct_id,
            field_index,
            base,
        } => {
            // Field access: render `base.<field_name>`. When `base` is
            // a `Var(v)` referring to a parameter of `Mutable`-wrapper
            // type, unwrap with `.val` first so the field projection
            // hits the underlying struct (`q.val.table`, not
            // `q.table` which Lean reads as `Mutable.table`).
            let field = field_name(*struct_id, *field_index, ctx);
            render_with_val_unwrap_if_mutable(base, ctx, w)?;
            w.write(".");
            w.write(&escape::escape_identifier(&field));
            Ok(())
        }

        Expr::If {
            cond,
            then_branch,
            else_branch,
        } => {
            // Detect a {Mutation T, T} arm-type mismatch and pick
            // Mutation T as the unified type. Stage 3 mut-to-let
            // sometimes leaves one arm yielding a value-form (e.g.
            // a native return that strips MutableRef -- like
            // `Dynamic_field.add`) and the other yielding a
            // Mutation (the parameter). Without coercion, Lean
            // picks the then-arm's type and rejects the else-arm.
            // Pick Mutation T as the unified target: a downstream
            // consumer that needs value form can `.val`, and the
            // existing auto-unwrap in `render_call` /
            // `render_with_val_unwrap_if_mutable` does that
            // automatically once `var_types[v]` carries `MutableRef`.
            let target_ty = unify_if_arm_types(then_branch, else_branch, ctx);
            // Single-line short-form when BOTH branches are
            // `Block { stmts: [], tail: Value(_) }`. The multi-line
            // layout's `else` keyword sits at the writer's outer
            // indent column -- often well to the LEFT of `if`'s
            // column inside long expression chains (struct-literal
            // fields, BinOp operands). Lean's indent-sensitive
            // parser then either accepts the `else` (mostly inside
            // parens) or attaches it to the wrong `if`. Emitting
            // `if c then a else b` on one line sidesteps the
            // indentation rules entirely for the common
            // tail-only-arm case (the dominant shape in
            // path-precise abort companions). Multi-line
            // arms keep the original layout.
            // Treat blocks whose only stmts are pure evaluations
            // (Stmt::Eval / anonymous Stmt::Let) as "simple" --
            // `render_inner_block` drops those at emission time,
            // so the rendered Lean for such an arm is just the
            // tail expression. Without this look-through, deeply-
            // nested if's inside struct literals get multi-line
            // emission and break Lean's indentation parser.
            let stmts_drop_to_nothing =
                |stmts: &[Stmt]| -> bool { stmts.iter().all(is_erased_inner_discard) };
            let both_simple = matches!(then_branch.tail, BlockTail::Value(_))
                && stmts_drop_to_nothing(&then_branch.stmts)
                && matches!(else_branch.tail, BlockTail::Value(_))
                && stmts_drop_to_nothing(&else_branch.stmts);
            if both_simple {
                w.write("if ");
                render_expr(cond, ctx, w)?;
                w.write(" then ");
                if let Some(ref t) = target_ty {
                    render_inner_block_with_target_ty(then_branch, t, ctx, w)?;
                } else {
                    render_inner_block(then_branch, ctx, w)?;
                }
                w.write(" else ");
                if let Some(ref t) = target_ty {
                    render_inner_block_with_target_ty(else_branch, t, ctx, w)?;
                } else {
                    render_inner_block(else_branch, ctx, w)?;
                }
                return Ok(());
            }
            w.write("if ");
            render_expr(cond, ctx, w)?;
            w.write(" then");
            w.indent(true);
            if let Some(ref t) = target_ty {
                render_inner_block_with_target_ty(then_branch, t, ctx, w)?;
            } else {
                render_inner_block(then_branch, ctx, w)?;
            }
            w.dedent(false);
            w.newline();
            w.write("else");
            w.indent(true);
            if let Some(ref t) = target_ty {
                render_inner_block_with_target_ty(else_branch, t, ctx, w)?;
            } else {
                render_inner_block(else_branch, ctx, w)?;
            }
            w.dedent(false);
            Ok(())
        }

        Expr::Match {
            struct_id,
            selector,
            cases,
        } => render_match(*struct_id, selector, cases, ctx, w),

        Expr::While { .. } => Err(RenderError::UnsupportedConstruct {
            what: "Expr::While (post-stage-7 invariant violation)",
        }),

        // -------- mutable-reference machinery --------
        // All borrow / read / write ops lower to the typed-Mutation
        // prelude (`Prover.Mutation.Mutation.*`). The `Mutation`
        // abbreviation in each package's `Generated/AnyKey.lean`
        // resolves the `Key` parameter; the prelude's structure
        // field is named `val` so the legacy `r.val` accessor still
        // works against the new shape.
        Expr::BorrowLoc(name) => {
            // `(@Prover.Mutation.Mutation.ofLocal AnyKey _ <slot> x)`.
            // The slot index disambiguates distinct local-rooted
            // Mutations so `Mutation.isParent` correctly returns
            // `false` between them. We derive the slot from the
            // var's `$tN` suffix when present (stage 2's
            // `temp_name` produces this form for every temp); fall
            // back to a name hash for parameters / other VarIds.
            //
            // The wrapped `x` MUST honour `var_overrides`: when the
            // IR's BorrowLoc names a function parameter (post-SSA
            // var like `$t0_0`), the signature emits it under the
            // parameter's display name (e.g. `split_coin`). Without
            // the override lookup the renderer would write
            // `t_t0_0`, an undefined identifier in the body. Match
            // the lookup chain in `Expr::Var`'s rendering: first
            // check `redundant_borrowloc` for a redirect, then
            // `var_overrides`, fall back to escape.
            let slot = slot_from_var(name);
            w.write(&format!(
                "(@Prover.Mutation.Mutation.ofLocal {} _ {} ",
                key_slot(ctx),
                slot
            ));
            let resolved: &VarId = ctx.redundant_borrowloc.get(name).unwrap_or(name);
            if let Some(display) = ctx.var_overrides.get(resolved) {
                w.write(&escape::escape_identifier(display));
            } else {
                w.write(&escape::escape_identifier(resolved));
            }
            w.write(")");
            Ok(())
        }

        Expr::BorrowGlobal(id) => Err(RenderError::UnthreadedGlobal {
            operation: "BorrowGlobal",
            id: *id,
        }),

        Expr::ReadRef(inner) => {
            // Peephole: `ReadRef(Var(v))` where `v` was bound by a
            // dropped `BorrowLoc(x)` (the renderer's
            // `redundant_borrowloc` map captures this). Emit the
            // underlying source `x` directly -- no `.val` needed
            // because we never wrapped in the first place.
            if let Expr::Var(v) = inner.as_ref() {
                if let Some(src) = ctx.redundant_borrowloc.get(v) {
                    w.write(&escape::escape_identifier(src));
                    return Ok(());
                }
            }
            // `.val` works against the Mutation structure too (the
            // prelude field is named `val`). When inference shows
            // the operand isn't actually Mutation-typed (e.g., a
            // native returned an unwrapped value), render bare.
            render_in_form(
                inner,
                ExpectedForm::Value,
                ExprSyntax::Contextual,
                ExprSyntax::Contextual,
                ctx,
                w,
            )
        }

        Expr::WriteRef { reference, value } => {
            // Value-position only (stage 3 has already moved any
            // Stmt::Eval(WriteRef) into Stmt::Let { value: WriteRef }).
            // `Mutation.set` is the prelude alias for `updateValue`.
            //
            // The reference operand can be either an already-
            // Mutation-typed Var (typical post-stage-3) or the plain
            // underlying struct (when it comes from a native return
            // whose IR `MutableRef` slot was stripped). `Mutation.set`
            // requires a `Mutation Key T` parent; wrap with
            // `Mutation.ofLocal` when the inferred type isn't
            // already `MutableRef`. Same pattern as `BorrowField`
            // base unwrap and `render_writeback`'s `Reference`
            // parent.
            w.write(&format!(
                "(@Prover.Mutation.Mutation.set {} _ ",
                key_slot(ctx)
            ));
            render_in_form(
                reference,
                ExpectedForm::Mutation {
                    value_target: None,
                    slot: MutationSlot::DerivedFromExpr,
                },
                ExprSyntax::Contextual,
                ExprSyntax::Contextual,
                ctx,
                w,
            )?;
            w.write(" ");
            render_with_parens_if_needed(value, ctx, w)?;
            w.write(")");
            Ok(())
        }

        Expr::WriteBack {
            node,
            edge,
            child,
            world,
        } => {
            // The renderer's role here is to produce the parent's new
            // value computed from `child`'s current value + the edge.
            // `world.is_some()` => DF writeback: store into World instead
            // of the object value (see `render_writeback`).
            render_writeback(node, edge, child, world.as_ref(), ctx, w)
        }

        Expr::IsParent { node, edge, child } => {
            // For SpecGlobalRoot parents the helper writes `false`
            // directly and returns `Ok(false)`; in that case we
            // skip the surrounding `isParent` wrapper.
            let mut tmp = LeanWriter::new(String::new());
            let needs_wrap = render_borrow_node_as_mutation_local(node, ctx, &mut tmp)?;
            let node_text = tmp.into_inner();
            if !needs_wrap {
                w.write(&node_text);
                return Ok(());
            }
            // Hyper edges -> `Mutation.isParentHyper` with a
            // `List (Edge Key)` arg. Flat edges -> single-arg
            // `Mutation.isParent`. Stage 2's `normalize_borrow_edge`
            // (see `stage_02_ir_cfg::translate_op`) guarantees any
            // surviving `Hyper` chain has length >= 2 with no nested
            // Hypers and no interior `Direct` edges, so the chain-
            // literal emitter doesn't need to flatten -- but it does
            // anyway, defensively, in case future IR rewrites
            // re-introduce nested chains.
            // The prelude's `isParent` / `isParentHyper` expect the
            // child as a `Mutation Key T`. The IR carries `child` as
            // a `VarId`; depending on stage-3 mut-to-let's output,
            // the var's runtime type may be `Mutation T` (typical
            // post-borrow) OR a plain value-form `T` (when the
            // borrow's child was inlined to a struct slot's value).
            // Wrap with `Mutation.ofLocal` when the var's type is
            // value-form; otherwise pass the bare name.
            let child_expr = Expr::Var(child.clone());
            let child_is_mutation = rendered_form(&child_expr, ctx) == RenderedForm::Mutation;
            // When the child is a value-form result of a `&mut`-param
            // mutating native (e.g. `let $t7 = table::add($t7, ..)`),
            // `ofLocal` would reset its loc + path -- making `isParent`
            // always false and silently dropping a conditional
            // writeback. Recover the originating Mutation `src` via
            // `mutref_rebind_source` and wrap as `Mutation.set src
            // child`, which preserves `src`'s borrow path so `isParent`
            // can compare it. Only fires when `src` is itself a
            // Mutation; otherwise falls back to `ofLocal`. See
            // `collect_mutref_rebind_sources` (liquidity_miner
            // `support_coin` / `get_reward_manager_mut`).
            let rebind_src: Option<VarId> = if child_is_mutation {
                None
            } else {
                ctx.mutref_rebind_source.get(child).cloned().filter(|src| {
                    rendered_form(&Expr::Var(src.clone()), ctx) == RenderedForm::Mutation
                })
            };
            let render_child = |w: &mut LeanWriter<W>| -> RenderResult<()> {
                if let Some(src) = &rebind_src {
                    w.write(&format!(
                        "(@Prover.Mutation.Mutation.set {} _ ",
                        key_slot(ctx)
                    ));
                    w.write(&escape::escape_identifier(src));
                    w.write(" ");
                    w.write(&escape::escape_identifier(child));
                    w.write(")");
                } else {
                    render_in_form(
                        &child_expr,
                        ExpectedForm::Mutation {
                            value_target: None,
                            slot: MutationSlot::DerivedFromExpr,
                        },
                        ExprSyntax::Contextual,
                        ExprSyntax::Contextual,
                        ctx,
                        w,
                    )?;
                }
                Ok(())
            };
            match edge {
                BorrowEdge::Hyper(es) => {
                    w.write(&format!(
                        "(@Prover.Mutation.Mutation.isParentHyper {} _ _ _ ",
                        key_slot(ctx)
                    ));
                    w.write(&node_text);
                    w.write(" ");
                    render_edge_chain_literal(es, ctx, w)?;
                    w.write(" ");
                    render_child(w)?;
                    w.write(")");
                }
                _ => {
                    // `BorrowEdge::Direct` is the IDENTITY edge: upstream
                    // Boogie's codegen filters Direct edges out of the edge
                    // pattern and emits `$IsSameMutation` when only Direct
                    // remains (see `external-crates/move/move-prover/
                    // boogie-backend/src/bytecode_translator.rs` IsParent
                    // arm). The Lean prelude's `isParent` requires
                    // `child.path.length == parent.path.length + 1`, which
                    // Direct can never satisfy (it doesn't add a path
                    // entry), so wiring `IsParent .direct` through
                    // `isParent` always returns false and the gated
                    // WriteBack silently drops. Mirror Boogie: collapse to
                    // `isSameMutation` for Direct.
                    if matches!(edge, BorrowEdge::Direct) {
                        w.write(&format!(
                            "(@Prover.Mutation.Mutation.isSameMutation {} _ _ _ ",
                            key_slot(ctx)
                        ));
                        w.write(&node_text);
                        w.write(" ");
                        render_child(w)?;
                        w.write(")");
                        return Ok(());
                    }
                    w.write(&format!(
                        "(@Prover.Mutation.Mutation.isParent {} _ _ _ ",
                        key_slot(ctx)
                    ));
                    w.write(&node_text);
                    w.write(" ");
                    // Slice 2 of item B: for `MapKey` edges, recover the
                    // runtime key from `child.path` and emit a real
                    // `Edge.mapKey (AnyKey.k_<mangled> <key>)` literal
                    // when `key_type` is concrete primitive. Without
                    // this, slice 2's borrow-site change (which stores
                    // a real ctor in `child.path`) would mismatch
                    // `Edge.mapKey AnyKey.unit` here and isParent
                    // would return false where it used to return true.
                    if let BorrowEdge::MapKey { key_type, .. } = edge {
                        let child_expr = Expr::Var(child.clone());
                        let mut key_buf = LeanWriter::new(String::new());
                        render_map_key_for_child(&child_expr, ctx, &mut key_buf)?;
                        let key_str = key_buf.into_inner();
                        if super::mutation::is_concrete_key_payload(key_type) {
                            w.write(&format!(
                                "(@Prover.Mutation.Edge.mapKey {} ({}.{} {}))",
                                key_slot(ctx),
                                key_slot(ctx),
                                super::mutation::any_key_ctor_name(key_type, ctx.program),
                                key_str
                            ));
                        } else {
                            w.write(&format!(
                                "(@Prover.Mutation.Edge.mapKey {} {})",
                                key_slot(ctx),
                                key_unit_val(ctx)
                            ));
                        }
                    } else {
                        render_edge_literal(edge, ctx, w)?;
                    }
                    w.write(" ");
                    render_child(w)?;
                    w.write(")");
                }
            }
            Ok(())
        }

        Expr::ToProp(_) | Expr::ToBool(_) => Err(RenderError::UnsupportedConstruct {
            what: "ToProp/ToBool (unsupported rendered expression)",
        }),

        Expr::Quantifier {
            kind,
            binder,
            binder_type,
            domain,
            body,
        } => {
            use crate::ir::QuantDomain;
            use crate::ir::QuantifierKind as Q;

            // (kind, domain) -> prelude helper name. Mirrors the
            // legacy renderer's switch (see `move-prover-lean-backend`
            // `renderer/render.rs` Quantifier arm), adapted to the
            // new pipeline's collapsed shape (11 kinds x 3 domains).
            //
            // Two upstream variants collapse onto each (kind, Range)
            // slot:
            //   - `RangeMap` (index-only, `|i: u64| ...`)
            //     vs `MapRange` (vector-based, `|x: T| ...`)
            //   - `RangeCount` vs `CountRange`
            //   - `RangeSumMap` vs `SumMapRange`
            // The prelude has separate helpers per upstream variant
            // (`spec_range_map` vs `spec_map_range`, etc.). We
            // disambiguate by the binder's type: a `BoundedNat (2^64)`
            // binder is the index-only flavour (`spec_range_*`);
            // anything else is the vector-based flavour (`spec_*_range`).
            let is_index_binder = matches!(binder_type, crate::ir::Type::UInt(64));
            let helper_name: &str = match (*kind, domain) {
                (Q::Forall, QuantDomain::Unbounded) => "spec_forall",
                (Q::Exists, QuantDomain::Unbounded) => "spec_exists",

                // `VecRange` = `<op>_range!(vec, start, end, ..)` (vec
                // over an index window); `Range` = index-only
                // `range_<op>!(start, end, ..)` (only Map/Count/SumMap
                // have those upstream).
                (Q::Any, QuantDomain::Collection(_)) => "spec_any",
                (Q::Any, QuantDomain::VecRange { .. }) => "spec_any_range",

                (Q::All, QuantDomain::Collection(_)) => "spec_all",
                (Q::All, QuantDomain::VecRange { .. }) => "spec_all_range",

                (Q::Find, QuantDomain::Collection(_)) => "spec_find",
                (Q::Find, QuantDomain::VecRange { .. }) => "spec_find_range",

                (Q::FindIndex, QuantDomain::Collection(_)) => "spec_find_index",
                (Q::FindIndex, QuantDomain::VecRange { .. }) => "spec_find_index_range",

                (Q::FindIndices, QuantDomain::Collection(_)) => "spec_find_indices",
                (Q::FindIndices, QuantDomain::VecRange { .. }) => "spec_find_indices_range",

                (Q::Map, QuantDomain::Collection(_)) => "spec_map",
                (Q::Map, QuantDomain::VecRange { .. }) => "spec_map_range",
                (Q::Map, QuantDomain::Range { .. }) => "spec_range_map",

                (Q::Filter, QuantDomain::Collection(_)) => "spec_filter",
                (Q::Filter, QuantDomain::VecRange { .. }) => "spec_filter_range",

                (Q::Count, QuantDomain::Collection(_)) => "spec_count",
                (Q::Count, QuantDomain::VecRange { .. }) => "spec_count_range",
                (Q::Count, QuantDomain::Range { .. }) => "spec_range_count",

                (Q::SumMap, QuantDomain::Collection(_)) => "spec_sum_map",
                (Q::SumMap, QuantDomain::VecRange { .. }) => "spec_sum_map_range",
                (Q::SumMap, QuantDomain::Range { .. }) => "spec_range_sum_map",

                // Invalid combos: only Forall / Exists permit
                // `Unbounded`; the rest require a domain.
                (_, QuantDomain::Unbounded) => {
                    return Err(RenderError::UnsupportedConstruct {
                        what: "Quantifier: non-Forall/Exists with Unbounded domain",
                    });
                }
                // Upstream never emits `Forall`/`Exists` over a
                // bounded domain (see `translate_quant`: both upstream
                // variants map to `Unbounded`). Defensive arm: reject
                // explicitly rather than fall through and crash.
                (Q::Forall, _) | (Q::Exists, _) => {
                    return Err(RenderError::UnsupportedConstruct {
                        what: "Quantifier: Forall/Exists over Range/Collection (upstream emits Unbounded only)",
                    });
                }
                // e.g. `Any`/`All`/`Find` over an index-only `Range` --
                // no such upstream macro (those always carry a vec).
                _ => {
                    return Err(RenderError::UnsupportedConstruct {
                        what: "Quantifier: unsupported (kind, domain) combination",
                    });
                }
            };

            // Emit: `(helper [start end | collection] (fun binder => body))`.
            //
            // `Find`/`FindIndex` model Move's `find!`/`find_index!`, which
            // return `Option<_>`. The `spec_find*` helpers return only the
            // inner `vec` list (`[x]` / `[]`); wrap it in the generated
            // `MoveOption.MoveOption.mk` so the result types as the Option
            // its callers expect. `FindIndices` returns a genuine
            // `vector<u64>` (every match), so it is left unwrapped.
            let wrap_move_option = matches!(*kind, Q::Find | Q::FindIndex);
            if wrap_move_option {
                w.write("(MoveOption.MoveOption.mk ");
            }
            w.write("(");
            w.write(helper_name);
            match domain {
                QuantDomain::Unbounded => {}
                QuantDomain::Range { start, end } => {
                    w.write(" ");
                    render_with_parens_if_needed(start, ctx, w)?;
                    w.write(" ");
                    render_with_parens_if_needed(end, ctx, w)?;
                }
                QuantDomain::Collection(coll) => {
                    w.write(" ");
                    render_with_parens_if_needed(coll, ctx, w)?;
                }
                // Prelude helper signature is `(start stop) (vec) (pred)`.
                QuantDomain::VecRange { vec, start, end } => {
                    w.write(" ");
                    render_with_parens_if_needed(start, ctx, w)?;
                    w.write(" ");
                    render_with_parens_if_needed(end, ctx, w)?;
                    w.write(" ");
                    render_with_parens_if_needed(vec, ctx, w)?;
                }
            }
            // Lambda: register the binder's type so the body's name
            // resolution (in `render_expr` -> `render_call` ->
            // `rendered_type_of`) sees the correct type. The binder
            // name is freshly generated per quantifier in stage 2
            // (`__qi_<pc>_<dest>`), so it cannot collide with any
            // other name in the surrounding scope -- we don't bother
            // restoring the previous binding after the body.
            ctx.var_types
                .borrow_mut()
                .insert(binder.clone(), binder_type.clone());
            w.write(" (fun ");
            w.write(&escape::escape_identifier(binder));
            w.write(" => ");
            render_inner_block(body, ctx, w)?;
            w.write("))");
            if wrap_move_option {
                w.write(")");
            }
            Ok(())
        }
        Expr::LabeledBlock { .. } => {
            unreachable!("Expr::LabeledBlock should be eliminated by stage 7 helper extraction")
        }
    }
}

/// Render a theorem statement -- a Bool `Expr` whose top structure is
/// the logical-connective natives (`$prover_imp/iff/neg`, see
/// `ir::connectives`) -- as a Lean `Prop`. The connectives become real
/// `→` / `↔` / `¬`; every other (Bool) leaf is coerced to `Prop` with
/// `= true`. Used by the `FunctionKind::Theorem` renderer in
/// `render/function.rs` (see `plans/lean-pipeline/theorem-emission.md`).
pub(in crate::render) fn render_theorem_statement(
    e: &Expr,
    ctx: &ExprCtx<'_>,
) -> RenderResult<String> {
    use crate::ir::connectives::Connective;
    if let Expr::Call { fun, args, .. } = e {
        if let Some(c) = ctx
            .program
            .natives
            .decls
            .get(fun)
            .and_then(Connective::from_native_decl)
        {
            return Ok(match c {
                Connective::Imp => format!(
                    "({}) → ({})",
                    render_theorem_statement(&args[0], ctx)?,
                    render_theorem_statement(&args[1], ctx)?
                ),
                Connective::Iff => format!(
                    "({}) ↔ ({})",
                    render_theorem_statement(&args[0], ctx)?,
                    render_theorem_statement(&args[1], ctx)?
                ),
                Connective::Neg => {
                    format!("¬ ({})", render_theorem_statement(&args[0], ctx)?)
                }
            });
        }
        // `world_wf` (auto-injected by stage 12 on bag-touching
        // obligations) is a `Prop`-valued framework predicate. It is
        // ALREADY a `Prop`, so render it bare -- the `= true` Bool
        // coercion below would be ill-typed on a Prop.
        if crate::stage_12_obligations::is_world_wf_native(ctx.program, *fun) {
            return writeback::render_expr_to_string(e, ctx);
        }
    }
    Ok(format!(
        "({}) = true",
        writeback::render_expr_to_string(e, ctx)?
    ))
}

pub(super) fn render_const<W: Write>(c: &Const, w: &mut LeanWriter<W>) -> RenderResult<()> {
    match c {
        Const::Bool(b) => {
            w.write(if *b { "true" } else { "false" });
            Ok(())
        }
        Const::UInt { bits, value } => {
            if let Some(alias) = opaque_uint_const_alias(*bits, value) {
                w.write(&alias);
                return Ok(());
            }
            // Emit literal as a BoundedNat. Lean's BoundedNat has a
            // numeric literal coercion from Nat, but we want the type
            // explicit so type inference doesn't drift.
            let n = u256_to_decimal(value);
            w.write(&format!("({} : BoundedNat (2^{}))", n, bits));
            Ok(())
        }
        Const::Address(addr) => {
            w.write(&format!("(Address.ofNat {})", addr));
            Ok(())
        }
        Const::Unit => {
            w.write("()");
            Ok(())
        }
        Const::Vector {
            elem_type: _,
            elems,
        } => {
            if let Some(first) = elems.first().filter(|first| {
                elems.len() >= VECTOR_REPLICATE_THRESHOLD && elems.iter().all(|elem| elem == *first)
            }) {
                w.write(&format!("(List.replicate {} ", elems.len()));
                render_const(first, w)?;
                w.write(")");
                return Ok(());
            }

            w.write("[");
            for (i, e) in elems.iter().enumerate() {
                if i > 0 {
                    w.write(", ");
                }
                render_const(e, w)?;
            }
            w.write("]");
            Ok(())
        }
        // Stage 5 SSA's `Inhabited.default` placeholder for a typed
        // loop-carried value unavailable at loop entry. Emitted as bare
        // `default`; the call-argument's expected type drives `Inhabited`
        // resolution (generated structs derive `Inhabited`). Same mechanism
        // as the BorrowMapKey writeback fallback lambda.
        Const::Default(_) => {
            w.write("default");
            Ok(())
        }
    }
}

fn u256_to_decimal(v: &U256) -> String {
    // ethnum::U256 implements Display.
    format!("{}", v)
}

fn render_binop<W: Write>(
    op: BinOp,
    lhs: &Expr,
    rhs: &Expr,
    ctx: &ExprCtx<'_>,
    w: &mut LeanWriter<W>,
) -> RenderResult<()> {
    if let Some(head) = named_bounded_binop(op) {
        w.write("(");
        w.write(head);
        w.write(" ");
        render_operand_wrapping_control_flow(lhs, ctx, w)?;
        w.write(" ");
        render_operand_wrapping_control_flow(rhs, ctx, w)?;
        w.write(")");
        return Ok(());
    }
    let sym = binop_symbol(op);
    let is_cmp = matches!(op, BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge);
    if is_cmp {
        // Move comparisons return Bool; Lean's <, <=, > etc. on Nat
        // return Prop. Wrap in `decide` for the Bool result.
        w.write("(decide ");
    }
    w.write("(");
    render_operand_wrapping_control_flow(lhs, ctx, w)?;
    w.write(sym);
    render_operand_wrapping_control_flow(rhs, ctx, w)?;
    w.write(")");
    if is_cmp {
        w.write(")");
    }
    Ok(())
}

/// Operations whose fixed-width semantics cannot be expressed by Lean's
/// ordinary surface operators on `BoundedNat`. Stage 10 normally rewrites
/// these to synthetic calls before render; keeping this direct spelling makes
/// diagnostic/pre-stage rendering semantic rather than misleading.
fn named_bounded_binop(op: BinOp) -> Option<&'static str> {
    Some(match op {
        BinOp::WrappingAdd => "BoundedNat.wrapping_add",
        BinOp::WrappingSub => "BoundedNat.wrapping_sub",
        BinOp::WrappingMul => "BoundedNat.wrapping_mul",
        BinOp::SAdd => "BoundedNat.sadd",
        BinOp::SSub => "BoundedNat.ssub",
        BinOp::SMul => "BoundedNat.smul",
        BinOp::SDiv => "BoundedNat.sdiv",
        BinOp::SMod => "BoundedNat.smod",
        BinOp::AShr => "BoundedNat.ashr",
        BinOp::SLt => "BoundedNat.slt",
        BinOp::SLe => "BoundedNat.sle",
        BinOp::SGt => "BoundedNat.sgt",
        BinOp::SGe => "BoundedNat.sge",
        _ => return None,
    })
}

/// Render `e` as an operand of a binary operator. Wraps `Expr::If`
/// and `Expr::Match` in an extra pair of parentheses so the `else`
/// / final arm doesn't greedily consume the trailing operator.
///
/// Lean's `if c then a else b` is right-associative on the `else`
/// branch -- a downstream parser sees `if c then a else b OP rhs`
/// as `if c then a else (b OP rhs)`. The enclosing `(LHS OP RHS)`
/// parens from `render_binop` don't help: the greedy-else binds
/// inside them. Adding `((if c then a else b) OP rhs)` is the fix.
/// Same trick for `match` (its final arm body extends similarly).
fn render_operand_wrapping_control_flow<W: Write>(
    e: &Expr,
    ctx: &ExprCtx<'_>,
    w: &mut LeanWriter<W>,
) -> RenderResult<()> {
    if matches!(e, Expr::If { .. } | Expr::Match { .. }) {
        w.write("(");
        render_expr(e, ctx, w)?;
        w.write(")");
    } else {
        render_expr(e, ctx, w)?;
    }
    Ok(())
}

fn binop_symbol(op: BinOp) -> &'static str {
    match op {
        BinOp::Add => " + ",
        BinOp::Sub => " - ",
        BinOp::Mul => " * ",
        BinOp::WrappingAdd
        | BinOp::WrappingSub
        | BinOp::WrappingMul
        | BinOp::SAdd
        | BinOp::SSub
        | BinOp::SMul => unreachable!("named bounded arithmetic handled before symbol lookup"),
        BinOp::Div => " / ",
        BinOp::Mod => " % ",
        BinOp::SDiv | BinOp::SMod => {
            unreachable!("named signed arithmetic handled before symbol lookup")
        }
        BinOp::BitAnd => " &&& ",
        BinOp::BitOr => " ||| ",
        BinOp::BitXor => " ^^^ ",
        BinOp::Shl => " <<< ",
        BinOp::Shr => " >>> ",
        BinOp::LShr => " >>> ",
        BinOp::AShr => unreachable!("named arithmetic shift handled before symbol lookup"),
        BinOp::And => " && ",
        BinOp::Or => " || ",
        BinOp::Eq => " == ",
        BinOp::Neq => " != ",
        BinOp::Lt => " < ",
        BinOp::Le => " <= ",
        BinOp::Gt => " > ",
        BinOp::Ge => " >= ",
        BinOp::SLt | BinOp::SLe | BinOp::SGt | BinOp::SGe => {
            unreachable!("named signed comparison handled before symbol lookup")
        }
    }
}

fn render_unop<W: Write>(
    op: UnOp,
    operand: &Expr,
    ctx: &ExprCtx<'_>,
    w: &mut LeanWriter<W>,
) -> RenderResult<()> {
    match op {
        UnOp::Not => {
            w.write("(!");
            render_with_parens_if_needed(operand, ctx, w)?;
            w.write(")");
        }
        UnOp::BitNot => {
            w.write("(~~~");
            render_with_parens_if_needed(operand, ctx, w)?;
            w.write(")");
        }
        UnOp::Cast(bits) => {
            // `BoundedNat.convert` is the prelude helper for retyping
            // between widths (matches the legacy renderer).
            w.write("(BoundedNat.convert ");
            render_with_parens_if_needed(operand, ctx, w)?;
            w.write(&format!(" : BoundedNat (2^{}))", bits));
        }
    }
    Ok(())
}

fn render_bitop<W: Write>(
    op: &BitOp,
    ctx: &ExprCtx<'_>,
    w: &mut LeanWriter<W>,
) -> RenderResult<()> {
    match op {
        BitOp::Extract { high, low, operand } => {
            w.write(&format!("(BoundedNat.extract {} {} ", high, low));
            render_with_parens_if_needed(operand, ctx, w)?;
            w.write(")");
        }
        BitOp::Concat { high, low } => {
            w.write("(BoundedNat.concat ");
            render_with_parens_if_needed(high, ctx, w)?;
            w.write(" ");
            render_with_parens_if_needed(low, ctx, w)?;
            w.write(")");
        }
        BitOp::ZeroExtend { bits, operand } => {
            w.write(&format!("(BoundedNat.zeroExtend {} ", bits));
            render_with_parens_if_needed(operand, ctx, w)?;
            w.write(")");
        }
        BitOp::SignExtend { bits, operand } => {
            w.write(&format!("(BoundedNat.signExtend {} ", bits));
            render_with_parens_if_needed(operand, ctx, w)?;
            w.write(")");
        }
    }
    Ok(())
}
