//! `Function` -> Lean `def name (params) : T := body`.

use std::collections::BTreeMap;
use std::fmt::Write;

use crate::ir::{FunId, Function, NativeDecl, Program, Type};

use super::escape;
use super::expr::{render_function_body, rendered_type_of, ExprCtx};
use super::ty;
use super::writer::LeanWriter;
use super::{context::RenderContext, RenderError, RenderResult};

/// Render a single function definition.
///
/// `force_partial` is set by `emit_function_sccs` when emitting a
/// mutual block whose membership includes a function that would
/// already render as `partial def` (loop helpers, self-recursive
/// sources). Lean rejects mixing `partial def` and `def` inside one
/// mutual block, so we propagate partial-ness across the SCC.
/// Collect the CONCRETE (non-type-param) object types transferred /
/// shared / frozen in `func`'s body, as rendered Lean type strings.
/// A universe-polymorphic lemma function (`{__TyU}`) that packs a
/// concrete object into the world (e.g. `package::claim_and_keep` ->
/// `Publisher`) needs `[HasCode __TyU T] [Object.HasObjectId T]` as
/// hypotheses + a `Bag.Entry __TyU` world; see `render_function`.
fn transferred_concrete_object_types(
    func: &Function,
    program: &Program,
    current_module: Option<&str>,
    tp_names: &[String],
) -> Vec<String> {
    use crate::ir::{Expr, Type};

    fn is_transfer_native(program: &Program, fid: FunId) -> bool {
        let Some(callee) = program.lookup_callee(fid) else {
            return false;
        };
        let name = callee.name();
        let Some(m) = program.modules.get(&callee.module()) else {
            return false;
        };
        if m.package_name != "Sui" || m.name != "transfer" {
            return false;
        }
        matches!(
            name,
            "transfer"
                | "public_transfer"
                | "share_object"
                | "public_share_object"
                | "freeze_object"
                | "public_freeze_object"
                | "transfer_impl"
                | "share_object_impl"
                | "freeze_object_impl"
        )
    }

    struct Collector<'a> {
        program: &'a Program,
        current_module: Option<&'a str>,
        tp_names: &'a [String],
        out: Vec<String>,
    }
    impl crate::ir::visit::Visitor for Collector<'_> {
        fn visit_expr(&mut self, e: &Expr) {
            if let Expr::Call { fun, type_args, .. } = e {
                if is_transfer_native(self.program, *fun) {
                    // The transferred object's type is the first type
                    // arg. Only CONCRETE structs need explicit
                    // hypotheses -- bare type params are handled by the
                    // per-param ObjType taint (`needs_obj`).
                    if let Some(t @ Type::Struct { .. }) = type_args.first() {
                        let s = super::ty::type_to_string(
                            t,
                            self.program,
                            self.current_module,
                            Some(self.tp_names),
                        );
                        if !self.out.contains(&s) {
                            self.out.push(s);
                        }
                    }
                }
            }
            crate::ir::visit::walk_expr_default(self, e);
        }
    }

    let mut c = Collector {
        program,
        current_module,
        tp_names,
        out: Vec::new(),
    };
    crate::ir::visit::Visitor::visit_block(&mut c, &func.body);
    c.out
}

/// Collect the distinct CONCRETE map-key payload Lean types borrowed in
/// `func`'s body (`Expr::Borrow { step: MapKey { key_type, .. } }` with a
/// concrete `key_type`). A LEMMA-package function wraps such a key via
/// `IntoKey.intoKey` (see `render::expr::util::render_anykey_wrap`)
/// rather than the in-scope-only `AnyKey.k_<ctor>` constructor, so it
/// needs an explicit `[IntoKey __MutKey <payload>]` hypothesis -- the
/// user-package call site (which imports `Generated.AnyKey`) resolves it
/// via `__MutKey := AnyKey`. The payload string is produced by the SAME
/// `mutation::payload_lean_ty` that renders the `Generated.AnyKey`
/// instance, so the constraint and the instance unify. Map-key analogue
/// of `transferred_concrete_object_types`.
fn lemma_concrete_map_key_payloads(func: &Function, program: &Program) -> Vec<String> {
    use crate::ir::{path::PathStep, Expr};
    struct Collector<'a> {
        program: &'a Program,
        out: Vec<String>,
    }
    impl crate::ir::visit::Visitor for Collector<'_> {
        fn visit_expr(&mut self, e: &Expr) {
            if let Expr::Borrow {
                step: PathStep::MapKey { key_type, .. },
                ..
            } = e
            {
                if crate::render::mutation::is_concrete_key_payload(key_type) {
                    let s = crate::render::mutation::payload_lean_ty(key_type, self.program);
                    if !self.out.contains(&s) {
                        self.out.push(s);
                    }
                }
            }
            crate::ir::visit::walk_expr_default(self, e);
        }
    }
    let mut c = Collector {
        program,
        out: Vec::new(),
    };
    crate::ir::visit::Visitor::visit_block(&mut c, &func.body);
    c.out
}

/// Collect the CONCRETE object struct types that `func` passes to an
/// `object::id` / `object::id_address` ID accessor. Unlike a transfer
/// (`transferred_concrete_object_types`), an id accessor never touches
/// the world's Object slot -- `object::id` has signature
/// `(tv0) [DecidableEq] [Inhabited] [HasObjectId tv0] (obj) : ID`. So such a
/// concrete object needs ONLY a `[Object.HasObjectId T]` hypothesis, NOT
/// `[HasCode __ObjU T]`, no `{__ObjU}` binder, and no world-Object pin.
/// A lemma-package function that reads the id of a `Struct<T>` it builds
/// from its own type param (e.g. Sui `coin_registry::new_currency`
/// calling `object::id(TreasuryCap<T>)`) needs this so the hypothesis is
/// resolved at the user call site (which imports `ObjTypeInterp`). Bare
/// type-param objects are handled by the per-param `needs_obj` taint.
fn id_accessed_concrete_object_types(
    func: &Function,
    program: &Program,
    current_module: Option<&str>,
    tp_names: &[String],
) -> Vec<String> {
    use crate::ir::{Expr, Type};

    fn is_id_accessor_native(program: &Program, fid: FunId) -> bool {
        let Some(callee) = program.lookup_callee(fid) else {
            return false;
        };
        let name = callee.name();
        let Some(m) = program.modules.get(&callee.module()) else {
            return false;
        };
        if m.package_name != "Sui" || m.name != "object" {
            return false;
        }
        matches!(name, "id" | "id_address")
    }

    struct Collector<'a> {
        program: &'a Program,
        current_module: Option<&'a str>,
        tp_names: &'a [String],
        out: Vec<String>,
    }
    impl crate::ir::visit::Visitor for Collector<'_> {
        fn visit_expr(&mut self, e: &Expr) {
            if let Expr::Call { fun, type_args, .. } = e {
                if is_id_accessor_native(self.program, *fun) {
                    if let Some(t @ Type::Struct { .. }) = type_args.first() {
                        let s = super::ty::type_to_string(
                            t,
                            self.program,
                            self.current_module,
                            Some(self.tp_names),
                        );
                        if !self.out.contains(&s) {
                            self.out.push(s);
                        }
                    }
                }
            }
            crate::ir::visit::walk_expr_default(self, e);
        }
    }

    let mut c = Collector {
        program,
        current_module,
        tp_names,
        out: Vec::new(),
    };
    crate::ir::visit::Visitor::visit_block(&mut c, &func.body);
    c.out
}

/// Whether `fid` is a `derived_object` call whose `type_args[0]` is the
/// KEY type threaded into `derive_address`. Since #23, `derive_address`
/// folds `Universe.typeName` of the key's tycode into the derived
/// address (and since #6, the key VALUE via `Repr`), so a caller passing
/// its own key type into any of these must supply `[HasCode __TyU
/// <keytype>]` -- exactly like a `dynamic_field::store_*` K type.
/// `claim`/`exists_` are matched for EXTERNAL callers (e.g. `coin_registry`
/// threading `CurrencyKey<T>`); `derive_address` for the in-module
/// `claim`/`exists_` bodies that call it directly.
pub(crate) fn derived_object_key_call(program: &Program, fid: FunId) -> bool {
    let Some(callee) = program.lookup_callee(fid) else {
        return false;
    };
    let name = callee.name();
    let Some(m) = program.modules.get(&callee.module()) else {
        return false;
    };
    if m.package_name != "Sui" || m.name != "derived_object" {
        return false;
    }
    matches!(
        name,
        "claim"
            | "claim.aborts"
            | "exists"
            | "exists.aborts"
            | "exists_"
            | "exists_.aborts"
            | "derive_address"
            | "derive_address.aborts"
    )
}

/// #6: the type-param indices of `func` that appear as a BARE key type
/// (`type_args[0]`) of a `derived_object::{claim,exists_,derive_address}`
/// call. Since #6, `derive_address` folds `(repr key).pretty` into the
/// address, so any function threading its own type param `T` as the key
/// must carry `[Repr T]` (mirrors the `[HasCode __TyU T]` taint, but only
/// for the derived-object KEY param -- NOT df_store K/V params, which must
/// stay Repr-free). Concrete key types are covered by the `Repr` instance
/// emitted on the key struct (see `derived_object_key_struct_names`).
fn derived_object_key_repr_param_idxs(
    program: &Program,
    func: &Function,
) -> std::collections::BTreeSet<usize> {
    use crate::ir::{Expr, Type};
    struct C<'a> {
        program: &'a Program,
        params: std::collections::BTreeSet<usize>,
    }
    impl crate::ir::visit::Visitor for C<'_> {
        fn visit_expr(&mut self, e: &Expr) {
            if let Expr::Call { fun, type_args, .. } = e {
                if derived_object_key_call(self.program, *fun) {
                    if let Some(Type::TypeParam(n)) = type_args.first() {
                        self.params.insert(usize::from(*n));
                    }
                }
            }
            crate::ir::visit::walk_expr_default(self, e);
        }
    }
    let mut c = C {
        program,
        params: std::collections::BTreeSet::new(),
    };
    crate::ir::visit::Visitor::visit_block(&mut c, &func.body);
    c.params
}

/// #6: program-wide set of struct NAMES used as a CONCRETE derived-object
/// key (`type_args[0]` of a `derived_object::{claim,exists_,derive_address}`
/// call resolving to a `Struct`). Each such struct needs a `Repr` instance
/// so the `[Repr key]` hypothesis on `derive_address` resolves at the
/// concrete call site. Value keys (non-generic, real fields -- e.g.
/// `AccountKey`) get `deriving Repr` (value-dependent); phantom/generic
/// keys get a constant instance (see `struct_def`).
pub(crate) fn derived_object_key_struct_names(
    program: &Program,
) -> std::collections::BTreeSet<String> {
    use crate::ir::{Expr, Type};
    struct C<'a> {
        program: &'a Program,
        names: std::collections::BTreeSet<String>,
    }
    impl crate::ir::visit::Visitor for C<'_> {
        fn visit_expr(&mut self, e: &Expr) {
            if let Expr::Call { fun, type_args, .. } = e {
                if derived_object_key_call(self.program, *fun) {
                    if let Some(Type::Struct { struct_id, .. }) = type_args.first() {
                        if let Some(s) = self.program.structs.get(struct_id) {
                            self.names.insert(s.qualified_name.clone());
                        }
                    }
                }
            }
            crate::ir::visit::walk_expr_default(self, e);
        }
    }
    let mut c = C {
        program,
        names: std::collections::BTreeSet::new(),
    };
    for f in program.functions.values() {
        crate::ir::visit::Visitor::visit_block(&mut c, &f.body);
    }
    c.names
}

/// Collect the dynamic-field store K/V universe types used in `func`'s
/// body. Returns `(concrete_types, param_indices)`:
///   - `concrete_types`: rendered Lean type strings for every store
///     K/V type that is NOT a bare type param -- each needs an explicit
///     `[HasCode __TyU <ty>]` hypothesis on a universe-polymorphic
///     lemma function (the user-package call site, which imports
///     `Generated.TyCodeInterp`, resolves `__TyU := TyCode`).
///   - `param_indices`: indices of this function's type params appearing
///     (bare or nested) in a store K/V type -- those get the per-param
///     `[HasCode __TyU T]` constraint via `needs_tycode`.
/// `dynamic_field::store_*` natives are the routed form of df
/// add/borrow/borrow_mut/exists (see stage_02 dynamic_field_rewrite).
fn df_store_universe_types(
    func: &Function,
    program: &Program,
    current_module: Option<&str>,
    tp_names: &[String],
) -> (Vec<String>, std::collections::BTreeSet<usize>) {
    use crate::ir::{Expr, Type};

    // Returns Some(n) = number of leading type_args ([K] or [K,V]) that
    // need a `[HasCode __TyU ..]` hypothesis, or None if not a df store
    // native. The `store_bag_*` natives store a whole Bag value (which
    // needs no HasCode -- its entries ride as `BagEntry`), so only their
    // KEY type is collected.
    fn df_store_collect_arity(program: &Program, fid: FunId) -> Option<usize> {
        let callee = program.lookup_callee(fid)?;
        let name = callee.name();
        let m = program.modules.get(&callee.module())?;
        if m.package_name != "Sui" || m.name != "dynamic_field" {
            return None;
        }
        match name {
            "borrow" | "set" | "add" | "remove" | "store_remove_if_exists" => Some(2),
            "has" => Some(1),
            "store_bag_borrow" | "store_bag_set" | "store_bag_add" | "store_bag_remove"
            | "store_bag_has" => Some(1),
            _ => None,
        }
    }

    // `derived_object::{claim, exists_}` (+ their `.aborts` split
    // variants) are TRANSLATED lemma functions that drive a dynamic
    // field under the hood: each is universe-polymorphic over `__TyU`,
    // pins its world DfEntry slot to `Bag.Entry __TyU`, and takes
    // `[HasCode __TyU Claimed]` (+ `[HasCode __TyU ClaimedStatus]` for
    // `claim`) as hypotheses. A caller threading its own world into one
    // of these must therefore join the df universe exactly like a direct
    // `dynamic_field::store_*` caller: bind `{__TyU}`, pin the world
    // DfEntry override, and supply the SAME concrete `[HasCode __TyU ..]`
    // hypotheses so the native's requirements discharge. The stored
    // value types are fixed (`Claimed` marker + its `ClaimedStatus`
    // payload), so they are hardcoded rather than read off `type_args`
    // (the call's only type arg is the derived KEY, which rides as the
    // df address and needs no code). Concrete `__TyU := TyCode`
    // resolution happens at the user call site.
    fn derived_object_df_types(program: &Program, fid: FunId) -> Option<&'static [&'static str]> {
        let callee = program.lookup_callee(fid)?;
        let name = callee.name();
        let m = program.modules.get(&callee.module())?;
        if m.package_name != "Sui" || m.name != "derived_object" {
            return None;
        }
        // `name` is the RAW IR name. `exists` is a Lean reserved word
        // that the renderer escapes to `exists_` (see escape.rs), so the
        // raw form here is `exists` / `exists.aborts` -- match those (the
        // escaped variants are kept too, defensively). `claim` is not
        // reserved, so its raw and rendered names coincide.
        match name {
            "claim" | "claim.aborts" => Some(&[
                "_root_.Derived_object.Claimed",
                "_root_.Derived_object.ClaimedStatus",
            ]),
            "exists" | "exists.aborts" | "exists_" | "exists_.aborts" => {
                Some(&["_root_.Derived_object.Claimed"])
            }
            _ => None,
        }
    }

    fn collect_params(ty: &Type, into: &mut std::collections::BTreeSet<usize>) {
        match ty {
            Type::TypeParam(n) => {
                into.insert(usize::from(*n));
            }
            Type::Vector(inner) | Type::Reference(inner) => collect_params(inner, into),
            Type::MutableRef { inner, root } => {
                collect_params(inner, into);
                collect_params(root, into);
            }
            Type::Tuple(ts) => ts.iter().for_each(|t| collect_params(t, into)),
            Type::Struct { type_args, .. } => {
                type_args.iter().for_each(|t| collect_params(t, into))
            }
            _ => {}
        }
    }

    struct Collector<'a> {
        program: &'a Program,
        current_module: Option<&'a str>,
        tp_names: &'a [String],
        concrete: Vec<String>,
        params: std::collections::BTreeSet<usize>,
    }
    impl crate::ir::visit::Visitor for Collector<'_> {
        fn visit_expr(&mut self, e: &Expr) {
            if let Expr::Call { fun, type_args, .. } = e {
                if let Some(arity) = df_store_collect_arity(self.program, *fun) {
                    // Routed store_* calls carry `type_args = [K, V]`;
                    // store_bag_* collect only [K] (arity 1).
                    for t in type_args.iter().take(arity) {
                        match t {
                            Type::TypeParam(n) => {
                                self.params.insert(usize::from(*n));
                            }
                            _ => {
                                collect_params(t, &mut self.params);
                                let s = super::ty::type_to_string(
                                    t,
                                    self.program,
                                    self.current_module,
                                    Some(self.tp_names),
                                );
                                if !self.concrete.contains(&s) {
                                    self.concrete.push(s);
                                }
                            }
                        }
                    }
                }
                // A `derived_object::{claim, exists_}` callee (or its
                // `.aborts` split) drives a df internally; the caller
                // joins the same `__TyU` universe and must supply the
                // native's fixed `[HasCode __TyU ..]` value-type
                // hypotheses.
                if let Some(tys) = derived_object_df_types(self.program, *fun) {
                    for s in tys {
                        let s = (*s).to_string();
                        if !self.concrete.contains(&s) {
                            self.concrete.push(s);
                        }
                    }
                }
                // #23: a `derived_object::{claim, exists_, derive_address}`
                // callee folds `type_args[0]` (the KEY type) into the
                // derived address via `Universe.typeName`, so the caller
                // must carry `[HasCode __TyU <keytype>]`. A bare type
                // param taints that param (`[HasCode __TyU t_tvN]`); a
                // concrete key type contributes its string
                // (`[HasCode __TyU (CurrencyKey t_tv0)]`).
                if derived_object_key_call(self.program, *fun) {
                    if let Some(kt) = type_args.first() {
                        match kt {
                            // A bare key type param taints THAT param
                            // (the in-module `claim`/`exists_` bodies
                            // call `derive_address<t_tv0>`): emit
                            // `[HasCode __TyU t_tv0]` on the param.
                            Type::TypeParam(n) => {
                                self.params.insert(usize::from(*n));
                            }
                            // A wrapped / concrete key type contributes
                            // the WHOLE type as one `[HasCode __TyU
                            // (CurrencyKey t_tv0)]` hypothesis -- the
                            // exact thing `derive_address` projects
                            // `Universe.typeName` from. We do NOT recurse
                            // into the inner param: `HasCode (CurrencyKey
                            // T)` is an independent closed-universe entry,
                            // never derived from `HasCode T`, so tainting
                            // the inner param would emit a superfluous
                            // (and possibly unresolvable) `[HasCode __TyU
                            // t_tv0]`. The concrete set ALSO propagates
                            // across `.aborts`/`.cont` edges via
                            // `df_concrete_types_for`, which the param
                            // taint would not.
                            _ => {
                                let s = super::ty::type_to_string(
                                    kt,
                                    self.program,
                                    self.current_module,
                                    Some(self.tp_names),
                                );
                                if !self.concrete.contains(&s) {
                                    self.concrete.push(s);
                                }
                            }
                        }
                    }
                }
            }
            crate::ir::visit::walk_expr_default(self, e);
        }
    }

    let mut c = Collector {
        program,
        current_module,
        tp_names,
        concrete: Vec::new(),
        params: std::collections::BTreeSet::new(),
    };
    crate::ir::visit::Visitor::visit_block(&mut c, &func.body);
    (c.concrete, c.params)
}

/// The broad lemma-package predicate used by `render_function`'s
/// universe gating (NOT `escape::is_lemma_package`, which is the
/// narrower namespace-rendering helper). Functions in these packages
/// stay universe-POLYMORPHIC (abstract `__TyU`/`__BagU`/`__ObjU` +
/// HasCode hypotheses) instead of pinning the per-project concrete
/// `_root_.TyCode`/`_root_.BagU`/`_root_.ObjType`, to avoid a render
/// cycle through `Generated.*Interp`.
pub(crate) fn name_is_lemma_package(pkg: &str) -> bool {
    const LEMMA_PACKAGES: &[&str] = &[
        "Prelude",
        "Prover",
        "Sui",
        "MoveStdlib",
        "Pyth",
        "Wormhole",
        "DeepBook",
        "Generated",
        "NewPipeline",
    ];
    LEMMA_PACKAGES.contains(&pkg)
}

/// Program-wide map: lemma `FunId` -> the concrete df value-type strings
/// it must carry as `[HasCode __TyU ..]` hypotheses. Built in two phases:
///
///   1. DIRECT: every lemma function's own `df_store_universe_types`
///      concrete set (direct `dynamic_field::store_*` /
///      `derived_object::{claim, exists_}` callees).
///   2. INHERITANCE: a `.aborts` / `.requires` / `.ensures` Spec
///      companion and a `.cont_N` continuation fragment share their
///      source / parent's type-param list and call one another, yet
///      their own bodies may not directly hit a df native -- so a
///      companion that THREADS its world into a universe-polymorphic
///      sibling under-reports. Mirror `dyn_type_universe::
///      inherit_spec_companion_typeparam_deps`: union the source /
///      parent's concrete set DOWN into the companion, and a cont
///      fragment's set UP into its parent. The concrete strings are
///      universe-independent (`_root_.` paths, or types over the SHARED
///      type-param list), so they transfer verbatim -- no positional
///      remapping needed.
///
/// Inheritance edges never cross modules (Spec `target` and `.cont_N`
/// parent both resolve within the function's own module), so a lemma
/// function only ever inherits from lemma functions.
/// Program-wide dynamic-field universe of every lemma function.
pub(super) struct DfUniverse {
    /// Type params that need `[HasCode __TyU T]`.
    pub(super) params: std::collections::HashMap<FunId, std::collections::BTreeSet<usize>>,
    /// Concrete df value types that need `[HasCode __TyU <ty>]`.
    pub(super) concrete: std::collections::HashMap<FunId, Vec<String>>,
    /// Functions that must bind `{__TyU}` only because they call into a
    /// df-universe function (no param or concrete type of their own to
    /// supply).
    pub(super) bound: std::collections::HashSet<FunId>,
}

impl DfUniverse {
    pub(super) fn binds(&self, fid: FunId) -> bool {
        self.params.get(&fid).is_some_and(|p| !p.is_empty())
            || self.concrete.get(&fid).is_some_and(|c| !c.is_empty())
            || self.bound.contains(&fid)
    }
}

/// The direct df store taint of every lemma function, then a fixpoint that
/// follows CALL edges (and the Spec-companion / cont-fragment edges of
/// `propagate_concrete_across_edges`): a lemma function that calls a
/// df-universe lemma function joins the same universe. A callee's tainted
/// type param `k` maps through the call's `type_args[k]` -- a bare caller
/// param is tainted in turn, any other type is supplied as a concrete
/// `[HasCode __TyU ..]` -- and the callee's closed concrete types carry over
/// verbatim. Without the call edges, `linked_table::pop_front` calling
/// `remove` (which hits `dynamic_field` directly) rendered with a plain
/// `World` against `remove`'s `Bag.Entry __TyU` DfEntry slot:
/// `failed to synthesize Universe ?m`.
pub(super) fn compute_df_universe(program: &Program) -> DfUniverse {
    use crate::ir::{Expr, Type};

    fn collect_params(ty: &Type, into: &mut std::collections::BTreeSet<usize>) {
        match ty {
            Type::TypeParam(n) => {
                into.insert(usize::from(*n));
            }
            Type::Vector(inner) | Type::Reference(inner) => collect_params(inner, into),
            Type::MutableRef { inner, root } => {
                collect_params(inner, into);
                collect_params(root, into);
            }
            Type::Tuple(ts) => ts.iter().for_each(|t| collect_params(t, into)),
            Type::Struct { type_args, .. } => {
                type_args.iter().for_each(|t| collect_params(t, into))
            }
            _ => {}
        }
    }

    struct Calls(Vec<(FunId, Vec<Type>)>);
    impl crate::ir::visit::Visitor for Calls {
        fn visit_expr(&mut self, e: &Expr) {
            if let Expr::Call { fun, type_args, .. } = e {
                self.0.push((*fun, type_args.clone()));
            }
            crate::ir::visit::walk_expr_default(self, e);
        }
    }

    let mut universe = DfUniverse {
        params: std::collections::HashMap::new(),
        concrete: std::collections::HashMap::new(),
        bound: std::collections::HashSet::new(),
    };
    let mut calls: std::collections::HashMap<FunId, Vec<(FunId, Vec<Type>)>> =
        std::collections::HashMap::new();
    for (fid, f) in program.functions.iter() {
        let Some(m) = program.modules.get(&f.module) else {
            continue;
        };
        if !name_is_lemma_package(&m.package_name) {
            continue;
        }
        let (concrete, params) =
            df_store_universe_types(f, program, Some(m.name.as_str()), &f.signature.type_params);
        universe.concrete.insert(*fid, concrete);
        universe.params.insert(*fid, params);
        let mut c = Calls(Vec::new());
        crate::ir::visit::Visitor::visit_block(&mut c, &f.body);
        calls.insert(*fid, c.0);
    }

    loop {
        let mut changed = false;
        for (fid, sites) in calls.iter() {
            let f = &program.functions[fid];
            let module = program.modules.get(&f.module).map(|m| m.name.as_str());
            for (callee, type_args) in sites {
                if callee == fid || !universe.binds(*callee) {
                    continue;
                }
                let Some(callee_fn) = program.functions.get(callee) else {
                    continue;
                };
                let callee_params = universe.params.get(callee).cloned().unwrap_or_default();
                let callee_concrete = universe.concrete.get(callee).cloned().unwrap_or_default();
                let mut new_params = std::collections::BTreeSet::new();
                let mut new_concrete = Vec::new();
                for k in callee_params {
                    let Some(ta) = type_args.get(k) else {
                        continue;
                    };
                    if let Type::TypeParam(n) = ta {
                        new_params.insert(usize::from(*n));
                    } else {
                        collect_params(ta, &mut new_params);
                        new_concrete.push(super::ty::type_to_string(
                            ta,
                            program,
                            module,
                            Some(&f.signature.type_params),
                        ));
                    }
                }
                // A callee concrete type over the callee's own params
                // (`remove` storing `Node<K, V>`) is re-expressed in the
                // caller's terms by substituting each param with the
                // caller's rendered type argument.
                let callee_names: Vec<String> = callee_fn
                    .signature
                    .type_params
                    .iter()
                    .map(|tp| escape::escape_identifier(tp).to_string())
                    .collect();
                let replacements: std::collections::HashMap<&str, String> = callee_names
                    .iter()
                    .enumerate()
                    .filter_map(|(k, name)| {
                        type_args.get(k).map(|ta| {
                            (
                                name.as_str(),
                                super::ty::type_to_string(
                                    ta,
                                    program,
                                    module,
                                    Some(&f.signature.type_params),
                                ),
                            )
                        })
                    })
                    .collect();
                for s in callee_concrete {
                    if !type_string_mentions_type_param(&s, &callee_fn.signature.type_params) {
                        new_concrete.push(s);
                    } else if replacements.len() == callee_names.len() {
                        new_concrete.push(substitute_identifiers(&s, &replacements));
                    }
                }
                let params = universe.params.entry(*fid).or_default();
                for p in new_params {
                    changed |= params.insert(p);
                }
                let concrete = universe.concrete.entry(*fid).or_default();
                for s in new_concrete {
                    if !concrete.contains(&s) {
                        concrete.push(s);
                        changed = true;
                    }
                }
                changed |= universe.bound.insert(*fid);
            }
        }
        let before = universe.concrete.clone();
        universe.concrete = propagate_concrete_across_edges(program, universe.concrete);
        changed |= universe.concrete != before;
        if !changed {
            break;
        }
    }
    universe
}

/// Replace whole identifier tokens of `s` found in `replacements`. Token
/// characters are alphanumerics, `_`, `'` and `.`, so `t_tv0` never matches
/// inside `t_tv01`, and a qualified path (`_root_.Linked.K`) is one token that
/// never equals a bare type-param name.
fn substitute_identifiers(
    s: &str,
    replacements: &std::collections::HashMap<&str, String>,
) -> String {
    let mut out = String::with_capacity(s.len());
    let mut token = String::new();
    let flush = |token: &mut String, out: &mut String| {
        if !token.is_empty() {
            match replacements.get(token.as_str()) {
                Some(r) => out.push_str(r),
                None => out.push_str(token),
            }
            token.clear();
        }
    };
    for c in s.chars() {
        if c.is_alphanumeric() || c == '_' || c == '\'' || c == '.' {
            token.push(c);
        } else {
            flush(&mut token, &mut out);
            out.push(c);
        }
    }
    flush(&mut token, &mut out);
    out
}

/// Shared fixpoint that propagates a per-function concrete-type set
/// (`map`) across Spec-companion (`.aborts`/`.requires`/`.ensures`) and
/// `.cont_N` fragment edges, so a function that merely THREADS its world
/// into a universe-polymorphic sibling inherits the same hypotheses its
/// sibling requires. Used by both `compute_df_concrete_types` (the
/// `[HasCode __TyU ..]` df universe) and `compute_obj_id_concrete_types`
/// (the `[Object.HasObjectId ..]` object universe). Direction matches the
/// typeparam-dep pass: downward (companion / cont fragment inherits its
/// source / parent's set) plus upward for cont fragments only (a type
/// born in a deep fragment must also constrain its parent and siblings).
fn propagate_concrete_across_edges(
    program: &Program,
    mut map: std::collections::HashMap<FunId, Vec<String>>,
) -> std::collections::HashMap<FunId, Vec<String>> {
    use crate::ir::function::FunctionKind;
    // (module, name) -> fid, for resolving `.cont_N` parents by name
    // (Synthetic fragments carry no `target` field).
    let mut name_index: std::collections::HashMap<(crate::ir::ModId, &str), FunId> =
        std::collections::HashMap::new();
    for (fid, f) in program.functions.iter() {
        name_index.insert((f.module, f.name.as_str()), *fid);
    }
    // fid -> inheritance source (Spec `target` / nearest existing cont
    // parent, walking up dropped `.cont_N` levels like the typeparam pass).
    let mut targets: std::collections::HashMap<FunId, FunId> = std::collections::HashMap::new();
    for (fid, f) in program.functions.iter() {
        let target = match &f.kind {
            FunctionKind::Spec { target, .. } => Some(*target),
            FunctionKind::Synthetic => {
                let mut base = f.name.as_str();
                let mut found = None;
                while let Some(parent) = crate::ir::names::cont_parent(base) {
                    if let Some(&pfid) = name_index.get(&(f.module, parent)) {
                        found = Some(pfid);
                        break;
                    }
                    base = parent;
                }
                found
            }
            _ => None,
        };
        if let Some(t) = target {
            if t != *fid {
                targets.insert(*fid, t);
            }
        }
    }
    loop {
        let mut changed = false;
        for (fid, target) in targets.iter() {
            let Some(target_set) = map.get(target).cloned() else {
                continue;
            };
            // Downward: a Spec companion / cont fragment inherits its
            // source / parent's concrete set.
            if let Some(local) = map.get_mut(fid) {
                for s in &target_set {
                    if !local.contains(s) {
                        local.push(s.clone());
                        changed = true;
                    }
                }
            }
            // Upward (cont fragments only): a type born in a deep
            // fragment must also constrain its parent (and, transitively,
            // its sibling fragments). Spec -> source stays downward-only.
            let fid_is_cont = matches!(
                program.functions.get(fid).map(|f| &f.kind),
                Some(FunctionKind::Synthetic)
            );
            if fid_is_cont {
                if let Some(fid_set) = map.get(fid).cloned() {
                    if let Some(parent) = map.get_mut(target) {
                        for s in &fid_set {
                            if !parent.contains(s) {
                                parent.push(s.clone());
                                changed = true;
                            }
                        }
                    }
                }
            }
        }
        if !changed {
            break;
        }
    }
    map
}

/// Per-function CONCRETE object-id types (`[Object.HasObjectId T]`) a
/// lemma function must carry: the objects it reads via `object::id` /
/// `id_address`, UNIONED across Spec-companion / cont-fragment edges. A
/// Spec companion like `coin_registry::new_currency.aborts` that only
/// delegates the `object::id` call to its `.cont_0.cont_0` fragment
/// still binds `[Object.HasObjectId (Coin.TreasuryCap t_tv0)]` so it can
/// thread that instance down to the fragment it calls.
pub(super) fn compute_obj_id_concrete_types(
    program: &Program,
) -> std::collections::HashMap<FunId, Vec<String>> {
    let mut map: std::collections::HashMap<FunId, Vec<String>> = std::collections::HashMap::new();
    for (fid, f) in program.functions.iter() {
        let Some(m) = program.modules.get(&f.module) else {
            continue;
        };
        if !name_is_lemma_package(&m.package_name) {
            continue;
        }
        let ids = id_accessed_concrete_object_types(
            f,
            program,
            Some(m.name.as_str()),
            &f.signature.type_params,
        );
        map.insert(*fid, ids);
    }
    propagate_concrete_across_edges(program, map)
}

/// Collect the CONCRETE (non-type-param) type args passed to a
/// universe-generic `type_name::*` / `sui::types::is_one_time_witness`
/// / `bcs::to_bytes` native in `func`'s body, as rendered Lean type
/// strings. These natives are pinned `(U := __TyU)` at the call site for
/// a lemma-package caller (see `render::expr::call` `needs_tycode_pin`),
/// so the function must bind `{__TyU}` and carry `[HasCode __TyU <ty>]`
/// for each concrete `<ty>` -- even when NO type param is tycode-tainted
/// (e.g. `coin_registry::new_currency` calling
/// `type_name::with_original_ids<bool>` on the fixed `bool` OTW
/// sentinel). A bare type-param arg is excluded -- those are covered by
/// the per-param `tycode_typeparam_needs_constraint` taint. Concrete
/// resolution (`__TyU := TyCode`) happens at the user call site.
fn tycode_native_concrete_types(
    func: &Function,
    program: &Program,
    current_module: Option<&str>,
    tp_names: &[String],
) -> Vec<String> {
    use crate::ir::{Expr, Type};

    fn is_tycode_pin_native(program: &Program, fid: FunId) -> bool {
        let Some(callee) = program.lookup_callee(fid) else {
            return false;
        };
        let name = callee.name();
        let Some(m) = program.modules.get(&callee.module()) else {
            return false;
        };
        let is_type_name = m.package_name == "MoveStdlib"
            && m.name == "type_name"
            && matches!(
                name,
                "get" | "with_defining_ids" | "get_with_original_ids" | "with_original_ids"
            );
        let is_types_otw =
            m.package_name == "Sui" && m.name == "types" && name == "is_one_time_witness";
        let is_bcs_to_bytes = super::native_models::is_bcs_to_bytes_model(program, fid);
        is_type_name || is_types_otw || is_bcs_to_bytes
    }

    struct Collector<'a> {
        program: &'a Program,
        current_module: Option<&'a str>,
        tp_names: &'a [String],
        out: Vec<String>,
    }
    impl crate::ir::visit::Visitor for Collector<'_> {
        fn visit_expr(&mut self, e: &Expr) {
            if let Expr::Call { fun, type_args, .. } = e {
                if is_tycode_pin_native(self.program, *fun) {
                    // The universe-generic arg is the first type arg
                    // (`type_name::get<T>` / `is_one_time_witness<T>` /
                    // `bcs::to_bytes<X>`). Only CONCRETE args need an
                    // explicit `[HasCode __TyU ..]` hypothesis -- a bare
                    // type param is handled by the per-param tycode taint.
                    match type_args.first() {
                        Some(Type::TypeParam(_)) | None => {}
                        Some(t) => {
                            let s = super::ty::type_to_string(
                                t,
                                self.program,
                                self.current_module,
                                Some(self.tp_names),
                            );
                            if !self.out.contains(&s) {
                                self.out.push(s);
                            }
                        }
                    }
                }
            }
            crate::ir::visit::walk_expr_default(self, e);
        }
    }

    let mut c = Collector {
        program,
        current_module,
        tp_names,
        out: Vec::new(),
    };
    crate::ir::visit::Visitor::visit_block(&mut c, &func.body);
    c.out
}

/// True if `func`'s body calls the universe-generic `sui::bag::new` /
/// `bag::new.aborts` native. A freshly-created `Bag` is empty, so its
/// element universe is fixed by no argument and is pinned `(U := __BagU)`
/// at the call site for a lemma-package caller (see `render::expr::call`
/// `is_bag_new`). The function must therefore bind `{__BagU}` even when
/// no type param is bag-tainted (e.g. `coin_registry::new_currency`
/// building an empty `extra_fields` Bag). `[Universe __BagU]` alone
/// satisfies `bag::new` -- no `[HasCode __BagU ..]` is needed for the
/// empty bag.
fn body_calls_abstract_bag_new(func: &Function, program: &Program) -> bool {
    use crate::ir::Expr;

    fn is_bag_new(program: &Program, fid: FunId) -> bool {
        let Some(callee) = program.lookup_callee(fid) else {
            return false;
        };
        let name = callee.name();
        let Some(m) = program.modules.get(&callee.module()) else {
            return false;
        };
        m.package_name == "Sui" && m.name == "bag" && matches!(name, "new" | "new.aborts")
    }

    struct Collector<'a> {
        program: &'a Program,
        found: bool,
    }
    impl crate::ir::visit::Visitor for Collector<'_> {
        fn visit_expr(&mut self, e: &Expr) {
            if let Expr::Call { fun, .. } = e {
                if is_bag_new(self.program, *fun) {
                    self.found = true;
                }
            }
            crate::ir::visit::walk_expr_default(self, e);
        }
    }

    let mut c = Collector {
        program,
        found: false,
    };
    crate::ir::visit::Visitor::visit_block(&mut c, &func.body);
    c.found
}

/// Whether `fid` is the `Sui::derived_object::derive_address` lemma
/// (the NON-`.aborts` variant). Since #23 this function is rendered with
/// a hardcoded TYPE-AWARE body: it folds `Universe.typeName` of the key's
/// tycode into the derived address so distinct key TYPES under a shared
/// parent never collide (the opaque native `hash_type_and_key` carried no
/// type code, so all four securitize services aliased the same
/// `Claimed{ID 0}` slot). It therefore binds `{__TyU}` + a named
/// `[__hc : HasCode __TyU <key>]` and must be pinned at every call site
/// like any other universe-binding lemma. See `render_derive_address`.
pub(crate) fn is_derived_object_derive_address(program: &Program, fid: FunId) -> bool {
    let Some(func) = program.functions.get(&fid) else {
        return false;
    };
    let Some(m) = program.modules.get(&func.module) else {
        return false;
    };
    m.package_name == "Sui" && m.name == "derived_object" && func.name == "derive_address"
}

/// Whether function `fid` binds the abstract df/tycode universe `{__TyU}`
/// in its rendered signature. This is the single source of truth for the
/// `{__TyU}` binder gate -- it MUST mirror the `lemma_tycode_universe ||
/// df_universe || tycode_concrete_universe` condition at the `{__TyU}`
/// emission site inside `render_function` (keep the two in sync).
///
/// Used at TRANSLATED-callee call sites (`render::expr::call`) to decide
/// whether a caller must pin `(__TyU := __TyU)` (lemma caller forwarding
/// its own universe) or `(__TyU := _root_.TyCode)` (user-package caller
/// supplying the concrete closed universe). The earlier call-site gate
/// only checked tainted TYPE PARAMS (`tycode_typeparam_needs_constraint`),
/// so a callee that binds `{__TyU}` purely for a CONCRETE tycode-native
/// reason (e.g. `coin_registry::finalize` -> `type_name::with_original_ids
/// <bool>` on the fixed OTW sentinel) was never pinned, leaving Lean with
/// a constraint-only `__TyU` it cannot infer ("typeclass instance problem
/// is stuck").
pub(crate) fn binds_tycode_universe(context: &RenderContext<'_>, fid: FunId) -> bool {
    let program = context.program;
    let Some(func) = program.functions.get(&fid) else {
        return false;
    };
    let pkg_is_lemma = program
        .modules
        .get(&func.module)
        .map_or(false, |m| name_is_lemma_package(&m.package_name));
    if !pkg_is_lemma {
        return false;
    }
    let current_module = program.modules.get(&func.module).map(|m| m.name.as_str());

    let lemma_tycode_universe = (0..func.signature.type_params.len())
        .any(|i| context.tycode_typeparam_needs_constraint(fid, i));

    let df_universe = context.binds_df_universe(fid);

    let tycode_concrete_types =
        tycode_native_concrete_types(func, program, current_module, &func.signature.type_params);
    let tycode_concrete_universe = !tycode_concrete_types.is_empty();

    // `derive_address` binds `{__TyU}` for its hardcoded type-aware body
    // (see `is_derived_object_derive_address`), even though it hits no df
    // store native / tainted type_name param directly.
    lemma_tycode_universe
        || df_universe
        || tycode_concrete_universe
        || is_derived_object_derive_address(program, fid)
}

/// Emit the #23 type-aware `derived_object::derive_address`. The Move
/// source is `df::hash_type_and_key(parent.to_address(),
/// DerivedObjectKey(key))` -- an opaque native that drops the key's TYPE,
/// so two services storing different key types under one shared parent
/// derive the SAME address and collide on the `Claimed` df slot. Here the
/// key's tycode `Universe.typeName` is folded into a base-257 rolling hash
/// over the parent address bytes, so distinct key types map to distinct
/// addresses. Binds `{__TyU}` + a NAMED `[__hc : HasCode __TyU <key>]`
/// (the body projects `__hc.code`); `binds_tycode_universe` reports true
/// for this fn so every call site pins `(__TyU := ..)`.
fn render_derive_address<W: Write>(func: &Function, w: &mut LeanWriter<W>) {
    let tp_raw = func
        .signature
        .type_params
        .first()
        .map(String::as_str)
        .unwrap_or("t_tv0");
    let tp = escape::escape_identifier(tp_raw);
    w.write(&format!(
        "def derive_address {{__TyU : Type}} [Universe __TyU] ({tp} : Type) [DecidableEq {tp}] [Inhabited {tp}] [Repr {tp}] [__hc : HasCode __TyU {tp}] (parent : _root_.Object.ID) (key : {tp}) : Address :="
    ));
    w.indent(true);
    w.write("let t_t2_0 := (_root_.Object.id_to_address parent)\n");
    w.write("let __tn := (Universe.typeName (__hc.code))\n");
    // #6: ALSO fold the key VALUE (`(repr key).pretty`) into the hash, so
    // two keys of the SAME type but DIFFERENT values (e.g. two `AccountKey`
    // for distinct investors under one shared parent) derive DISTINCT
    // addresses. Type-only folding (#23) left same-type/different-value
    // keys colliding on the `Claimed` df slot -> spurious
    // `EObjectAlreadyExists`. Requires `[Repr key]`, threaded onto every
    // `derived_object::{claim,exists_,derive_address}` caller param and a
    // `Repr` instance on every concrete derived-object key struct.
    w.write("let __kv := (repr key).pretty\n");
    w.write("let __seed := (t_t2_0.bytes.val)\n");
    w.write("let __h1 := (__tn.toList.foldl (fun acc c => (acc * 257 + c.toNat + 1) % (2 ^ 256)) ((__seed + 1) % (2 ^ 256)))\n");
    w.write("Address.mk \u{27e8}(__kv.toList.foldl (fun acc c => (acc * 257 + c.toNat + 1) % (2 ^ 256)) __h1) % (2 ^ 256), Nat.mod_lt _ (by decide)\u{27e9}");
    w.dedent(false);
    w.newline();
    w.newline();
}

/// Whether a rendered concrete type string references any of `type_params`
/// as a whole identifier token. A concrete `[HasCode __TyU (<ty>)]`
/// hypothesis whose `<ty>` mentions a type param (e.g. `CurrencyKey t_tv0`
/// from a `derived_object::{claim,exists_}` key) must be DEFERRED until
/// after the `(T : Type)` binders -- emitting it early makes Lean
/// auto-bind a SEPARATE front implicit `{t_tv0}` and the hypothesis
/// constrains the wrong param ("failed to synthesize HasCode __TyU
/// (CurrencyKey t_tv0)"). Mirrors the `__ObjU` `obj_concrete_transfer`
/// deferral. Non-param concrete types stay in the early block.
fn type_string_mentions_type_param(ty: &str, type_params: &[String]) -> bool {
    fn is_ident_char(b: u8) -> bool {
        b == b'_' || b.is_ascii_alphanumeric()
    }
    fn contains_token(hay: &str, needle: &str) -> bool {
        if needle.is_empty() {
            return false;
        }
        let hb = hay.as_bytes();
        let nb = needle.as_bytes();
        let mut i = 0usize;
        while i + nb.len() <= hb.len() {
            if &hb[i..i + nb.len()] == nb {
                let before_ok = i == 0 || !is_ident_char(hb[i - 1]);
                let after = i + nb.len();
                let after_ok = after == hb.len() || !is_ident_char(hb[after]);
                if before_ok && after_ok {
                    return true;
                }
            }
            i += 1;
        }
        false
    }
    for tp in type_params {
        if contains_token(ty, tp) {
            return true;
        }
        let esc = escape::escape_identifier(tp);
        if esc.as_str() != tp.as_str() && contains_token(ty, &esc) {
            return true;
        }
    }
    false
}

pub fn render_function<W: Write>(
    func: &Function,
    fid: FunId,
    context: &RenderContext<'_>,
    current_module: Option<&str>,
    w: &mut LeanWriter<W>,
    force_partial: bool,
    as_proof_stub: bool,
    // Emit this member of a `mutual … end` block as `def … partial_fixpoint`
    // (rather than `partial def`). Set by `emit_function_sccs` only for a
    // fixpoint-eligible SCC -- every member a loop helper or abort companion
    // of a loop -- so each member is first-order and provably monotone.
    // Mutually exclusive with `force_partial`.
    force_fixpoint: bool,
    // For a read-only World-threaded fixpoint, the shared entry-World parameter
    // used to define the call-specific FlatOrder bottom.
    fixpoint_world_bottom: Option<&crate::ir::VarId>,
) -> RenderResult<()> {
    let program = context.program;
    // #23 type-aware `derive_address`: short-circuit the whole emission
    // with a hardcoded, type-aware body. The Move source funnels through
    // the opaque native `hash_type_and_key`, which carries NO type code,
    // so derived addresses collide across distinct key TYPES sharing a
    // parent (all four securitize services aliased the same
    // `Claimed{ID 0}` slot -> spurious `EObjectAlreadyExists`). We instead
    // fold `Universe.typeName` of the key's tycode into a base-257 rolling
    // hash over the parent address, binding `{__TyU}` + a named
    // `[__hc : HasCode __TyU <key>]`. Every caller pins `(__TyU := ..)`
    // via the standard machinery (`binds_tycode_universe` is true here).
    if is_derived_object_derive_address(program, fid) {
        render_derive_address(func, w);
        return Ok(());
    }
    // Proof obligations (stage 12, `FunctionKind::Theorem`) render as a
    // `Prop`-valued definition declared with the function they
    // constrain: `def NAME params : Prop := <statement>`. The Bool
    // statement body is coerced to a Prop (connective natives ->
    // →/↔/¬, Bool leaves -> `= true`). The actual `theorem … := proof`
    // lives in the durable `<Mod>_Proofs.lean` and references this
    // `def` by name. See the `is_theorem` branches at the return-type
    // slot and the body slot below.
    //
    // TRUSTED obligations (stage 12, `FunctionKind::Axiom`) share the
    // Prop-def rendering (`is_theorem` covers both), but instead of a
    // `_Proofs.lean` theorem they get an `axiom NAME_holds (params) :
    // <ns>.NAME args` right after the def in the SAME module file --
    // emitted via a second `render_function` call with
    // `as_proof_stub=true`, where `is_axiom` swaps the keyword/name and
    // drops the `:= by sorry`.
    let is_axiom = matches!(func.kind, crate::ir::FunctionKind::Axiom { .. });
    let is_theorem = matches!(func.kind, crate::ir::FunctionKind::Theorem { .. }) || is_axiom;

    // Post step 5 of `no-stubs-templated-natives.md`: native callees
    // live exclusively in `program.natives.decls` and resolve at
    // call sites via `Program::lookup_callee`. The per-function
    // render loop only sees translated `Function` entries with real
    // bodies; no native skip-block is needed.
    let escaped_name = escape::escape_identifier(&func.name);

    // Stage 7's loop-body helpers and their Spec.Aborts companions can
    // recurse through source loop state. They carry no pipeline-injected
    // fuel, and Lean generally cannot infer structural termination from
    // state such as `BoundedNat (2^64)` or List indices. The classification
    // below lets recursive bodies use the fixpoint/partial paths while a
    // non-recursive LoopAfter remains a plain `def`.
    let is_loop_helper = matches!(
        func.kind,
        crate::ir::FunctionKind::LoopBody { .. } | crate::ir::FunctionKind::LoopAfter { .. },
    );
    // The loop continuation `<fn>.while_N.after` is non-recursive (it just
    // returns the post-loop scope). It does not need `partial def`; emit it
    // as a plain `def` so its body is transparent (the carry-loop proof
    // unfolds it when the loop exits). Recursive/mutual afters still fall
    // back to `partial def` via `body_calls_self`/`force_partial`.
    let is_loop_after = matches!(func.kind, crate::ir::FunctionKind::LoopAfter { .. });
    let is_loop_helper_aborts = matches!(
        func.kind,
        crate::ir::FunctionKind::Spec { kind: crate::ir::SpecKind::Aborts, target }
            if matches!(
                program.functions.get(&target).map(|f| &f.kind),
                Some(crate::ir::FunctionKind::LoopBody { .. })
                    | Some(crate::ir::FunctionKind::LoopAfter { .. })
            ),
    );
    // Source-level self-recursion: a Move `fun foo` whose body calls
    // `foo` directly (a tree-recursive helper like a heapify or a
    // tree-walk). Lean can't prove termination structurally on
    // BoundedNat / List indices; emit `partial def` so the body
    // typechecks. Proof-carrying termination is deferred -- same
    // treatment as loop helpers.
    //
    // The render-side dep walker `walk_block_for_call_deps` filters
    // self-edges out, so the SCC `mutual ... end` wrapper doesn't
    // fire on these. Detect the self-call directly here by matching
    // any `Expr::Call { fun }` whose resolved function shares this
    // function's (module, name) pair.
    let body_calls_self = body_calls_self_by_name(&func.body, &func.module, &func.name, program);
    // A self-recursive loop helper (the `while_N` iteration or its
    // `.aborts` companion) is emitted as a total `def … partial_fixpoint`
    // instead of an opaque `partial def`. `partial_fixpoint` (Lean 4.31+)
    // attaches a denotational fixpoint semantics, generating `.eq_def` and
    // `.fixpoint_induct` so the loop body is PROVABLE -- an opaque
    // `partial def` exposes nothing (no unfolding, no induction), which is
    // why the add/sub/wrapping family was previously unprovable. Fires for
    // ANY direct self-recursion (`body_calls_self`): generated loop helpers
    // AND source-level tree-recursive Move functions (e.g.
    // `priority_queue::max_heapify_recursive`), whose single tail-position
    // self-call is monotone, so `partial_fixpoint`'s derivation goes through
    // and downstream proofs get `.eq_def`. Excluded: `force_partial` (a
    // member of a NON-fixpoint-eligible mutual SCC -- Lean forbids mixing
    // `partial def` and `partial_fixpoint` in one block). `emit_fixpoint` is
    // cleared below if the body falls back to `sorry` (then a plain
    // `def := sorry` is fine, since the fallback body is non-recursive). The
    // trailing `partial_fixpoint` clause is appended after the body.
    // Covers BOTH value-returning bodies AND the abort-side companions
    // (`<fn>.aborts.while_N`, `<fn>.aborts.cont_N`, returning
    // `Abort.AbortResult`). Abort loops would otherwise fail
    // `partial_fixpoint`'s monotonicity derivation, because the
    // abort-propagation `match` has a `let`-bound scrutinee -- we repair that
    // just before rendering via `inline_aborts_match_scrutinees`, which
    // inlines the (pure) scrutinee so the recursive call lives only in the
    // `NoAbort` arm (monotone). `force_fixpoint` (a fixpoint-eligible
    // mutual-block member: a loop's abort/continuation SCC, OR the abort SCC
    // of a TAIL-recursive source function) emits `partial_fixpoint` even
    // though its recursion is mutual, not a direct self-call (so
    // `body_calls_self` is false for it). NOTE: the abort SCC of a
    // self-recursive SOURCE function is fixpoint-eligible ONLY when its abort
    // recursion is TAIL-position: the recursive `.aborts` call starts in a
    // `match` scrutinee (non-monotone), but
    // `collapse_tail_recursive_aborts_match` rewrites the identity
    // abort-propagation into the bare recursive call (tail-position,
    // monotone) when the post-recursion continuation is trivially NoAbort
    // (see `scc_is_fixpoint_eligible` shape 2, e.g.
    // `priority_queue::max_heapify_recursive`). A NON-tail source abort SCC
    // stays `partial def` via `force_partial`; the source's tail-recursive
    // VALUE face flips to `partial_fixpoint` via `body_calls_self` above.
    let execution_only =
        context.loop_termination.mode() == super::loop_termination::LoopMode::Execution;
    let mut emit_fixpoint = !as_proof_stub
        && !execution_only
        && (force_fixpoint || (body_calls_self && !force_partial));
    // `partial_fixpoint`'s flat-order monotonicity prover only eliminates a
    // recursive call in TAIL position, so a lone self-recursive source
    // function, or its abort companion, takes the fixpoint path only when its
    // recursion is tail-position; otherwise it keeps the opaque `partial def`.
    // Generated loop helpers are tail-recursive by construction and a mutual
    // block is gated by `scc_is_fixpoint_eligible`; neither is re-checked.
    if emit_fixpoint && !force_fixpoint && !source_self_recursion_is_tail_position(func, program) {
        emit_fixpoint = false;
    }
    // PROOF-mode opt-in: a SINGLE self-recursive loop helper (not a mutual
    // `force_fixpoint` block) whose measure + decreasing proof a human has
    // registered (non-`sorry`) is emitted as a genuinely total
    // `def … termination_by <measure> decreasing_by <tactic>` instead of
    // `partial_fixpoint`. Same body, different terminator -- both expose
    // `.eq_def`, so spec proofs are agnostic; the total form additionally
    // carries a real termination certificate. `ready_entry` returns `None`
    // in `Test` mode (a `sorry` in the termination arg would poison
    // `#eval`) and whenever no ready registry entry exists, so the default
    // is unchanged `partial_fixpoint`. Cleared below if the body falls back
    // to `sorry` (a non-recursive body needs neither terminator).
    let mut total_entry = if emit_fixpoint && !force_fixpoint {
        super::loop_termination::ready_entry(&context.loop_termination, program, func)
    } else {
        None
    };
    if total_entry.is_some() {
        emit_fixpoint = false;
    }
    let fixpoint_world_bottom = emit_fixpoint.then_some(fixpoint_world_bottom).flatten();
    let mark_simp_aborts =
        !as_proof_stub && !is_theorem && is_trivial_total_aborts_companion(func, program);
    if mark_simp_aborts {
        w.line("@[simp]");
    }
    if as_proof_stub {
        // Durable proofs file: prove the named obligation prop. The
        // `def NAME : Prop := <stmt>` lives in the module; here we emit
        // `theorem NAME params : <ns>.NAME args := by sorry`.
        // Trusted obligations are ASSUMED instead: `axiom NAME_holds
        // (params) : <ns>.NAME args` -- no proof body, greppable via
        // `#print axioms`.
        if is_axiom {
            w.write("axiom ");
        } else {
            w.write("theorem ");
        }
    } else if emit_fixpoint || total_entry.is_some() {
        w.write("def ");
    } else if (is_loop_helper && !is_loop_after)
        || is_loop_helper_aborts
        || body_calls_self
        || force_partial
    {
        w.write("partial def ");
    } else {
        w.write("def ");
    }
    if as_proof_stub && is_axiom {
        w.write(&escape::escape_identifier(
            &crate::ir::names::axiom_holds_name(&func.name),
        ));
    } else {
        if as_proof_stub {
            w.write("_root_.");
        }
        w.write(&escaped_name);
    }

    // Type parameters: emit as explicit `(T : Type) [DecidableEq T] [Inhabited T]`,
    // plus `[HasCode _root_.TyCode T]` IF this function lives in a
    // non-lemma (user) package -- those files import
    // `Generated.TyCodeInterp` so the constraint resolves at call
    // sites. Lemma-package files don't import TyCode (and importing
    // it would re-introduce the framework -> user cycle), so we
    // skip the constraint there.
    //
    // The HasCode constraint enables Lean's instance search to
    // synthesize `HasCode TyCode (SupportedAsset T)`,
    // `HasCode TyCode (Node T)`, etc. via the derived wrapping
    // instances emitted in `Generated/TyCodeInterp.lean`.
    // `SuiSpecs` and `SuiSystem` are rendered per-project, so their
    // emission files DO import `Generated.TyCodeInterp` and CAN carry
    // `[HasCode _root_.TyCode T]` constraints. The remaining lemma
    // packages -- `Prelude`, `Prover`, `Sui`, `MoveStdlib`, `Pyth`,
    // `Wormhole`, `DeepBook`, `Generated`, `NewPipeline` -- are
    // hand-written / cross-project framework files that must remain
    // independent of the per-project universe to avoid a render
    // cycle. Functions in those packages stay generic in `U`.
    let pkg_is_lemma = program
        .modules
        .get(&func.module)
        .map_or(false, |m| name_is_lemma_package(&m.package_name));
    // A lemma-package function that calls a `type_name::*` native with
    // one of its own type params is kept universe-POLYMORPHIC: rather
    // than pinning `_root_.TyCode` (which would force a
    // Generated.TyCodeInterp import and a render cycle -- the lemma
    // module's own structs are TyCode leaves), we bind an abstract
    // universe `__TyU` here and thread `[HasCode __TyU Ti]` per tainted
    // param. The type_name call inside the body infers `__TyU` from
    // that constraint; concrete `U := TyCode` resolution happens at the
    // user call site. User packages don't need this -- they carry
    // `[HasCode _root_.TyCode Ti]` directly and import TyCodeInterp.
    let lemma_tycode_universe = pkg_is_lemma
        && (0..func.signature.type_params.len())
            .any(|i| context.tycode_typeparam_needs_constraint(fid, i));
    // Dynamic-field store natives (`dynamic_field::store_*`, the routed
    // form of df add/borrow/borrow_mut/exists) in a LEMMA package need
    // the same universe-polymorphic treatment as `type_name` callers:
    // the world's BagEntry slot must be `Bag.Entry __TyU` and every
    // stored K/V type needs `[HasCode __TyU ..]`. User packages import
    // `Generated.World` (whose concrete `World` abbrev already pins the
    // slot to `Bag.Entry _root_.TyCode`) + `Generated.TyCodeInterp`, so
    // they need none of this. See `render::ty` WORLD_BAGENTRY_OVERRIDE.
    // Param taint follows call edges (`compute_df_universe`): a lemma
    // function that calls a df-universe function with its own type params
    // needs the same `[HasCode __TyU T]` binders.
    let (df_concrete_direct, df_param_idxs) = if pkg_is_lemma {
        let (direct, _) =
            df_store_universe_types(func, program, current_module, &func.signature.type_params);
        (direct, context.df_typeparams(fid))
    } else {
        (Vec::new(), std::collections::BTreeSet::new())
    };
    // #6: type params threaded as a BARE derived-object KEY (into
    // `derived_object::{claim,exists_,derive_address}`) need `[Repr T]`
    // because `derive_address` now folds `(repr key).pretty`. Computed for
    // BOTH lemma and user packages (a user `register<K>` may call
    // `claim<K>`). Concrete key types resolve via the struct's own `Repr`
    // instance (see `derived_object_key_struct_names` + `struct_def`).
    let repr_param_idxs = derived_object_key_repr_param_idxs(program, func);
    // `df_concrete_direct` holds only this function's OWN direct df
    // value types. A `.aborts` Spec companion / `.cont_N` fragment that
    // merely THREADS its world into a universe-polymorphic sibling (e.g.
    // `coin_registry::new_currency.aborts` calling `derived_object::
    // exists_` and its own cont fragments) under-reports -- it joins the
    // `__TyU` df universe transitively but hits no df native directly.
    // `df_concrete_types_for` returns the direct set UNIONED with what
    // flows across Spec-companion / cont-fragment edges, so such a
    // function still binds `{__TyU}` and supplies the same `[HasCode
    // __TyU ..]` hypotheses its siblings require. `df_param_idxs` stays
    // direct (no client needs companion inheritance of param taint here).
    let df_concrete_types = if pkg_is_lemma {
        context.df_concrete_types(fid).to_vec()
    } else {
        df_concrete_direct
    };
    let df_universe = !df_concrete_types.is_empty()
        || !df_param_idxs.is_empty()
        || (pkg_is_lemma && context.binds_df_universe(fid));
    // A lemma-package function may pin `(U := __TyU)` on a
    // `type_name::*` / `is_one_time_witness` / `bcs::to_bytes` native
    // call applied to a CONCRETE type (no tainted type param) -- e.g.
    // `coin_registry::new_currency` calling
    // `type_name::with_original_ids<bool>` on the fixed OTW sentinel.
    // Such a function still references `__TyU` in its body, so it must
    // bind `{__TyU}` and carry `[HasCode __TyU <concrete>]`, even though
    // neither `lemma_tycode_universe` (no tainted param) nor `df_universe`
    // fires. Concrete `__TyU := TyCode` resolution happens at the user
    // call site (which imports `Generated.TyCodeInterp`).
    let tycode_concrete_types = if pkg_is_lemma {
        tycode_native_concrete_types(func, program, current_module, &func.signature.type_params)
    } else {
        Vec::new()
    };
    let tycode_concrete_universe = !tycode_concrete_types.is_empty();
    // Capture the exact binder segment (universe binders + type params +
    // deferred instance hypotheses + value params) as it is written, so
    // the conjunct-projection pass can reuse it VERBATIM for the emitted
    // `.c<k>` leaf defs and the `_conj` theorem. `sigw!` tees every
    // binder write to both the real writer and `sig`; the companion
    // output is unchanged (`sig` is a side copy). All binder emission
    // below MUST go through `sigw!` for the capture to stay complete.
    let mut sig = String::new();
    macro_rules! sigw {
        ($s:expr) => {{
            let __s = $s;
            w.write(__s);
            sig.push_str(__s);
        }};
    }
    if lemma_tycode_universe || df_universe || tycode_concrete_universe {
        sigw!(" {__TyU : Type} [Universe __TyU] [Repr __TyU]");
    }
    // A LEMMA-package function with a type param flowing into a
    // `bag::*` / `object_bag::*` op is kept universe-POLYMORPHIC over an
    // abstract bag universe `__BagU` (distinct from the df universe
    // `__TyU`): the bag op infers its universe from the `Bag` value, and
    // each bag-tainted param carries `[HasCode __BagU T]`. Concrete
    // `__BagU := BagU` resolution happens at the user call site (which
    // imports BagUInterp), avoiding a BagUInterp render cycle in the
    // lemma module. User packages pin `_root_.BagU` directly instead.
    let lemma_bagu_universe = pkg_is_lemma
        && (0..func.signature.type_params.len())
            .any(|i| context.bagu_typeparam_needs_constraint(fid, i));
    // A lemma module that OWNS a `Bag` struct field imports
    // `Generated.BagUInterp` (so `_root_.BagU` is in scope) and renders
    // that field concretely as `Bag.Bag _root_.BagU`. For bags, such a
    // module behaves like a USER package: `bag::new` pins the concrete
    // `_root_.BagU` (see render::expr::call, gated on
    // `caller_module_has_bag_struct`), so the empty-bag case below must
    // NOT bind the abstract `{__BagU}` -- doing so would leave an unused
    // binder while the body references `_root_.BagU`, and (worse) make a
    // fresh bag `Bag.Bag __BagU` clash with the concrete struct field
    // `Bag.Bag _root_.BagU` it flows into.
    let module_imports_bagu_interp =
        super::dyn_type_universe::module_has_bag_struct(program, func.module);
    // A lemma-package function that builds a fresh EMPTY bag via
    // `bag::new` pins `(U := __BagU)` at the call site with no
    // bag-tainted type param to anchor it (e.g. a lemma `bag` wrapper
    // initialising an empty Bag in a module that does NOT own a bag
    // struct). It must still bind `{__BagU}`. `[Universe __BagU]` alone
    // discharges `bag::new` -- no `[HasCode __BagU ..]` is needed for an
    // empty bag. Suppressed when the module imports BagUInterp (concrete
    // `_root_.BagU` is pinned at the call site instead).
    let body_bag_new =
        pkg_is_lemma && !module_imports_bagu_interp && body_calls_abstract_bag_new(func, program);
    if lemma_bagu_universe || body_bag_new {
        sigw!(" {__BagU : Type} [Universe __BagU] [Repr __BagU]");
    }
    let mut world_type_overrides = super::ty::WorldTypeOverrides::default();
    if df_universe {
        for ty in &df_concrete_types {
            if !type_string_mentions_type_param(ty, &func.signature.type_params) {
                sigw!(&format!(" [HasCode __TyU ({})]", ty));
            }
        }
        world_type_overrides.df_entry = Some("Bag.Entry __TyU".to_string());
    }
    // Concrete-type `[HasCode __TyU ..]` hypotheses for `type_name::*` /
    // OTW / `bcs::to_bytes` natives applied to a concrete type (the
    // `tycode_concrete_universe` case above). Deduped against the df
    // store types, which already emit their own `[HasCode __TyU ..]`.
    for ty in &tycode_concrete_types {
        if !df_concrete_types.contains(ty)
            && !type_string_mentions_type_param(ty, &func.signature.type_params)
        {
            sigw!(&format!(" [HasCode __TyU ({})]", ty));
        }
    }
    // A universe-polymorphic lemma function that transfers / shares /
    // freezes a CONCRETE object (e.g. `package::claim_and_keep` ->
    // `Publisher`) can't resolve `[HasCode ObjType T] [HasObjectId T]` for
    // the concrete `T` itself (T's universe code lives only in the
    // project's `Generated.ObjTypeInterp`, which this lemma module can't
    // import -- ObjTypeInterp imports it -> cycle). Instead take those
    // instances as HYPOTHESES: the user-package CALL site (which imports
    // ObjTypeInterp) synthesizes them. The world's Object slot is pinned
    // to `Bag.Entry _root_.ObjType` -- the concrete OBJECT universe (the
    // `Generated.ObjType` enum is always imported, no cycle) -- which is
    // SEPARATE from the function's `__TyU` (the TyCode universe used for
    // the one-time-witness `type_name`). The `transfer::*` native then
    // unifies `ObjUniv := _root_.ObjType` from the world arg.
    // See plans/lean-pipeline/import-cycle-build-failures.md.
    // Fire for ANY lemma-package function that transfers a CONCRETE object,
    // not only `lemma_tycode_universe` (tainted-type-param) ones. A
    // NON-generic concrete transfer -- e.g. `clock::share_for_testing`
    // calling `share_object Clock` -- equally needs the world's Object slot
    // pinned: it constrains the slot to `Bag.Entry ObjType`, but the
    // module's polymorphic `World` notation leaves `__WorldObject` free, so
    // `Universe ?m.4` fails to synthesize (cetus-dlmm Sui/Clock.lean). The
    // `__ObjU` path pins the slot ABSTRACTLY with `[Universe __ObjU]` as a
    // hypothesis resolved at the user call site, so -- unlike a module-level
    // concrete `_root_.ObjType` pin -- the lemma module imports no
    // `ObjTypeInterp` and introduces no render/build cycle.
    // See plans/lean-pipeline/cetus-dlmm-sui-clock-universe-bug.md.
    //
    // The concrete `[HasCode __ObjU T]` / `[Object.HasObjectId T]`
    // hypotheses are NOT emitted here: when `T` mentions one of this
    // function's type params (e.g. `Currency t_tv0`), emitting them
    // before the `(t_tv0 : Type)` binder below makes Lean auto-bind a
    // SEPARATE front implicit `{t_tv0}`, so the body's explicit `t_tv0`
    // never matches the hypothesis. They are deferred until AFTER the
    // type-param binders (see `obj_concrete_transfer` emission below).
    // Only the universe binder `{__ObjU : Type} [Universe __ObjU]` and
    // the world-Object pin are set up here -- neither references a type
    // param.
    let obj_concrete_transfer = if pkg_is_lemma {
        transferred_concrete_object_types(
            func,
            program,
            current_module,
            &func.signature.type_params,
        )
    } else {
        Vec::new()
    };
    // Concrete objects read via an `object::id` / `id_address` accessor
    // need ONLY `[Object.HasObjectId T]` (no `__ObjU`, no world pin).
    // Deduped against the transfer set, which already emits HasObjectId.
    let obj_concrete_id = if pkg_is_lemma {
        context.obj_id_concrete_types(fid).to_vec()
    } else {
        Vec::new()
    };
    if pkg_is_lemma {
        // Also fire for GENERIC ObjType-tainted type params (e.g.
        // `transfer::public_transfer<T>`, `test_scenario::take_shared<T>`):
        // their `[HasCode ObjType T]` must be the ABSTRACT `[HasCode __ObjU T]`
        // (resolved at the user call site), NOT a `_root_.ObjType` pin --
        // pinning `_root_.ObjType` here forces `Universe ObjType`, which lives
        // only in `Generated.ObjTypeInterp`, and importing that into a
        // framework module (e.g. `Sui.Transfer`, pulled in by `Sui.Package`)
        // closes a `TyCodeInterp -> Sui.Package -> Sui.Transfer ->
        // ObjTypeInterp -> TyCodeInterp` build cycle. Mirrors the abstract
        // `__TyU`/`__BagU` treatment of the other universes. See
        // plans/lean-pipeline/import-cycle-build-failures.md.
        let has_obj_tainted_tp = (0..func.signature.type_params.len())
            .any(|i| context.obj_typeparam_needs_constraint(fid, i));
        if !obj_concrete_transfer.is_empty() || has_obj_tainted_tp {
            // Abstract OBJECT universe `__ObjU`, kept DISTINCT from the
            // TyCode universe `__TyU` (which serves the one-time-witness
            // `type_name`). Conflating them breaks at the call site, where
            // `__TyU` infers to `TyCode` (from the OTW) but the world's
            // Object slot is `ObjType`. With a separate `__ObjU`: the world
            // is `Bag.Entry __ObjU`, each concrete object T carries
            // `[HasCode __ObjU T] [HasObjectId T]`, and `[Universe __ObjU]`
            // is a hypothesis -- all resolved at the user-package call site
            // (`__ObjU := _root_.ObjType`, instances from ObjTypeInterp), so
            // the lemma module needs no ObjTypeInterp import (no cycle).
            sigw!(" {__ObjU : Type} [Universe __ObjU]");
            world_type_overrides.object = Some("Bag.Entry __ObjU".to_string());
        }
        // CONCRETE map-key borrows: a lemma-package function that wraps a
        // concrete key (e.g. `sui::versioned::load_value_mut`, keyed by a
        // `u64`) emits `IntoKey.intoKey <key>` against the abstract
        // `__MutKey`, so it needs a `[IntoKey AnyKey <payload>]`
        // hypothesis per distinct concrete key type. `AnyKey` is the
        // file-scoped notation for `__MutKey`; the user-package call site
        // resolves the instance via `Generated.AnyKey`. See
        // `render::expr::util::render_anykey_wrap`.
        for payload in lemma_concrete_map_key_payloads(func, program) {
            sigw!(&format!(" [IntoKey AnyKey ({})]", payload));
        }
    }
    for (tp_index, tp) in func.signature.type_params.iter().enumerate() {
        let tp_esc = escape::escape_identifier(tp);
        // Per-typeparam ObjType+HasObjectId taint, used for both
        // user-package and lemma-package functions. Lemma functions
        // (e.g. `Sui.Test_scenario.take_shared<T>`) need to thread
        // the typed constraints into the natives they call -- their
        // bodies pass the constraints abstractly without needing
        // resolution against the project's `Generated.ObjTypeInterp`
        // (which they don't import). The actual resolution happens
        // at user-code call sites that DO import ObjTypeInterp.
        let needs_obj = context.obj_typeparam_needs_constraint(fid, tp_index);
        // Lemma-package functions that call a `type_name::*` native
        // with this type param need `[HasCode _root_.TyCode T]` too,
        // even though lemma packages otherwise stay universe-generic.
        // The `(U := _root_.TyCode)` injection at the call site (see
        // render::expr) makes the native require it. User packages
        // carry the TyCode constraint on every param unconditionally,
        // so this taint only matters in the lemma branch.
        let needs_tycode = context.tycode_typeparam_needs_constraint(fid, tp_index)
            || df_param_idxs.contains(&tp_index);
        // `[ToAnyKey T] [FromAnyKey T]` are needed only on type params
        // that transitively reach a map-key typeclass use (a bare
        // `TypeParam` key -- the `ToAnyKey.toAnyKey` wrap / the
        // `generic_key` `FromAnyKey.fromAnyKey` recover). Gated like
        // the other constraints (and emitted in BOTH the lemma and
        // user branches): the universal `ToAnyKey` catch-all is gone,
        // so demanding it on a non-key param would fail to resolve at
        // a concrete non-key instantiation. See
        // `mutation::compute_anykey_typeparam_deps`.
        //
        // Stage-12 obligation props (`is_theorem` -- Theorem+Axiom,
        // rendered `def NAME params : Prop :=`) additionally carry the
        // round-trip law `[LawfulAnyKey T]` right after the pair. The
        // obligation's provability (the writeback lowering composes
        // `fromAnyKey (toAnyKey k)`) depends on the law, but the impl
        // defs / `_spec` companions / `.aborts` etc. only COMPUTE the
        // composite and must NOT demand it -- their helper lemmas carry
        // just the pair, and the two data classes do not imply the law
        // (the `AnyKeyGap` certificate). So the extra binder is emitted
        // for obligation decls only; concrete instantiations discharge
        // it via the per-variant `rfl` `LawfulAnyKey` instances in
        // `Generated.AnyKey`. See `mutation::render_any_key_file`.
        let anykey = if context.anykey_typeparam_needs_constraint(fid, tp_index) {
            if pkg_is_lemma {
                // Framework (lemma) modules never import `Generated.AnyKey`,
                // where `ToAnyKey` / `FromAnyKey` live: key through the
                // prelude's `IntoKey` / `FromKey` over the abstract
                // `AnyKey := __MutKey`, exactly as concrete keys do.
                format!(" [IntoKey AnyKey {0}] [FromKey AnyKey {0}]", tp_esc)
            } else if is_theorem {
                format!(
                    " [ToAnyKey {0}] [FromAnyKey {0}] [LawfulAnyKey {0}]",
                    tp_esc
                )
            } else {
                format!(" [ToAnyKey {0}] [FromAnyKey {0}]", tp_esc)
            }
        } else {
            String::new()
        };
        // #6: a derived-object KEY param needs `[Repr T]` because
        // `derive_address` folds `(repr key).pretty`. Emitted in BOTH
        // branches; harmless on lemmas never instantiated with a concrete
        // key (the hypothesis just stays abstract).
        let repr_bind = if repr_param_idxs.contains(&tp_index) {
            format!(" [Repr {}]", tp_esc)
        } else {
            String::new()
        };
        if pkg_is_lemma {
            // Generic-universe HasCode for type_name callers (see
            // `lemma_tycode_universe` above): `[HasCode __TyU T]`,
            // NOT `[HasCode _root_.TyCode T]`.
            let tycode = if needs_tycode {
                format!(" [HasCode __TyU {}]", tp_esc)
            } else {
                String::new()
            };
            // Bag-tainted lemma params carry `[HasCode __BagU T]` (the
            // abstract bag universe bound by `lemma_bagu_universe`).
            let bagu = if context.bagu_typeparam_needs_constraint(fid, tp_index) {
                format!(" [HasCode __BagU {}]", tp_esc)
            } else {
                String::new()
            };
            if needs_obj {
                // Abstract object universe `__ObjU` (bound above as
                // `{__ObjU : Type} [Universe __ObjU]`), NOT `_root_.ObjType`:
                // keeps the lemma module free of the `Generated.ObjTypeInterp`
                // import (and the build cycle it closes). The concrete
                // `__ObjU := _root_.ObjType` resolution happens at the user
                // call site, which imports ObjTypeInterp.
                sigw!(&format!(
                    " ({0} : Type) [DecidableEq {0}] [Inhabited {0}]{1}{2} [HasCode __ObjU {0}] [Object.HasObjectId {0}]{3}{4}",
                    tp_esc, tycode, bagu, anykey, repr_bind
                ));
            } else {
                sigw!(&format!(
                    " ({0} : Type) [DecidableEq {0}] [Inhabited {0}]{1}{2}{3}{4}",
                    tp_esc, tycode, bagu, anykey, repr_bind
                ));
            }
        } else {
            // Every user-package type param carries the TyCode
            // constraint (TyCode is closed-universe over every type
            // that appears in heterogeneous storage; the recursive
            // wrapping derivation makes `HasCode TyCode (...)`
            // resolvable for any project type). Only type params
            // that transitively flow into a `transfer::*` or
            // `test_scenario::take_*` callsite need the ObjType +
            // HasObjectId constraints. Over-approximating would
            // break generic helpers like `queue::new<T>` when
            // instantiated with non-object types like `u64`, since
            // `HasObjectId u64` doesn't exist.
            //
            // A type param that flows into a `bag::*` / `object_bag::*`
            // op additionally carries `[HasCode _root_.BagU T]` -- the
            // bag op infers its universe `BagU` from the `Bag` value and
            // needs the K/V HasCode in that SEPARATE universe. Unlike
            // TyCode this is CONDITIONAL (BagU has no instance for
            // arbitrary T), so we gate it on the bag taint.
            let needs_bagu = context.bagu_typeparam_needs_constraint(fid, tp_index);
            let bagu = if needs_bagu {
                format!(" [HasCode _root_.BagU {}]", tp_esc)
            } else {
                String::new()
            };
            if needs_obj {
                // An OBJECT type param resolves `HasCode TyCode` only
                // when it actually flows into a tycode call. Adding it
                // unconditionally breaks when the param is instantiated
                // with a Bag-containing object (e.g. scallop's
                // `Obligation`): such structs are excluded from the
                // TyCode universe, yet `assert_owner<Item: key>` -- which
                // only calls `object::id(item)` -- would still demand
                // `HasCode TyCode Obligation`. Objects use ObjType; keep
                // TyCode only when `needs_tycode` says it's truly used.
                let tycode = if needs_tycode {
                    format!(" [HasCode _root_.TyCode {}]", tp_esc)
                } else {
                    String::new()
                };
                sigw!(&format!(
                    " ({0} : Type) [DecidableEq {0}] [Inhabited {0}]{1}{2} [HasCode _root_.ObjType {0}] [Object.HasObjectId {0}]{3}{4}",
                    tp_esc, tycode, bagu, anykey, repr_bind
                ));
            } else {
                sigw!(&format!(
                    " ({0} : Type) [DecidableEq {0}] [Inhabited {0}] [HasCode _root_.TyCode {0}]{1}{2}{3}",
                    tp_esc, bagu, anykey, repr_bind
                ));
            }
        }
    }

    // Deferred concrete OBJECT-universe hypotheses, emitted AFTER the
    // type-param binders above so a concrete object type that mentions a
    // type param (e.g. `Currency t_tv0`, `Coin.TreasuryCap t_tv0`) has
    // that param IN SCOPE. Emitting them earlier (in the `{__ObjU}`
    // block) made Lean auto-bind a separate front implicit `{t_tv0}`,
    // breaking instance resolution at every use site. Lemma-package only;
    // universe vars (`__ObjU`) are implicit so this does not change the
    // explicit positional calling convention.
    if pkg_is_lemma {
        // Transferred concrete objects need BOTH the universe code and the
        // object-id witness (the `transfer::*` native consumes both).
        for t in &obj_concrete_transfer {
            sigw!(&format!(
                " [HasCode __ObjU {0}] [_root_.Object.HasObjectId {0}]",
                t
            ));
        }
        // Id-accessed concrete objects need only the object-id witness.
        // Skip any already covered by the transfer set above.
        for t in &obj_concrete_id {
            if !obj_concrete_transfer.contains(t) {
                sigw!(&format!(" [_root_.Object.HasObjectId {0}]", t));
            }
        }
        // Concrete df/tycode `[HasCode __TyU (<ty>)]` hypotheses whose
        // type MENTIONS a type param (e.g. `CurrencyKey t_tv0` from a
        // `derived_object::{claim,exists_}` key) are deferred to here --
        // AFTER the `(T : Type)` binders -- for the same reason as the
        // `__ObjU` hypotheses above: emitting them early makes Lean
        // auto-bind a separate front implicit `{t_tv0}`. Non-param
        // concrete types stayed in the early block. Deduped: tycode
        // entries already covered by df are skipped.
        for ty in &df_concrete_types {
            if type_string_mentions_type_param(ty, &func.signature.type_params) {
                sigw!(&format!(" [HasCode __TyU ({})]", ty));
            }
        }
        for ty in &tycode_concrete_types {
            if type_string_mentions_type_param(ty, &func.signature.type_params)
                && !df_concrete_types.contains(ty)
            {
                sigw!(&format!(" [HasCode __TyU ({})]", ty));
            }
        }
    }

    // Regular parameters. Build the disambiguated name list once so
    // the signature print and the body's `var_overrides` agree. Two
    // Move parameters named `_` (allowed for "intentionally unused")
    // both escape to `_arg`; without disambiguation Lean rejects the
    // second binder as a duplicate. Suffix repeats with `_N` so each
    // param name is unique within the signature.
    let tp_names: Vec<String> = func.signature.type_params.clone();
    let mut pnames: Vec<String> = Vec::with_capacity(func.signature.params.len());
    {
        let mut seen: std::collections::BTreeSet<String> = std::collections::BTreeSet::new();
        for p in &func.signature.params {
            if p.name.is_empty() {
                return Err(RenderError::EmptyParamName {
                    func: func.name.clone(),
                });
            }
            let base = escape::escape_identifier(&p.name);
            let mut n = base.clone();
            let mut i: usize = 2;
            while !seen.insert(n.clone()) {
                n = format!("{}_{}", base, i);
                i += 1;
            }
            pnames.push(n);
        }
    }
    let type_context = ty::TypeRenderContext::new(
        program,
        current_module,
        Some(&tp_names),
        &world_type_overrides,
    );
    for (p, pname) in func.signature.params.iter().zip(pnames.iter()) {
        let tystr = ty::type_to_string_in(&p.ty, &type_context);
        sigw!(" (");
        sigw!(pname);
        sigw!(" : ");
        sigw!(&tystr);
        sigw!(")");
    }

    // Return type. Always rendered; the body's tail is constrained by
    // `BlockTail::Value(e)` (after stage 3) to a single expression.
    // Obligation defs are `Prop`-typed (the IR signature says `Bool`,
    // but the body renders as a Prop statement); their body slot below
    // emits the statement.
    if as_proof_stub {
        // The proof goal is the obligation prop (a `def … : Prop` in the
        // module) applied to this theorem's own params. Explicit args, in
        // declaration order, are the type params followed by the value
        // params; instance args (`[DecidableEq _]` etc.) are inferred.
        let m = &program.modules[&func.module];
        let modns = super::escape::module_render_namespace(&m.package_name, &m.name);
        w.write(" : ");
        w.write(&modns);
        w.write(".");
        w.write(&escaped_name);
        for tp in &tp_names {
            // The binder renders the type param as `escape_identifier(tp)`
            // (`$tv0` -> `t_tv0`); the application arg must match.
            w.write(" ");
            w.write(&escape::escape_identifier(tp));
        }
        for pn in &pnames {
            w.write(" ");
            w.write(pn);
        }
        if !is_axiom {
            w.write(" :=");
        }
    } else if is_theorem {
        w.write(" : Prop :=");
    } else {
        w.write(" : ");
        let ret_str = ty::type_to_string_in(&func.signature.return_type, &type_context);
        if let Some(bottom_param) = fixpoint_world_bottom {
            let world_name = func
                .signature
                .params
                .iter()
                .position(|p| &p.var == bottom_param)
                .and_then(|index| pnames.get(index))
                .expect("validated fixpoint World parameter");
            let (result_type, world_type) = match &func.signature.return_type {
                crate::ir::Type::Tuple(parts) if parts.len() == 2 => (&parts[0], &parts[1]),
                _ => unreachable!("validated pair-valued World fixpoint return"),
            };
            let result_str = ty::type_to_string_in(result_type, &type_context);
            let world_str = ty::type_to_string_in(world_type, &type_context);
            w.write("_root_.Prover.World.ReadOnlyWorldResult ");
            w.write(&world_str);
            w.write(" (");
            w.write(&result_str);
            w.write(") ");
            w.write(world_name);
        } else {
            w.write(&ret_str);
        }
        w.write(" :=");
    }

    // Body.
    w.indent(true);
    // Build the var-id -> display-name map so the body uses parameter
    // names instead of the upstream pipeline's SSA temps (`$t0`).
    let mut var_overrides = BTreeMap::new();
    let mut var_types: BTreeMap<crate::ir::VarId, crate::ir::Type> = BTreeMap::new();
    for (p, pname) in func.signature.params.iter().zip(pnames.iter()) {
        if !p.name.is_empty() {
            // Use the disambiguated, Lean-escaped name so body
            // references resolve to the unique signature binder
            // (e.g. two `_` params print as `_arg` and `_arg_2`).
            var_overrides.insert(p.var.clone(), pname.clone());
        }
        var_types.insert(p.var.clone(), p.ty.clone());
    }
    // Param types are the only entries we have up-front. The
    // renderer updates `var_types` as it walks each `Stmt::Let`, so
    // a reference at the call site sees the binding that was in
    // scope at that point (not the final value of a shadowed name).
    let mut borrow_sources: BTreeMap<crate::ir::VarId, super::expr::RuntimeBorrowSource> =
        BTreeMap::new();
    // Record witness-gated map borrow_mut values (x::wit_table::borrow_mut)
    // as MapKey sources FIRST, so `collect_borrow_sources`'s WriteBack/
    // WriteRef inheritance threads the key through the borrowed value's
    // field-set chain to the writeback child (the inner `.table`).
    super::expr::collect_map_borrow_sources(program, &func.body, &mut borrow_sources);
    super::expr::collect_borrow_sources(&func.body, &mut borrow_sources);
    let mut borrow_mut_origins: BTreeMap<crate::ir::VarId, super::expr::BorrowMutOrigin> =
        BTreeMap::new();
    super::expr::collect_borrow_mut_origins(&func.body, &mut borrow_mut_origins);
    // Pre-pass: trace let-bound results of mutating natives
    // (`Bag.add`, `Table.remove`, etc.) back to the borrowed-mut
    // variable they logically replace. The writeback dispatch in
    // `apply_edge_inner_only` reads this map to thread the
    // borrowed Mutation's `.mapKey k` path through to the
    // writeback child, which is the only way
    // `writeBackGhostMapKey` can recover the runtime key. See
    // `ExprCtx::borrow_mut_derivatives` and the writeback dispatch
    // in `apply_edge_inner_only`'s `Direct` arm.
    let mut borrow_mut_derivatives: BTreeMap<crate::ir::VarId, crate::ir::VarId> = BTreeMap::new();
    super::expr::collect_borrow_mut_derivatives(
        program,
        &func.body,
        &borrow_sources,
        &borrow_mut_origins,
        &mut borrow_mut_derivatives,
    );
    // Pre-pass: map value-form `&mut`-param mutating-native rebinds
    // (`let $t = table::add($t, ..)`) back to the borrowed Mutation
    // var they replace, regardless of whether that var is a
    // recognized container borrow source. Consumed only by the
    // `Expr::IsParent` child renderer to preserve the borrow path
    // via `Mutation.set` (otherwise `ofLocal` resets it and the
    // conditional writeback is silently dropped). See
    // `collect_mutref_rebind_sources`.
    let mut mutref_rebind_source: BTreeMap<crate::ir::VarId, crate::ir::VarId> = BTreeMap::new();
    super::expr::collect_mutref_rebind_sources(program, &func.body, &mut mutref_rebind_source);
    // Pre-pass: find let-bound `BorrowLoc(x)` temps whose every use
    // is `ReadRef(Var(v))`. The renderer drops the wrap and emits
    // bare `x` at each use; eliminates the `Mutation.ofLocal AnyKey ...`
    // round-trip that would otherwise auto-bind `__MutKey` on a
    // function whose signature has no Mutation (the Ascii /
    // MoveOption.destroy_some case).
    // The redundant_borrowloc peephole drops `let v := BorrowLoc(x)`
    // and redirects every `Var(v)` use to `Var(x)`. Only safe in
    // LEMMA packages where the file-scoped `variable {__MutKey : Type}`
    // makes the dropped Mutation wrap problematic for auto-bound
    // implicit synthesis. In USER packages the concrete `AnyKey`
    // inductive in `Generated/AnyKey.lean` removes that problem,
    // and the renderer's Mutation flow has complex interactions
    // (Sui-object wrappers, container natives, etc.) that the
    // peephole can break. Gate the pre-pass on `in_lemma_package`
    // so user packages render unchanged.
    let in_lemma_package_for_peephole = program
        .modules
        .get(&func.module)
        .map(|m| escape::is_lemma_package(&m.package_name))
        .unwrap_or(false);
    let sig_has_mutation_for_peephole = func
        .signature
        .params
        .iter()
        .any(|p| ty_contains_mutable_ref(&p.ty))
        || ty_contains_mutable_ref(&func.signature.return_type);
    let mut redundant_borrowloc: BTreeMap<crate::ir::VarId, crate::ir::VarId> = BTreeMap::new();
    // Only run the peephole when the function lives in a lemma
    // package AND its signature exposes no Mutation. This is the
    // narrow case where `__MutKey` auto-binds purely from body
    // references (and downstream callers fail with
    // "don't know how to synthesize implicit argument __MutKey").
    // In all other configurations the peephole is either unnecessary
    // (user packages have concrete AnyKey, no auto-bind issue) or
    // unsafe (a lemma function returning a Mutation needs the
    // wrap to flow through to its caller).
    if in_lemma_package_for_peephole && !sig_has_mutation_for_peephole {
        super::expr::collect_redundant_borrowloc(program, &func.body, &mut redundant_borrowloc);
    }
    let var_target_types =
        super::expr::compute_var_target_types(&func.body, &func.signature.return_type);
    let is_aborts = crate::ir::names::is_aborts_name(&func.name);
    // Name of the lifecycle `World` param (if any), forwarded by
    // `BlockTail::Abort` tails so an aborting branch preserves df/world
    // state instead of synthesizing an empty `default` World. Stage 7 may
    // also carry non-lifecycle World snapshots; selection is semantic rather
    // than positional.
    let world_param: Option<String> = program
        .struct_id_by_qualified_name(crate::stage_04_effects::WORLD_QUALIFIED_NAME)
        .and_then(|world_id| {
            crate::stage_04_effects::common::function_lifecycle_world_position(func, world_id)
        })
        .and_then(|index| pnames.get(index).cloned());
    let ctx = ExprCtx {
        render_context: context,
        program,
        current_module,
        type_params: Some(&tp_names),
        function_return_type: Some(&func.signature.return_type),
        world_param,
        var_overrides: &var_overrides,
        var_types: std::cell::RefCell::new(var_types),
        borrow_sources,
        borrow_mut_origins,
        borrow_mut_derivatives,
        mutref_rebind_source,
        is_aborts,
        redundant_borrowloc,
        var_target_types,
        mutation_users: context.mutation_users(),
        world_type_overrides: &world_type_overrides,
        caller_is_lemma_pkg: pkg_is_lemma,
        // True iff THIS caller actually emitted a `{__TyU}` binder above
        // (line ~1111: `lemma_tycode_universe || df_universe ||
        // tycode_concrete_universe`). A caller that binds `{__TyU}` purely
        // for a df-store reason (`df_universe`) -- e.g.
        // `derived_object::claim` / `exists_` and their `.aborts`
        // companions -- must still forward `(__TyU := __TyU)` to a
        // universe-binding callee like the #23 type-aware `derive_address`
        // (which has no world arg, so `{__TyU}` is otherwise uninferable).
        // The previous `lemma_tycode_universe`-only value under-reported
        // those df-universe callers, leaving Lean's `__TyU` stuck.
        caller_has_tycode_universe: lemma_tycode_universe
            || df_universe
            || tycode_concrete_universe,
        caller_module_has_bag_struct: module_imports_bagu_interp,
        current_fn_id: fid,
    };

    // Stub bodies (`stmts=[], tail=Value(Unit)`) come from the
    // pipeline driver when a function is registered but never has its
    // body populated.
    let body = &func.body;
    // Set once the real (non-stub, non-sorry-fallback) body renders, so
    // the conjunct-projection pass only fires on a companion whose body
    // is actually the conjunction it claims to be.
    let mut body_rendered_ok = false;
    let body_is_empty = body.stmts.is_empty()
        && matches!(
            &body.tail,
            crate::ir::BlockTail::Value(crate::ir::Expr::Unit)
        );
    if as_proof_stub {
        // Durable proof obligation: leave the proof to the human. The
        // `by sorry` typechecks against the named prop and is the seed
        // a human replaces with a real tactic proof. A trusted
        // obligation (`axiom`) has no proof body at all.
        if !is_axiom {
            w.write("by sorry");
        }
    } else if is_theorem {
        // The Bool body IS the statement; render it as the Prop value
        // of the `def … : Prop :=` opened above. Datatype invariants are
        // carried explicitly by the spec's own requires/ensures clauses
        // (native predicates), so the statement needs no injected
        // hypotheses here.
        let crate::ir::BlockTail::Value(e) = &body.tail else {
            return Err(RenderError::MalformedTheoremBody {
                module: current_module.unwrap_or("<unknown-module>").to_string(),
                function: func.name.clone(),
                tail: block_tail_name(&body.tail),
            });
        };
        let stmt = super::expr::render_theorem_statement(e, &ctx)?;
        w.write(&stmt);
    } else if body_is_empty {
        emit_fixpoint = false;
        total_entry = None;
        if matches!(&func.signature.return_type, Type::Unit) {
            w.write("()");
        } else {
            w.write("sorry");
        }
    } else {
        // Render the body into a side buffer first. On unsupported
        // construct (quantifier, while, break/continue/non-tail
        // return, etc.) fall back to `sorry` so the rest of the
        // module still emits. The side-buffer pattern avoids
        // partial-rendering artifacts when the failure happens
        // mid-statement.
        // Abort bodies benefit from inlining let-bound match scrutinees, then
        // collapsing any exposed TAIL-recursive abort-propagation match into
        // its bare recursive `.aborts` call (moving the recursion out of the
        // non-monotone match-scrutinee position -- see
        // `collapse_tail_recursive_aborts_match`), then normalizing the
        // remaining result-match shapes. This removes generated
        // `match (if check then Aborted code else NoAbort)` propagation chains
        // before Lean sees them. Transform a clone so the IR the rest of the
        // pipeline holds is untouched.
        let mut normalized_body;
        let body: &crate::ir::Block = if func.name.contains(".aborts") || emit_fixpoint {
            normalized_body = body.clone();
            if !func.name.contains(".aborts") {
                select_let_bound_match_values(
                    &mut normalized_body,
                    func.module,
                    &func.name,
                    program,
                );
                &normalized_body
            } else {
                inline_aborts_match_scrutinees(&mut normalized_body, program);
                collapse_tail_recursive_aborts_match(&mut normalized_body, program);
                normalize_aborts_result_matches(&mut normalized_body, program);
                inline_generated_abort_temporaries(&mut normalized_body);
                for _ in 0..8 {
                    let changed = crate::stage_06_let_inline::copy_inline::copy_inline_once(
                        &mut normalized_body,
                    )
                        || crate::stage_06_let_inline::single_use::single_use_inline_once(
                            &mut normalized_body,
                            program,
                        );
                    if !changed {
                        break;
                    }
                }
                if emit_fixpoint {
                    select_let_bound_match_values(
                        &mut normalized_body,
                        func.module,
                        &func.name,
                        program,
                    );
                }
                &normalized_body
            }
        } else {
            body
        };
        let mut side = LeanWriter::new(String::new());
        match render_function_body(body, &ctx, &mut side) {
            Ok(()) => {
                let rendered = side.into_inner();
                w.write(&rendered);
                body_rendered_ok = true;
            }
            Err(err @ RenderError::UnthreadedGlobal { .. }) => {
                // Global nodes are not an ordinary unsupported surface that
                // can be quarantined behind a `sorry`.  Reaching one means
                // `thread_globals` was skipped, and accepting the fallback
                // would erase a real global-state read or update.
                return Err(err);
            }
            Err(err) => {
                // A `sorry` fallback body is non-recursive, so `partial_fixpoint`
                // (which requires the recursive call) would fail to elaborate;
                // a plain `def … := sorry` is well-formed instead. Same reason
                // a total `def … termination_by` can't apply to it.
                emit_fixpoint = false;
                total_entry = None;
                w.write("sorry  -- render fallback: ");
                w.write(&format!("{:?}", err));
            }
        }
    }
    w.dedent(false);
    if emit_fixpoint {
        // Trailing `partial_fixpoint` clause (column 0, after the body).
        w.newline();
        w.write("partial_fixpoint");
    } else if let Some(entry) = &total_entry {
        // Trailing total-`def` termination clauses (column 0, after the
        // body): the human-supplied measure + decreasing proof, spliced
        // verbatim. The `decreasing_by` tactic runs in a context that
        // already carries the loop's guard hypotheses.
        w.newline();
        w.write("termination_by ");
        w.write(entry.measure.trim());
        w.newline();
        w.write("decreasing_by");
        w.newline();
        w.write("  ");
        // Indent each continuation line of a multi-line tactic by two
        // spaces so the block sits under `decreasing_by`.
        let tac = entry.decreasing.trim();
        let mut first = true;
        for line in tac.lines() {
            if first {
                w.write(line);
                first = false;
            } else {
                w.newline();
                w.write("  ");
                w.write(line);
            }
        }
    }
    w.newline();
    w.newline();
    // Additive conjunct projections: named `.c<k>` leaf defs + a `_conj`
    // characterization theorem for a `.asserts`/`.ensures`/`.requires`
    // companion whose body is a top-level `&&` tree. Gated to the
    // standalone (non-mutual, non-proof-stub) render path, since a
    // `theorem` cannot sit inside a `mutual … end` block; spec
    // companions are non-recursive and never land in one, and the
    // `force_partial`/`force_fixpoint` guard is belt-and-suspenders. The
    // helper self-gates on kind/shape and emits nothing off-pattern.
    if body_rendered_ok && !as_proof_stub && !force_partial && !force_fixpoint {
        super::conjunct_projection::emit_conjunct_projections(
            func, &ctx, &sig, &tp_names, &pnames, w,
        )?;
    }
    Ok(())
}

fn block_tail_name(tail: &crate::ir::BlockTail) -> &'static str {
    match tail {
        crate::ir::BlockTail::Value(_) => "value",
        crate::ir::BlockTail::Return(_) => "return",
        crate::ir::BlockTail::ReturnFromBlock { .. } => "return_from_block",
        crate::ir::BlockTail::Break { .. } => "break",
        crate::ir::BlockTail::Continue { .. } => "continue",
        crate::ir::BlockTail::Abort { .. } => "abort",
    }
}

fn is_trivial_total_aborts_companion(func: &Function, program: &Program) -> bool {
    if !crate::ir::names::is_aborts_name(&func.name) || !func.body.stmts.is_empty() {
        return false;
    }
    match &func.body.tail {
        crate::ir::BlockTail::Value(crate::ir::Expr::Const(crate::ir::Const::Bool(false))) => true,
        crate::ir::BlockTail::Value(e) => is_no_abort_pack(e, program),
        _ => false,
    }
}

fn is_no_abort_pack(e: &crate::ir::Expr, program: &Program) -> bool {
    matches!(
        e,
        crate::ir::Expr::Pack {
            struct_id,
            variant: Some(crate::stage_07_dejumps::option_aborts::OPTION_NONE_TAG),
            fields,
            ..
        } if fields.is_empty() && is_abort_result_struct(*struct_id, program)
    )
}

fn is_abort_result_struct(struct_id: crate::ir::StructId, program: &Program) -> bool {
    program.structs.get(&struct_id).is_some_and(|s| {
        s.qualified_name == crate::stage_07_dejumps::option_aborts::OPTION_QUALIFIED_NAME
    })
}

/// True iff `ty` mentions `Type::MutableRef` anywhere in its structure.
/// Used to gate the lemma-package redundant-`BorrowLoc` peephole.
fn ty_contains_mutable_ref(ty: &Type) -> bool {
    match ty {
        Type::MutableRef { .. } => true,
        Type::Tuple(ts) => ts.iter().any(ty_contains_mutable_ref),
        Type::Vector(inner) | Type::Reference(inner) => ty_contains_mutable_ref(inner),
        Type::Struct { type_args, .. } => type_args.iter().any(ty_contains_mutable_ref),
        Type::Unit
        | Type::Bool
        | Type::Prop
        | Type::UInt(_)
        | Type::Address
        | Type::TypeParam(_) => false,
    }
}

/// Emit the renderer-owned executable model for
/// `Sui::test_scenario::end_transaction`.
pub fn render_end_transaction_model<W: Write>(
    decl: &NativeDecl,
    program: &Program,
    current_module: Option<&str>,
    w: &mut LeanWriter<W>,
) -> RenderResult<()> {
    let is_end_transaction =
        super::native_models::is_renderer_owned_end_transaction_model(decl, program);
    if !is_end_transaction {
        return Err(RenderError::NativeModelPolicy {
            what: format!(
                "no renderer-owned native model for declaration `{}`",
                decl.name
            ),
        });
    }
    let escaped_name = escape::escape_identifier(&decl.name);

    w.write("def ");
    w.write(&escaped_name);

    let tp_names: Vec<String> = decl.signature.type_params.clone();
    for tp in &tp_names {
        let tp_esc = escape::escape_identifier(tp);
        w.write(&format!(
            " ({} : Type) [DecidableEq {}] [Inhabited {}]",
            tp_esc, tp_esc, tp_esc
        ));
    }

    let mut seen: std::collections::BTreeSet<String> = std::collections::BTreeSet::new();
    for p in &decl.signature.params {
        let base = if p.name.is_empty() {
            "_arg".to_string()
        } else {
            escape::escape_identifier(&p.name)
        };
        // Prefix with `_` so Lean doesn't warn about an unused binder.
        let mut pname = format!("_{}", base.trim_start_matches('_'));
        let mut i: usize = 2;
        while !seen.insert(pname.clone()) {
            pname = format!("_{}_{}", base.trim_start_matches('_'), i);
            i += 1;
        }
        let tystr = ty::type_to_string(&p.ty, program, current_module, Some(&tp_names));
        w.write(" (");
        w.write(&pname);
        w.write(" : ");
        w.write(&tystr);
        w.write(")");
    }

    w.write(" : ");
    let ret_str = ty::type_to_string(
        &decl.signature.return_type,
        program,
        current_module,
        Some(&tp_names),
    );
    w.write(&ret_str);
    // This model is emitted here rather than in the natives sibling because
    // its return type `(TransactionEffects, World)` references the
    // Move-defined `TransactionEffects` struct, which is emitted in
    // THIS file just above (the sibling is imported before it). Give
    // it a real body so `num_user_events()` reflects the count of
    // `event::emit` calls in the concluded transaction: read the
    // world's per-tx user-event counter into the effects, then reset
    // it (Sui reports per-transaction counts). Likewise fill
    // `created` from the world's per-tx committed-object list
    // (appended by `transfer_to` / `share` / `freeze`), mapping each
    // `Nat` id back to an `Object.ID` via `Test_scenario.idFromNat`,
    // then reset that list too.
    w.write(
        " :=
  (({ (default : TransactionEffects) with num_user_events := (Prover.World.World.user_event_count _world), created := ((Prover.World.World.created_ids _world).map idFromNat) }), (Prover.World.World.reset_created (Prover.World.World.reset_user_events _world)))",
    );
    w.newline();
    w.newline();
    Ok(())
}

/// Walk a Block's body looking for a `Expr::Call { fun }` whose
/// resolved function (by `program.functions` lookup) has the same
/// `(module, name)` as the caller. Used by `render_function` to gate
/// the `partial def` emission for source-level self-recursion --
/// `scc_needs_mutual_block`'s walker filters self-edges out so the
/// mutual-block wrapper doesn't fire on these, but the `def` body
/// would then fail Lean's structural-termination check.
pub(crate) fn body_calls_self_by_name(
    body: &crate::ir::Block,
    own_module: &crate::ir::ModId,
    own_name: &str,
    program: &Program,
) -> bool {
    walk_block_for_self_call(body, own_module, own_name, program)
}

/// Whether a directly self-recursive SOURCE function, or the `.aborts`
/// companion of one, recurses only in tail position once rendered. Any other
/// function kind answers `true`: this gate is not about it.
///
/// Value face (deepbook `fixed_math::math::ln`: `ln(inv).neg()` consumes its
/// own result): checked on the body as it stands. Abort face (deepbook
/// `strike_payout_tree::take_min`, whose `.aborts` has no `.cont_N` fragment
/// and is therefore a lone self-recursive function rather than a mutual
/// block): the recursive call starts in a propagation `match` scrutinee, so
/// the check runs after the same normalization `render_function` applies,
/// which moves it to tail position exactly when the step after the recursion
/// cannot abort. Lean rejects every other shape with "Could not prove ... to
/// be monotone in its recursive calls".
fn source_self_recursion_is_tail_position(func: &crate::ir::Function, program: &Program) -> bool {
    use crate::ir::{FunctionKind, SpecKind};
    match func.kind {
        FunctionKind::Source => {
            self_calls_only_in_tail_position(&func.body, &func.module, &func.name, program)
        }
        FunctionKind::Spec {
            kind: SpecKind::Aborts,
            target,
        } if matches!(
            program.functions.get(&target).map(|f| &f.kind),
            Some(FunctionKind::Source)
        ) =>
        {
            let mut body = func.body.clone();
            inline_aborts_match_scrutinees(&mut body, program);
            collapse_tail_recursive_aborts_match(&mut body, program);
            normalize_aborts_result_matches(&mut body, program);
            self_calls_only_in_tail_position(&body, &func.module, &func.name, program)
        }
        _ => true,
    }
}

/// True iff every self-call in `body` is the whole value of a tail position:
/// the block tail itself, reached only through `if` / `match` arms. A self-call
/// in a statement, a condition, a scrutinee or an argument is not. A block
/// ending `let x := e; x` is `e` in tail position: lowering names every
/// intermediate, so priority_queue `max_heapify_recursive` reaches its
/// recursion as `let t := if c then (let r := <rec>; r) else v; (t)`. A
/// one-element tuple renders as its element, so it is looked through too.
pub(crate) fn self_calls_only_in_tail_position(
    body: &crate::ir::Block,
    own_module: &crate::ir::ModId,
    own_name: &str,
    program: &Program,
) -> bool {
    use crate::ir::{Block, BlockTail, Expr, Stmt};
    fn singleton_element(e: &Expr) -> &Expr {
        match e {
            Expr::Tuple(items) if items.len() == 1 => singleton_element(&items[0]),
            other => other,
        }
    }
    if let (Some((Stmt::Let { pattern, value }, earlier)), BlockTail::Value(tail)) =
        (body.stmts.split_last(), &body.tail)
    {
        if let Expr::Var(result) = singleton_element(tail) {
            if matches!(pattern.as_slice(), [Some(bound)] if bound == result) {
                let forwarded = Block {
                    stmts: earlier.to_vec(),
                    tail: BlockTail::Value(value.clone()),
                };
                return self_calls_only_in_tail_position(&forwarded, own_module, own_name, program);
            }
        }
    }
    let calls_self = |e: &Expr| walk_expr_for_self_call(e, own_module, own_name, program);
    for s in &body.stmts {
        let (Stmt::Let { value: e, .. } | Stmt::Eval(e)) = s;
        if calls_self(e) {
            return false;
        }
    }
    let tail: &Expr = match &body.tail {
        BlockTail::Value(e) => singleton_element(e),
        BlockTail::Return(e) => singleton_element(e),
        _ => return !walk_block_for_self_call(body, own_module, own_name, program),
    };
    match tail {
        Expr::If {
            cond,
            then_branch,
            else_branch,
        } => {
            !calls_self(cond)
                && self_calls_only_in_tail_position(then_branch, own_module, own_name, program)
                && self_calls_only_in_tail_position(else_branch, own_module, own_name, program)
        }
        Expr::Match {
            selector, cases, ..
        } => {
            !calls_self(selector)
                && cases.iter().all(|arm| {
                    self_calls_only_in_tail_position(&arm.body, own_module, own_name, program)
                })
        }
        Expr::Call { args, .. } => !args.iter().any(calls_self),
        other => !calls_self(other),
    }
}

fn walk_block_for_self_call(
    b: &crate::ir::Block,
    own_module: &crate::ir::ModId,
    own_name: &str,
    program: &Program,
) -> bool {
    use crate::ir::{BlockTail, Stmt};
    for s in &b.stmts {
        let hit = match s {
            Stmt::Let { value, .. } => {
                walk_expr_for_self_call(value, own_module, own_name, program)
            }
            Stmt::Eval(e) => walk_expr_for_self_call(e, own_module, own_name, program),
        };
        if hit {
            return true;
        }
    }
    match &b.tail {
        BlockTail::Value(e) => walk_expr_for_self_call(e, own_module, own_name, program),
        BlockTail::Return(e) | BlockTail::Abort { code: e } => {
            walk_expr_for_self_call(e.as_ref(), own_module, own_name, program)
        }
        BlockTail::Break { value, .. } | BlockTail::Continue { value, .. } => {
            walk_expr_for_self_call(value.as_ref(), own_module, own_name, program)
        }
        BlockTail::ReturnFromBlock { .. } => unreachable!(
            "BlockTail::ReturnFromBlock should be eliminated by stage 7 helper extraction"
        ),
    }
}

fn walk_expr_for_self_call(
    e: &crate::ir::Expr,
    own_module: &crate::ir::ModId,
    own_name: &str,
    program: &Program,
) -> bool {
    use crate::ir::{BitOp, Expr, QuantDomain};
    match e {
        Expr::Borrow { step, base } => {
            step.exprs()
                .any(|__pe| walk_expr_for_self_call(__pe, own_module, own_name, program))
                || walk_expr_for_self_call(base, own_module, own_name, program)
        }
        Expr::Update { step, base, value } => {
            step.exprs()
                .any(|__pe| walk_expr_for_self_call(__pe, own_module, own_name, program))
                || walk_expr_for_self_call(base, own_module, own_name, program)
                || walk_expr_for_self_call(value, own_module, own_name, program)
        }
        Expr::Var(_)
        | Expr::Const(_)
        | Expr::Unit
        | Expr::BorrowLoc(_)
        | Expr::BorrowGlobal(_)
        | Expr::WriteBack { .. }
        | Expr::IsParent { .. } => false,
        Expr::BinOp { lhs, rhs, .. } => {
            walk_expr_for_self_call(lhs, own_module, own_name, program)
                || walk_expr_for_self_call(rhs, own_module, own_name, program)
        }
        Expr::UnOp { operand, .. } => {
            walk_expr_for_self_call(operand, own_module, own_name, program)
        }
        Expr::BitOp(op) => match op {
            BitOp::Extract { operand, .. }
            | BitOp::ZeroExtend { operand, .. }
            | BitOp::SignExtend { operand, .. } => {
                walk_expr_for_self_call(operand, own_module, own_name, program)
            }
            BitOp::Concat { high, low } => {
                walk_expr_for_self_call(high, own_module, own_name, program)
                    || walk_expr_for_self_call(low, own_module, own_name, program)
            }
        },
        Expr::Call { fun, args, .. } => {
            if let Some(callee) = program.functions.get(fun) {
                if callee.module == *own_module && callee.name == own_name {
                    return true;
                }
            }
            args.iter()
                .any(|a| walk_expr_for_self_call(a, own_module, own_name, program))
        }
        Expr::Tuple(es) | Expr::Pack { fields: es, .. } => es
            .iter()
            .any(|x| walk_expr_for_self_call(x, own_module, own_name, program)),
        Expr::Unpack { value, .. }
        | Expr::Field { base: value, .. }
        | Expr::ReadRef(value)
        | Expr::ToProp(value)
        | Expr::ToBool(value) => walk_expr_for_self_call(value, own_module, own_name, program),
        Expr::If {
            cond,
            then_branch,
            else_branch,
        } => {
            walk_expr_for_self_call(cond, own_module, own_name, program)
                || walk_block_for_self_call(then_branch, own_module, own_name, program)
                || walk_block_for_self_call(else_branch, own_module, own_name, program)
        }
        Expr::Match {
            selector, cases, ..
        } => {
            walk_expr_for_self_call(selector, own_module, own_name, program)
                || cases
                    .iter()
                    .any(|c| walk_block_for_self_call(&c.body, own_module, own_name, program))
        }
        Expr::While {
            header,
            cond,
            body,
            iter_locals,
            header_exit_locals: _,
            live_out: _,
        } => {
            iter_locals
                .iter()
                .any(|(_, init)| walk_expr_for_self_call(init, own_module, own_name, program))
                || walk_block_for_self_call(header, own_module, own_name, program)
                || walk_expr_for_self_call(cond, own_module, own_name, program)
                || walk_block_for_self_call(body, own_module, own_name, program)
        }
        Expr::WriteRef { reference, value } => {
            walk_expr_for_self_call(reference, own_module, own_name, program)
                || walk_expr_for_self_call(value, own_module, own_name, program)
        }
        Expr::Quantifier { domain, body, .. } => {
            let d = match domain {
                QuantDomain::Unbounded => false,
                QuantDomain::Range { start, end } => {
                    walk_expr_for_self_call(start, own_module, own_name, program)
                        || walk_expr_for_self_call(end, own_module, own_name, program)
                }
                QuantDomain::VecRange { vec, start, end } => {
                    walk_expr_for_self_call(vec, own_module, own_name, program)
                        || walk_expr_for_self_call(start, own_module, own_name, program)
                        || walk_expr_for_self_call(end, own_module, own_name, program)
                }
                QuantDomain::Collection(c) => {
                    walk_expr_for_self_call(c, own_module, own_name, program)
                }
            };
            d || walk_block_for_self_call(body, own_module, own_name, program)
        }
        Expr::LabeledBlock { .. } => {
            unreachable!("Expr::LabeledBlock should be eliminated by stage 7 helper extraction")
        }
    }
}

fn abort_result_type_args_from_expr(
    e: &crate::ir::Expr,
    struct_id: crate::ir::StructId,
    program: &Program,
) -> Option<Vec<Type>> {
    use crate::ir::Expr;
    let from_shape = match e {
        Expr::Pack {
            struct_id: sid,
            type_args,
            ..
        } if *sid == struct_id => Some(type_args.clone()),
        Expr::If {
            then_branch,
            else_branch,
            ..
        } => abort_result_type_args_from_block(then_branch, struct_id, program)
            .or_else(|| abort_result_type_args_from_block(else_branch, struct_id, program)),
        Expr::Match { cases, .. } => cases
            .iter()
            .find_map(|arm| abort_result_type_args_from_block(&arm.body, struct_id, program)),
        Expr::Tuple(elems) => elems
            .iter()
            .find_map(|elem| abort_result_type_args_from_expr(elem, struct_id, program)),
        _ => None,
    };
    from_shape.or_else(|| match rendered_type_of(e, program, &BTreeMap::new())? {
        Type::Struct {
            struct_id: sid,
            type_args,
        } if sid == struct_id => Some(type_args),
        _ => None,
    })
}

fn abort_result_type_args_from_block(
    block: &crate::ir::Block,
    struct_id: crate::ir::StructId,
    program: &Program,
) -> Option<Vec<Type>> {
    match &block.tail {
        crate::ir::BlockTail::Value(e) => abort_result_type_args_from_expr(e, struct_id, program),
        crate::ir::BlockTail::Return(e) => {
            abort_result_type_args_from_expr(e.as_ref(), struct_id, program)
        }
        _ => None,
    }
}

fn block_returns_selector(
    block: &crate::ir::Block,
    selector: &crate::ir::Expr,
    selector_var: Option<&crate::ir::VarId>,
) -> bool {
    if !block.stmts.is_empty() {
        return false;
    }
    let e = match &block.tail {
        crate::ir::BlockTail::Value(e) => e,
        crate::ir::BlockTail::Return(e) => e.as_ref(),
        _ => return false,
    };
    if e == selector {
        return true;
    }
    matches!(
        (selector_var, e),
        (Some(v), crate::ir::Expr::Var(ev)) if ev == v
    )
}

fn expr_is_selector(
    e: &crate::ir::Expr,
    selector: &crate::ir::Expr,
    selector_var: Option<&crate::ir::VarId>,
) -> bool {
    e == selector
        || matches!(
            (selector_var, e),
            (Some(v), crate::ir::Expr::Var(ev)) if ev == v
        )
}

fn rewrite_selector_occurrences_in_aborted_arm(
    block: &mut crate::ir::Block,
    selector: &crate::ir::Expr,
    selector_var: Option<&crate::ir::VarId>,
    replacement: crate::ir::Expr,
) -> bool {
    if !block.stmts.is_empty() {
        return false;
    }

    struct Rewriter<'a> {
        selector: &'a crate::ir::Expr,
        selector_var: Option<&'a crate::ir::VarId>,
        replacement: crate::ir::Expr,
        changed: bool,
    }

    impl crate::ir::visit::MutVisitor for Rewriter<'_> {
        fn visit_expr_mut(&mut self, e: &mut crate::ir::Expr) {
            if expr_is_selector(e, self.selector, self.selector_var) {
                *e = self.replacement.clone();
                self.changed = true;
                return;
            }
            crate::ir::visit::walk_expr_mut_default(self, e);
        }
    }

    let mut rewriter = Rewriter {
        selector,
        selector_var,
        replacement,
        changed: false,
    };
    match &mut block.tail {
        crate::ir::BlockTail::Value(e) => {
            crate::ir::visit::MutVisitor::visit_expr_mut(&mut rewriter, e)
        }
        crate::ir::BlockTail::Return(e) => {
            crate::ir::visit::MutVisitor::visit_expr_mut(&mut rewriter, e.as_mut())
        }
        _ => return false,
    }
    rewriter.changed
}

fn rewrite_aborted_selector_return_arms(
    cases: &mut [crate::ir::MatchArm],
    struct_id: crate::ir::StructId,
    type_args: &[Type],
    selector: &crate::ir::Expr,
    selector_var: Option<&crate::ir::VarId>,
) {
    for arm in cases {
        if arm.variant != crate::stage_07_dejumps::option_aborts::OPTION_SOME_TAG
            || arm.bindings.len() != 1
        {
            continue;
        }
        let replacement = crate::ir::Expr::Pack {
            struct_id,
            type_args: type_args.to_vec(),
            variant: Some(crate::stage_07_dejumps::option_aborts::OPTION_SOME_TAG),
            fields: vec![crate::ir::Expr::Var(arm.bindings[0].clone())],
        };
        rewrite_selector_occurrences_in_aborted_arm(
            &mut arm.body,
            selector,
            selector_var,
            replacement,
        );
    }
}

fn block_returns_no_abort_after_ignored_evals(
    block: &crate::ir::Block,
    struct_id: crate::ir::StructId,
    type_args: &[Type],
) -> bool {
    let e = match &block.tail {
        crate::ir::BlockTail::Value(e) => e,
        crate::ir::BlockTail::Return(e) => e.as_ref(),
        _ => return false,
    };
    matches!(
        e,
        crate::ir::Expr::Pack {
            struct_id: sid,
            type_args: args,
            variant: Some(crate::stage_07_dejumps::option_aborts::OPTION_NONE_TAG),
            fields,
        } if *sid == struct_id && args == type_args && fields.is_empty()
    )
}

fn block_returns_no_abort_exact(
    block: &crate::ir::Block,
    struct_id: crate::ir::StructId,
    type_args: &[Type],
) -> bool {
    block.stmts.is_empty()
        && block_returns_no_abort_after_ignored_evals(block, struct_id, type_args)
}

fn block_returns_aborted_exact(
    block: &crate::ir::Block,
    struct_id: crate::ir::StructId,
    type_args: &[Type],
) -> bool {
    if !block.stmts.is_empty() {
        return false;
    }
    let e = match &block.tail {
        crate::ir::BlockTail::Value(e) => e,
        crate::ir::BlockTail::Return(e) => e.as_ref(),
        _ => return false,
    };
    matches!(
        e,
        crate::ir::Expr::Pack {
            struct_id: sid,
            type_args: args,
            variant: Some(crate::stage_07_dejumps::option_aborts::OPTION_SOME_TAG),
            fields,
        } if *sid == struct_id && args == type_args && fields.len() == 1
    )
}

fn block_returns_aborted_binding(
    block: &crate::ir::Block,
    struct_id: crate::ir::StructId,
    type_args: &[Type],
    binding: &crate::ir::VarId,
) -> bool {
    if !block.stmts.is_empty() {
        return false;
    }
    let e = match &block.tail {
        crate::ir::BlockTail::Value(e) => e,
        crate::ir::BlockTail::Return(e) => e.as_ref(),
        _ => return false,
    };
    matches!(
        e,
        crate::ir::Expr::Pack {
            struct_id: sid,
            type_args: args,
            variant: Some(crate::stage_07_dejumps::option_aborts::OPTION_SOME_TAG),
            fields,
        } if *sid == struct_id
            && args == type_args
            && matches!(fields.as_slice(), [crate::ir::Expr::Var(v)] if v == binding)
    )
}

fn abort_result_match_is_identity(
    cases: &[crate::ir::MatchArm],
    struct_id: crate::ir::StructId,
    type_args: &[Type],
) -> bool {
    if cases.len() != 2 {
        return false;
    }
    let mut saw_no_abort = false;
    let mut saw_aborted = false;
    for arm in cases {
        match arm.variant {
            crate::stage_07_dejumps::option_aborts::OPTION_NONE_TAG => {
                if !arm.bindings.is_empty()
                    || !block_returns_no_abort_after_ignored_evals(&arm.body, struct_id, type_args)
                {
                    return false;
                }
                saw_no_abort = true;
            }
            crate::stage_07_dejumps::option_aborts::OPTION_SOME_TAG => {
                let [binding] = arm.bindings.as_slice() else {
                    return false;
                };
                if !block_returns_aborted_binding(&arm.body, struct_id, type_args, binding) {
                    return false;
                }
                saw_aborted = true;
            }
            _ => return false,
        }
    }
    saw_no_abort && saw_aborted
}

fn abort_result_match_on_abort_if(
    struct_id: crate::ir::StructId,
    type_args: &[Type],
    selector: &crate::ir::Expr,
    cases: &[crate::ir::MatchArm],
) -> Option<crate::ir::Expr> {
    let crate::ir::Expr::If {
        cond,
        then_branch,
        else_branch,
    } = selector
    else {
        return None;
    };
    if !block_returns_aborted_exact(then_branch, struct_id, type_args)
        || !block_returns_no_abort_exact(else_branch, struct_id, type_args)
    {
        return None;
    }
    if cases.len() != 2 {
        return None;
    }
    let no_abort_arm = cases.iter().find(|arm| {
        arm.variant == crate::stage_07_dejumps::option_aborts::OPTION_NONE_TAG
            && arm.bindings.is_empty()
    })?;
    let aborted_arm = cases
        .iter()
        .find(|arm| arm.variant == crate::stage_07_dejumps::option_aborts::OPTION_SOME_TAG)?;
    let [binding] = aborted_arm.bindings.as_slice() else {
        return None;
    };
    if !block_returns_selector(&aborted_arm.body, selector, None)
        && !block_returns_aborted_binding(&aborted_arm.body, struct_id, type_args, binding)
    {
        return None;
    }
    Some(crate::ir::Expr::If {
        cond: cond.clone(),
        then_branch: then_branch.clone(),
        else_branch: no_abort_arm.body.clone(),
    })
}

/// In abort-result matches, replace an aborted arm that returns the whole
/// selector with one that reconstructs the matched constructor:
/// `| Aborted code => Aborted code`.
pub(crate) fn normalize_aborts_result_matches(body: &mut crate::ir::Block, program: &Program) {
    struct Normalizer<'a> {
        program: &'a Program,
    }
    impl crate::ir::visit::MutVisitor for Normalizer<'_> {
        fn visit_expr_mut(&mut self, e: &mut crate::ir::Expr) {
            crate::ir::visit::walk_expr_mut_default(self, e);
            let crate::ir::Expr::Match {
                struct_id,
                selector,
                cases,
            } = e
            else {
                return;
            };
            if !is_abort_result_struct(*struct_id, self.program) {
                return;
            }
            let Some(type_args) =
                abort_result_type_args_from_expr(selector.as_ref(), *struct_id, self.program)
                    .or_else(|| {
                        cases.iter().find_map(|arm| {
                            abort_result_type_args_from_block(&arm.body, *struct_id, self.program)
                        })
                    })
            else {
                return;
            };
            let selector_var = match selector.as_ref() {
                crate::ir::Expr::Var(v) => Some(v.clone()),
                _ => None,
            };
            rewrite_aborted_selector_return_arms(
                cases,
                *struct_id,
                &type_args,
                selector.as_ref(),
                selector_var.as_ref(),
            );
            if let Some(rewritten) =
                abort_result_match_on_abort_if(*struct_id, &type_args, selector.as_ref(), cases)
            {
                *e = rewritten;
                return;
            }
            if abort_result_match_is_identity(cases, *struct_id, &type_args) {
                *e = selector.as_ref().clone();
            }
        }
    }
    crate::ir::visit::MutVisitor::visit_block_mut(&mut Normalizer { program }, body);
}

/// Select a let-bound `match` scrutinee by its VALUE, for a body emitted with
/// `partial_fixpoint`.
///
/// `partial_fixpoint`'s monotonicity prover splits every `match` on the path
/// to a recursive call, and fails on a scrutinee that is a `let`-bound local
/// ("Dependent elimination failed: Failed to solve equation
/// `x = MpcSig.Pending _`") -- the local unfolds to its definition. hashi's
/// `mpc_signing::to_signatures` loop matches on `let s := vector::borrow(..)`
/// and recurses in the `Signed` arm, so both its value and `.aborts` loops
/// were rejected. Matching on the bound expression itself is accepted (the
/// same fix `inline_aborts_match_scrutinees` makes for abort-result matches);
/// the `let` stays for any later use of the local, so nothing is lost to
/// proofs. A value containing a recursive self-call is left alone: moving
/// recursion into the scrutinee is exactly what the prover cannot handle.
pub(crate) fn select_let_bound_match_values(
    body: &mut crate::ir::Block,
    module: crate::ir::ModId,
    name: &str,
    program: &Program,
) {
    struct Selector<'a> {
        module: crate::ir::ModId,
        name: &'a str,
        program: &'a Program,
    }
    impl crate::ir::visit::MutVisitor for Selector<'_> {
        fn visit_block_mut(&mut self, b: &mut crate::ir::Block) {
            use crate::ir::{BlockTail, Expr, Stmt};
            crate::ir::visit::walk_block_mut_default(self, b);
            let BlockTail::Value(Expr::Match { selector, .. }) = &b.tail else {
                return;
            };
            let Expr::Var(v) = selector.as_ref() else {
                return;
            };
            let Some(value) = b.stmts.iter().rev().find_map(|s| match s {
                Stmt::Let { pattern, value }
                    if pattern.len() == 1 && pattern[0].as_ref() == Some(v) =>
                {
                    Some(value.clone())
                }
                _ => None,
            }) else {
                return;
            };
            let probe = crate::ir::Block::just(value.clone());
            if body_calls_self_by_name(&probe, &self.module, self.name, self.program) {
                return;
            }
            if let BlockTail::Value(Expr::Match { selector, .. }) = &mut b.tail {
                **selector = value;
            }
        }
    }
    crate::ir::visit::MutVisitor::visit_block_mut(
        &mut Selector {
            module,
            name,
            program,
        },
        body,
    );
}

/// Inline a `match`'s let-bound scrutinee into the match itself, for an
/// `.aborts.while_N` loop body about to be emitted with `partial_fixpoint`.
///
/// Abort companions propagate aborts with the shape
/// `let c := <abort-check>; match c { NoAbort => <rec ...> | Aborted _ => c }`.
/// `partial_fixpoint`'s monotonicity prover chokes on a `match` whose
/// scrutinee is a `let`-bound variable (dependent elimination fails to
/// solve `c = Aborted ..`). Inlining the scrutinee binding -- the
/// abort-check value, which is pure in an abort companion (an `if`-on-bool
/// over `AbortResult` constructors, or a total `.aborts` call) -- moves the
/// recursive call entirely into the `NoAbort` arm, leaving the selector
/// recursion-free, which IS monotone (confirmed: a `let`-bound selector
/// fails, the inlined form succeeds).
///
/// Scoped to abort-loop bodies (the only place a `match` on `AbortResult`
/// co-occurs with a recursive call); value loops carry no abort match, so
/// they never hit this path.
pub(crate) fn inline_aborts_match_scrutinees(body: &mut crate::ir::Block, program: &Program) {
    struct Inliner<'a> {
        program: &'a Program,
    }
    impl crate::ir::visit::MutVisitor for Inliner<'_> {
        fn visit_block_mut(&mut self, b: &mut crate::ir::Block) {
            use crate::ir::{BlockTail, Expr, Stmt};
            // Rewrite children first, then this block's tail match.
            crate::ir::visit::walk_block_mut_default(self, b);
            let BlockTail::Value(Expr::Match {
                struct_id,
                selector,
                ..
            }) = &b.tail
            else {
                return;
            };
            let struct_id = *struct_id;
            if !is_abort_result_struct(struct_id, self.program) {
                return;
            }
            let Expr::Var(v) = selector.as_ref() else {
                return;
            };
            let v = v.clone();
            let Some(idx) = b.stmts.iter().rposition(|s| {
                matches!(s, Stmt::Let { pattern, .. }
                    if pattern.len() == 1 && pattern[0].as_ref() == Some(&v))
            }) else {
                return;
            };
            let Stmt::Let { value, .. } = &b.stmts[idx] else {
                unreachable!()
            };
            let value = value.clone();
            if let Some(type_args) =
                abort_result_type_args_from_expr(&value, struct_id, self.program)
            {
                if let BlockTail::Value(Expr::Match {
                    selector, cases, ..
                }) = &mut b.tail
                {
                    rewrite_aborted_selector_return_arms(
                        cases,
                        struct_id,
                        &type_args,
                        selector.as_ref(),
                        Some(&v),
                    );
                }
            }
            b.stmts.remove(idx);
            crate::stage_06_let_inline::substitute::substitute_var_in_tail(&mut b.tail, &v, &value);
        }
    }
    crate::ir::visit::MutVisitor::visit_block_mut(&mut Inliner { program }, body);
}

/// Collapse a TAIL-recursive abort-propagation `match` into its bare
/// recursive `.aborts` call, exposing a monotone (tail-position) recursion
/// that `partial_fixpoint` accepts.
///
/// A Move source function that recurses in TAIL position (e.g.
/// `sui::priority_queue::max_heapify_recursive`) renders its abort face
/// with the abort-propagation shape
///
/// ```text
/// match <self.aborts recursive call> with
///   | NoAbort   => let _ := <value recursive call>; (<cont> ...)   -- <cont> ≡ NoAbort
///   | Aborted e => Aborted e
/// ```
///
/// where the post-recursion continuation `<cont>` (a stage-7 `.cont_*`
/// helper) is trivially `NoAbort` -- nothing aborts after the tail call.
/// That `match` is pointwise EQUAL to its own scrutinee (`X` aborts iff `X`
/// aborts, and the NoAbort arm never aborts), so replacing it with the bare
/// scrutinee is a sound re-encoding of the abort semantics. The payoff:
/// `partial_fixpoint`'s monotonicity prover rejects a recursive call in a
/// `match` SCRUTINEE ("Cannot eliminate recursive call ... enclosed in
/// match ..."), but accepts it in tail position -- so this collapse is what
/// makes the source-recursive abort SCC `partial_fixpoint`-eligible (see
/// `scc_is_fixpoint_eligible`), giving downstream proofs a real
/// `.eq_def`/`.fixpoint_induct` instead of an opaque `partial def`.
///
/// Runs AFTER [`inline_aborts_match_scrutinees`], which turns the let-bound
/// scrutinee (`let __c := <rec .aborts>; match __c`) into a direct call and
/// canonicalizes the `Aborted` arm to `Aborted e => Aborted e`.
///
/// NARROWLY GATED to that tail shape. The collapse fires only when
///   (a) the selector is a direct `Call` to a `Spec::Aborts` companion whose
///       target SOURCE function is itself self-recursive
///       (`body_calls_self_by_name`), and
///   (b) the NoAbort arm provably reduces to `NoAbort` (discard the leading
///       lets, then follow the `.cont_*` tail-call chain to a `NoAbort`).
/// A LOOP's abort companion is excluded: its NoAbort arm recurses back into
/// the loop helper, which does NOT reduce to `NoAbort` (real post-call
/// work), so (b) fails. NON-tail source recursion is excluded for the same
/// reason -- its NoAbort arm still runs abort checks after the recursive
/// call. Both keep their opaque `partial def`.
pub(crate) fn collapse_tail_recursive_aborts_match(body: &mut crate::ir::Block, program: &Program) {
    struct Collapser<'a> {
        program: &'a Program,
    }
    impl crate::ir::visit::MutVisitor for Collapser<'_> {
        fn visit_expr_mut(&mut self, e: &mut crate::ir::Expr) {
            crate::ir::visit::walk_expr_mut_default(self, e);
            let crate::ir::Expr::Match {
                struct_id,
                selector,
                cases,
            } = e
            else {
                return;
            };
            if !is_abort_result_struct(*struct_id, self.program) {
                return;
            }
            if !selector_is_self_recursive_source_aborts_call(selector.as_ref(), self.program) {
                return;
            }
            let Some(type_args) =
                abort_result_type_args_from_expr(selector.as_ref(), *struct_id, self.program)
            else {
                return;
            };
            if !aborts_match_is_tail_identity(cases, *struct_id, &type_args, self.program) {
                return;
            }
            *e = selector.as_ref().clone();
        }
    }
    crate::ir::visit::MutVisitor::visit_block_mut(&mut Collapser { program }, body);
}

/// True iff `sel` is a direct `Call` to the `.aborts` companion of a
/// SELF-RECURSIVE Move source function -- i.e. the recursive abort call
/// whose enclosing propagation `match` [`collapse_tail_recursive_aborts_match`]
/// may collapse. The abort companion of a LOOP helper is a `Spec::Aborts`
/// whose target is a `LoopBody`/`LoopAfter` (not a self-recursive source),
/// so it is correctly excluded here.
fn selector_is_self_recursive_source_aborts_call(sel: &crate::ir::Expr, program: &Program) -> bool {
    let crate::ir::Expr::Call { fun, .. } = sel else {
        return false;
    };
    let Some(f) = program.functions.get(fun) else {
        return false;
    };
    let crate::ir::FunctionKind::Spec {
        kind: crate::ir::SpecKind::Aborts,
        target,
    } = &f.kind
    else {
        return false;
    };
    let Some(t) = program.functions.get(target) else {
        return false;
    };
    body_calls_self_by_name(&t.body, &t.module, &t.name, program)
}

/// The identity abort-propagation shape whose NoAbort arm is trivially
/// abort-free: `| NoAbort => <reduces to NoAbort> | Aborted e => Aborted e`.
/// Unlike [`abort_result_match_is_identity`], the NoAbort arm may TAIL-CALL
/// a continuation helper that is itself `NoAbort` (the `.cont_*` chain),
/// not just return `NoAbort` directly.
fn aborts_match_is_tail_identity(
    cases: &[crate::ir::MatchArm],
    struct_id: crate::ir::StructId,
    type_args: &[Type],
    program: &Program,
) -> bool {
    if cases.len() != 2 {
        return false;
    }
    let mut saw_no_abort = false;
    let mut saw_aborted = false;
    for arm in cases {
        match arm.variant {
            crate::stage_07_dejumps::option_aborts::OPTION_NONE_TAG => {
                if !arm.bindings.is_empty() {
                    return false;
                }
                let mut visited = std::collections::BTreeSet::new();
                if !block_reduces_to_no_abort(
                    &arm.body,
                    struct_id,
                    type_args,
                    program,
                    &mut visited,
                ) {
                    return false;
                }
                saw_no_abort = true;
            }
            crate::stage_07_dejumps::option_aborts::OPTION_SOME_TAG => {
                let [binding] = arm.bindings.as_slice() else {
                    return false;
                };
                if !block_returns_aborted_binding(&arm.body, struct_id, type_args, binding) {
                    return false;
                }
                saw_aborted = true;
            }
            _ => return false,
        }
    }
    saw_no_abort && saw_aborted
}

/// True iff `block` unconditionally evaluates to `AbortResult.NoAbort`,
/// ignoring any leading (discarded) statements and following a tail-call
/// chain of continuation helpers whose bodies are themselves `NoAbort`.
/// `visited` breaks cycles: a call that recurses back into the abort SCC
/// does not reduce to the CONSTANT `NoAbort`, so it is rejected.
fn block_reduces_to_no_abort(
    block: &crate::ir::Block,
    struct_id: crate::ir::StructId,
    type_args: &[Type],
    program: &Program,
    visited: &mut std::collections::BTreeSet<FunId>,
) -> bool {
    if block_returns_no_abort_after_ignored_evals(block, struct_id, type_args) {
        return true;
    }
    let e = match &block.tail {
        crate::ir::BlockTail::Value(e) => e,
        crate::ir::BlockTail::Return(e) => e.as_ref(),
        _ => return false,
    };
    let crate::ir::Expr::Call { fun, .. } = e else {
        return false;
    };
    if !visited.insert(*fun) {
        return false;
    }
    let Some(f) = program.functions.get(fun) else {
        return false;
    };
    block_reduces_to_no_abort(&f.body, struct_id, type_args, program, visited)
}

/// True iff `body` contains a `match` whose SELECTOR subtree calls one of
/// `members`. A recursive call in a `match` scrutinee is exactly the
/// non-monotone position `partial_fixpoint` rejects; `scc_is_fixpoint_eligible`
/// runs the abort-face collapse on a clone and then uses this to keep
/// NON-tail source-abort recursion (whose scrutinee call the collapse does
/// not remove) out of the `partial_fixpoint` path.
pub(crate) fn block_has_member_call_in_match_scrutinee(
    body: &crate::ir::Block,
    members: &std::collections::BTreeSet<FunId>,
) -> bool {
    struct Finder<'a> {
        members: &'a std::collections::BTreeSet<FunId>,
        found: bool,
    }
    impl crate::ir::visit::Visitor for Finder<'_> {
        fn visit_expr(&mut self, e: &crate::ir::Expr) {
            if let crate::ir::Expr::Match { selector, .. } = e {
                if expr_calls_member(selector, self.members) {
                    self.found = true;
                }
            }
            crate::ir::visit::walk_expr_default(self, e);
        }
    }
    let mut f = Finder {
        members,
        found: false,
    };
    crate::ir::visit::Visitor::visit_block(&mut f, body);
    f.found
}

fn expr_calls_member(e: &crate::ir::Expr, members: &std::collections::BTreeSet<FunId>) -> bool {
    struct C<'a> {
        members: &'a std::collections::BTreeSet<FunId>,
        hit: bool,
    }
    impl crate::ir::visit::Visitor for C<'_> {
        fn visit_expr(&mut self, e: &crate::ir::Expr) {
            if let crate::ir::Expr::Call { fun, .. } = e {
                if self.members.contains(fun) {
                    self.hit = true;
                }
            }
            crate::ir::visit::walk_expr_default(self, e);
        }
    }
    let mut c = C {
        members,
        hit: false,
    };
    crate::ir::visit::Visitor::visit_expr(&mut c, e);
    c.hit
}

fn inline_generated_abort_temporaries(body: &mut crate::ir::Block) {
    struct Pass;
    impl crate::ir::visit::MutVisitor for Pass {
        fn visit_block_mut(&mut self, b: &mut crate::ir::Block) {
            use crate::ir::Stmt;
            let counts = crate::stage_06_let_inline::use_count::count_uses(b);
            let mut i = 0;
            while i < b.stmts.len() {
                let candidate = match &b.stmts[i] {
                    Stmt::Let { pattern, value } if pattern.len() == 1 => {
                        pattern[0].as_ref().and_then(|v| {
                            (v.as_ref().starts_with("__c_")
                                && counts.get(v) == 1
                                && !counts.has_borrow_use(v))
                            .then(|| (v.clone(), value.clone()))
                        })
                    }
                    _ => None,
                };
                if let Some((v, repl)) = candidate {
                    for j in (i + 1)..b.stmts.len() {
                        crate::stage_06_let_inline::substitute::substitute_var_in_stmt(
                            &mut b.stmts[j],
                            &v,
                            &repl,
                        );
                    }
                    crate::stage_06_let_inline::substitute::substitute_var_in_tail(
                        &mut b.tail,
                        &v,
                        &repl,
                    );
                    b.stmts.remove(i);
                } else {
                    i += 1;
                }
            }
            crate::ir::visit::walk_block_mut_default(self, b);
        }
    }
    crate::ir::visit::MutVisitor::visit_block_mut(&mut Pass, body);
}

/// Emit the generated `opaque` declarations for this module's
/// ensures-published ghost outputs ([`Program::ghost_opaque_outputs`],
/// synthesised by `stage_04_ghost::materialize_opaque_ghost_outputs`).
///
/// Each declaration is the underspecified ghost value a TRUSTED spec's
/// ensures constrain but the impl's body never computes:
///
/// ```lean
/// opaque cancel_pool_reward__ghost_out_315 (t_tv0 : Type) [Inhabited t_tv0] :
///     (Mutation PoolRewardManager) -> ... -> BoundedNat (2^64)
/// ```
///
/// The impl's entry rebind calls it positionally with its full augmented
/// param list, and the stage-12 trusted axiom is its defining constraint
/// (ghost-support.md Part 4). Binders are deliberately minimal: value
/// params in arrow form (the call site applies positionally; instance
/// args are never passed), and per type param only `[Inhabited]`, which
/// `opaque`'s `Nonempty` derivation needs when the ghost value type IS
/// the type param. Demanding fewer instances than the enclosing defs is
/// always safe -- the only call site sits inside the impl, whose binder
/// set is a superset.
///
/// Must be emitted after the module's structs (a param type may be a
/// module-local struct) and before its functions (the impl body calls
/// the opaque).
pub fn render_ghost_opaque_decls<W: Write>(
    program: &Program,
    mid: crate::ir::ModId,
    current_module: Option<&str>,
    w: &mut LeanWriter<W>,
) {
    for entries in program.ghost_opaque_outputs.values() {
        for (_k, _v, opaque_fid) in entries {
            let Some(decl) = program.natives.decls.get(opaque_fid) else {
                continue;
            };
            if decl.module != mid {
                continue;
            }
            let tp_names: Vec<String> = decl.signature.type_params.clone();
            w.write("opaque ");
            w.write(&escape::escape_identifier(&decl.name));
            for tp in &tp_names {
                let tp_esc = escape::escape_identifier(tp);
                w.write(&format!(" ({0} : Type) [Inhabited {0}]", tp_esc));
            }
            w.write(" :");
            w.newline();
            w.write("    ");
            for p in &decl.signature.params {
                let tystr = ty::type_to_string(&p.ty, program, current_module, Some(&tp_names));
                w.write(&format!("({}) -> ", tystr));
            }
            let ret = ty::type_to_string(
                &decl.signature.return_type,
                program,
                current_module,
                Some(&tp_names),
            );
            w.write(&ret);
            w.newline();
            w.newline();
        }
    }
}
