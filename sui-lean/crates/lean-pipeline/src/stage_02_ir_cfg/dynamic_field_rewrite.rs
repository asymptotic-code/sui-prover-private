//! World routing for `dynamic_field` / `dynamic_object_field` ops.
//!
//! `route_df_to_world` rewrites every df/dof operation onto the
//! World-backed natives registered by
//! `dynamic_fields::register_store_natives` (`borrow` / `set` /
//! `remove` / `store_remove_if_exists` / `has` + the
//! `store_bag_*` family), with stage 4 threading `world` through the
//! callers. See `plans/lean-pipeline/container-df-unification.md`.
//!
//! The former ghost-`TypedMap` rewrite half (Pack inflation + call
//! substitution) was deleted in step-2 slice C.

use crate::ir::expr::{Block, BlockTail, Expr, Stmt};
use crate::ir::path::PathStep;
use crate::ir::visit::MutVisitor;
use crate::ir::{FunId, Program, StructId, Type, VarId};

#[derive(Clone, Copy, PartialEq, Eq)]
enum DfOp {
    Add,
    Borrow,
    Exists,
    Remove,
    RemoveIfExists,
}

#[derive(Clone, Copy)]
struct StoreFids {
    borrow: FunId,
    set: FunId,
    add: FunId,
    has: FunId,
    remove: FunId,
    remove_if_exists: FunId,
    bag_borrow: FunId,
    bag_set: FunId,
    bag_add: FunId,
    bag_has: FunId,
}

/// True iff `ty` IS (a ref to) a `bag::Bag` / `object_bag::ObjectBag`
/// directly -- the df VALUE is a whole Bag. These route to the
/// `store_bag_*` natives (which stash the bag's entry list in
/// `World.df_bag_entries`). Distinct from `type_refs_bag`, which also
/// matches a struct that merely CONTAINS a Bag (e.g. `Referral`); those
/// can't ride the bag path and stay on the in-struct no-op model.
fn value_is_bag(ty: &Type, program: &Program) -> bool {
    match ty {
        Type::Struct { struct_id, .. } => program.structs.get(struct_id).map_or(false, |s| {
            s.qualified_name == "bag::Bag" || s.qualified_name == "object_bag::ObjectBag"
        }),
        Type::Reference(inner) | Type::Vector(inner) => value_is_bag(inner, program),
        Type::MutableRef { inner, .. } => value_is_bag(inner, program),
        _ => false,
    }
}

/// True iff `edge` is a `Hyper` chain containing a `MapKey` whose VALUE
/// type is a `Bag`/`ObjectBag` -- i.e. an escaping writeback that passes
/// THROUGH a `df<K, Bag>` (e.g. ember's `get_asset_balance` returning
/// `&mut Balance` via `vault.id -> df -> Bag -> SupportedAsset -> .balance`).
/// Such writebacks store into `World`, not the object value, so they must
/// be threaded like a world-returning call. Simple in-function df ops are
/// already lowered to `store_*`/`store_bag_*` Calls before this.
fn hyper_has_df_bag_mapkey(edge: &crate::ir::borrow::BorrowEdge, program: &Program) -> bool {
    use crate::ir::borrow::BorrowEdge;
    match edge {
        BorrowEdge::Hyper(edges) => edges.iter().any(|e| {
            matches!(e, BorrowEdge::MapKey { value_type, .. } if value_is_bag(value_type, program))
        }),
        _ => false,
    }
}

/// True iff `sid` is an IN-VALUE, List-backed Sui native map whose value the
/// renderer can reconstruct mid-chain via `<Map>.borrow` (`Table` /
/// `VecMap` / `ObjectTable`). Mirrors the `recon: Some(..)` set of
/// `render::expr::writeback::native_map_ops_for_struct`; `Bag` / `ObjectBag`
/// (universe-coded, `recon: None`) are excluded because their inner value
/// can't be read back with a plain `_ _ m k` borrow.
fn struct_is_recon_native_map(sid: StructId, program: &Program) -> bool {
    program.structs.get(&sid).map_or(false, |s| {
        matches!(
            s.qualified_name.as_str(),
            "table::Table" | "vec_map::VecMap" | "object_table::ObjectTable"
        )
    })
}

/// A key type is `AnyKey`-constructible iff it has no free type parameter.
/// Kept in step with `render::mutation::is_concrete_key_payload` (private to
/// the render module, so mirrored here) -- gate and renderer must agree on
/// which df/map keys can be discriminated by an `AnyKey` constructor.
fn key_type_is_concrete(ty: &Type) -> bool {
    match ty {
        Type::Unit | Type::Bool | Type::Prop | Type::UInt(_) | Type::Address => true,
        Type::Vector(inner) => key_type_is_concrete(inner),
        Type::Tuple(elems) => elems.iter().all(key_type_is_concrete),
        Type::Struct { type_args, .. } => type_args.iter().all(key_type_is_concrete),
        Type::Reference(inner) | Type::MutableRef { inner, .. } => key_type_is_concrete(inner),
        Type::TypeParam(_) => false,
    }
}

/// True iff `prefix` (the edges before the single df anchor) navigates to the
/// df's UID through structFields and IN-VALUE recon native-map lookups only.
/// The `StructId` a (possibly reference-wrapped) `Type::Struct` names.
fn struct_id_of(ty: &Type) -> Option<StructId> {
    match ty {
        Type::Struct { struct_id, .. } => Some(*struct_id),
        Type::Reference(inner) | Type::MutableRef { inner, .. } => struct_id_of(inner),
        _ => None,
    }
}

/// Each `MapKey` must be an in-value map step: preceded by a
/// content-placeholder `StructField` into a `Table` / `VecMap` /
/// `ObjectTable`, with a concrete key, AND its recorded `value_type` must be
/// the struct whose field the next edge reads -- a well-formedness check that
/// rejects an IR borrow path whose intermediate map key/value collapsed to an
/// inner df's types (sui-system's `get_candidate_or_active_validator_mut`
/// records `validator_candidates`'s Table lookup as `[u64 -> Validator]`
/// instead of `[address -> ValidatorWrapper]`; rendering a `Table.borrow`
/// there would mistype). A pure-structField prefix (the common single-object
/// df) qualifies trivially. Kept in lockstep with
/// `render::expr::writeback::render_encodable_df_writeback`'s prefix walk,
/// which reconstructs exactly this shape (a `VecIndex` / `Bag` /
/// non-concrete-key / ill-typed map step keeps the writeback on the non-world
/// path).
fn prefix_is_world_reconstructable(
    prefix: &[crate::ir::borrow::BorrowEdge],
    program: &Program,
) -> bool {
    use crate::ir::borrow::BorrowEdge;
    let mut i = 0;
    while i < prefix.len() {
        match &prefix[i] {
            BorrowEdge::StructField { .. } => i += 1,
            BorrowEdge::MapKey {
                key_type,
                value_type,
            } => {
                let container_ok = i >= 1
                    && match &prefix[i - 1] {
                        BorrowEdge::StructField { struct_id, .. } => {
                            struct_is_recon_native_map(*struct_id, program)
                        }
                        _ => false,
                    };
                if !container_ok || !key_type_is_concrete(key_type) {
                    return false;
                }
                // The map value must be the struct whose field the next edge
                // reads; the renderer descends `<Map>.borrow ... key` then
                // that field, so an inconsistent value_type is unrenderable.
                match prefix.get(i + 1) {
                    Some(BorrowEdge::StructField { struct_id, .. }) => {
                        if struct_id_of(value_type) != Some(*struct_id) {
                            return false;
                        }
                    }
                    _ => return false,
                }
                i += 1;
            }
            _ => return false,
        }
    }
    true
}

/// Mark a hyper writeback for world-threading (-> `set` /
/// `store_bag_set`) iff it is a dynamic-field write the renderer can
/// world-thread. Two accepted shapes:
///
/// 1. **Bag-valued df** (any position): the existing `df<K, Bag>` path,
///    handled by `render_world_df_writeback`'s bag branch.
/// 2. **Simple encodable df**: EXACTLY ONE `.mapKey`, and it is the LAST
///    edge, preceded by a `.structField` into an `object::UID` field --
///    i.e. the whole df value is replaced (e.g. app whitelist
///    `df<PackageWhitestKey, VecMap>` via the `whitelist_mut` wrapper).
///
/// Accepts a df value that descends into an IN-VALUE container (`Table` /
/// `VecMap` / `Vector`) field of the stored struct -- e.g. emode's
/// `Emode.emodes_pair[id].assetA.lt` (df value `Emode`, inner
/// `Table<u64, EmodeConfig>`). The renderer (`render_nested_df_field_update`)
/// reconstructs the whole df value (in-value `Table.set`/`Vec_map.set` for
/// the inner map) and stores it back via `Dynamic_field.set`. Still EXCLUDES
/// a SECOND df anchor (a genuine `df<DFKey, Struct>`-into-another-df): the
/// `df_anchors.len() == 1` check below keeps those on the non-world path,
/// where the inner df can't be reconstructed inline.
fn hyper_has_df_mapkey(edge: &crate::ir::borrow::BorrowEdge, program: &Program) -> bool {
    use crate::ir::borrow::BorrowEdge;
    if hyper_has_df_bag_mapkey(edge, program) {
        return true;
    }
    let edges = match edge {
        BorrowEdge::Hyper(es) => es,
        _ => return false,
    };
    // The df anchor is a `.mapKey` preceded by a `.structField` into an
    // `object::UID` field. There must be EXACTLY ONE -- a second df
    // anchor (emode's `df<DFKey, Struct>` descending into an inner df)
    // genuinely can't be reconstructed inline and stays on the
    // non-world-threaded path.
    let edge_into_uid = |i: usize| -> bool {
        i >= 1
            && match &edges[i - 1] {
                BorrowEdge::StructField {
                    struct_id,
                    field_index,
                } => program
                    .structs
                    .get(struct_id)
                    .and_then(|s| s.fields.get(*field_index))
                    .map_or(false, |f| is_uid_type(&f.field_type, program)),
                _ => false,
            }
    };
    let df_anchors: Vec<usize> = (0..edges.len())
        .filter(|&i| matches!(edges[i], BorrowEdge::MapKey { .. }) && edge_into_uid(i))
        .collect();
    if df_anchors.len() != 1 {
        return false;
    }
    let mk = df_anchors[0];
    // Everything before the df anchor navigates to the UID via structFields
    // OR in-value native-map lookups (Table / VecMap / ObjectTable content
    // placeholder + concrete MapKey) -- e.g. sui-system's
    // `candidate_validator_mut` reaches the Versioned df through
    // `ValidatorSet.validator_candidates[addr].inner.id`. The renderer
    // (`render_encodable_df_writeback`) rebuilds the uid by threading a native
    // `<Map>.borrow` at each map step; gate and renderer stay in lockstep on
    // exactly this shape.
    if !prefix_is_world_reconstructable(&edges[..mk], program) {
        return false;
    }
    // The map-prefixed renderer arm binds `AnyKey` constructors and has no
    // `FromAnyKey` bridge, so it needs a CONCRETE df key too. The
    // all-structField prefix keeps the general encodable path (generic keys
    // via `FromAnyKey`), so only constrain the df key when the prefix threads
    // through an in-value map.
    let prefix_all_structfield = edges[..mk]
        .iter()
        .all(|e| matches!(e, BorrowEdge::StructField { .. }));
    if !prefix_all_structfield {
        let df_key = match &edges[mk] {
            BorrowEdge::MapKey { key_type, .. } => key_type,
            _ => return false,
        };
        if !key_type_is_concrete(df_key) {
            return false;
        }
    }
    // Trailing after the df anchor: a chain of `.field` accesses into the
    // stored value (escaping &mut to `node.value`, `node.value.f`...),
    // OPTIONALLY ending in a single VALUE-FORM container leaf -- a
    // `.vecIndex` or a `.mapKey` that is NOT itself a df anchor (cetus
    // dlmm's `node.value.group.bins[offset]`). Both reconstruct the whole
    // df value and store it back via `set`. A second df anchor in the
    // trailing is excluded above; any non-leaf index, or a leaf followed
    // by more edges, is not handled.
    let trailing = &edges[mk + 1..];
    for e in trailing.iter() {
        match e {
            // structFields navigate into the stored value; `vecIndex` /
            // `mapKey` are in-value container steps (`Vector` / `Table` /
            // `VecMap`) at ANY depth -- a leaf (`node.value.bins[offset]`)
            // OR in the middle (emode `Emode.emodes_pair[id].assetA.lt`).
            // `df_anchors.len() == 1` already guarantees no SECOND df anchor
            // hides in the trailing (a real nested df<DFKey, Struct>-into-df
            // is still excluded), so every trailing mapKey here is an
            // in-value List-backed map, which `render_nested_df_field_update`
            // reconstructs (falling back to identity for anything it can't,
            // matching the prior drop -- never a new render error).
            BorrowEdge::StructField { .. } | BorrowEdge::VecIndex | BorrowEdge::MapKey { .. } => {}
            _ => return false,
        }
    }
    // The whole-value-store path excludes a DIRECT `bag::Bag` df value
    // (it rides `store_bag_*` via `hyper_has_df_bag_mapkey` case 1). A
    // bag-CONTAINING struct is a legal `TyCode` df value and rides `set`.
    // See `plans/lean-pipeline/split-bag-df-universes.md`.
    let v1 = match &edges[mk] {
        BorrowEdge::MapKey { value_type, .. } => value_type,
        _ => return false,
    };
    !value_is_bag(v1, program)
}

fn find_df_module(program: &Program) -> Option<crate::ir::ModId> {
    program.module_id_by_name("Sui", "dynamic_field")
}

/// `(option::some, option::none)` translated-function FunIds, if the
/// MoveStdlib option module is in the program.
fn find_option_fids(program: &Program) -> Option<(FunId, FunId)> {
    let opt_mod = program.module_id_by_name("MoveStdlib", "option")?;
    let mut some_fid = None;
    let mut none_fid = None;
    for (fid, f) in program.functions.iter() {
        if f.module != opt_mod {
            continue;
        }
        match f.name.as_str() {
            "some" => some_fid = Some(*fid),
            "none" => none_fid = Some(*fid),
            _ => {}
        }
    }
    Some((some_fid?, none_fid?))
}

fn store_fids(program: &Program, df_mod: crate::ir::ModId) -> Option<StoreFids> {
    let (mut b, mut s, mut h) = (None, None, None);
    let mut a = None;
    let (mut rm, mut rie) = (None, None);
    let (mut bb, mut bs, mut bh) = (None, None, None);
    let mut ba = None;
    for (fid, d) in &program.natives.decls {
        if d.module != df_mod {
            continue;
        }
        match d.name.as_str() {
            "borrow" => b = Some(*fid),
            "set" => s = Some(*fid),
            "add" => a = Some(*fid),
            "has" => h = Some(*fid),
            "remove" => rm = Some(*fid),
            "store_remove_if_exists" => rie = Some(*fid),
            "store_bag_borrow" => bb = Some(*fid),
            "store_bag_set" => bs = Some(*fid),
            "store_bag_add" => ba = Some(*fid),
            "store_bag_has" => bh = Some(*fid),
            _ => {}
        }
    }
    Some(StoreFids {
        borrow: b?,
        set: s?,
        add: a?,
        has: h?,
        remove: rm?,
        remove_if_exists: rie?,
        bag_borrow: bb?,
        bag_set: bs?,
        bag_add: ba?,
        bag_has: bh?,
    })
}

fn df_op(program: &Program, _df_mod: crate::ir::ModId, fun: FunId) -> Option<DfOp> {
    // df ops may be lifted as natives (e.g. `borrow`) OR as functions
    // (e.g. `add`), so resolve via `lookup_callee`, which handles both.
    //
    // Accept BOTH `Sui::dynamic_field` AND `Sui::dynamic_object_field`.
    // dof is modelled identically to df: the value being an object is a
    // Move-blockchain storage optimisation we deliberately do NOT model.
    // Routing dof ops through the same World `store_*` natives keeps them
    // faithful (real read/write/has/remove on `World.df_entries`) and
    // avoids the broken native-stub call sites -- `dof::borrow` rendered
    // with an explicit `Parent` type-arg the 2-type-arg call never
    // supplies, which partially-applies into a `Function`. The `store_*`
    // fids still come from the `dynamic_field` module (`store_fids`); only
    // the recognition gate widens.
    let callee = program.lookup_callee(fun)?;
    let module = program.modules.get(&callee.module())?;
    if module.package_name != "Sui"
        || !matches!(
            module.name.as_str(),
            "dynamic_field" | "dynamic_object_field"
        )
    {
        return None;
    }
    match callee.name() {
        "add" => Some(DfOp::Add),
        "borrow" => Some(DfOp::Borrow),
        // The framework renamed `exists_` to `exists`; a package resolves
        // whichever its pinned framework revision declares.
        "exists" | "exists_" | "exists_with_type" => Some(DfOp::Exists),
        "remove" => Some(DfOp::Remove),
        "remove_if_exists" => Some(DfOp::RemoveIfExists),
        _ => None,
    }
}

struct RouteCtx<'a> {
    program: &'a Program,
    df_mod: crate::ir::ModId,
    fids: StoreFids,
    uid_vars: std::collections::HashSet<crate::ir::VarId>,
    key_for_var: std::collections::HashMap<crate::ir::VarId, (Expr, Type, Type)>,
    /// Structs that (transitively) contain a `Bag` / `ObjectBag`, hence
    /// are excluded from the closed `TyCode` universe. A df whose VALUE
    /// type references one of these is NOT routed to the World store_*
    /// natives -- `HasCode TyCode <value>` would not resolve -- and is
    /// left on the in-struct map-key model. See render::dyn_type_universe.
    bag_ids: &'a std::collections::HashSet<StructId>,
    /// `(option::some, option::none)` FunIds, used by the
    /// remove_if_exists arm to construct the Option result. `None` when
    /// the MoveStdlib option module isn't in the program (the arm then
    /// panics if a remove_if_exists call is nonetheless encountered).
    option_fids: Option<(FunId, FunId)>,
}

/// True iff `ty` (transitively) references a bag-containing struct or a
/// `bag::Bag` / `object_bag::ObjectBag` directly -- i.e. is NOT
/// encodable in the `TyCode` universe used by the World df store.
fn type_refs_bag(
    ty: &Type,
    bag_ids: &std::collections::HashSet<StructId>,
    program: &Program,
) -> bool {
    match ty {
        Type::Struct {
            struct_id,
            type_args,
        } => {
            if bag_ids.contains(struct_id) {
                return true;
            }
            if let Some(s) = program.structs.get(struct_id) {
                if s.qualified_name == "bag::Bag" || s.qualified_name == "object_bag::ObjectBag" {
                    return true;
                }
            }
            type_args.iter().any(|a| type_refs_bag(a, bag_ids, program))
        }
        Type::Vector(inner) | Type::Reference(inner) => type_refs_bag(inner, bag_ids, program),
        Type::MutableRef { inner, root } => {
            type_refs_bag(inner, bag_ids, program) || type_refs_bag(root, bag_ids, program)
        }
        Type::Tuple(ts) => ts.iter().any(|t| type_refs_bag(t, bag_ids, program)),
        _ => false,
    }
}

fn is_uid_type(ty: &Type, program: &Program) -> bool {
    match ty {
        Type::Struct { struct_id, .. } => program
            .structs
            .get(struct_id)
            .map(|s| s.qualified_name == "object::UID")
            .unwrap_or(false),
        Type::MutableRef { inner, .. } => is_uid_type(inner, program),
        Type::Reference(inner) => is_uid_type(inner, program),
        _ => false,
    }
}

/// True iff `fun`'s (first) return component is an `object::UID`. Recognizes
/// uid-accessor wrappers (`market::uid` / `uid_mut`) so a var bound to such a
/// call is treated as a df-anchor UID -- routing its df ops through the World
/// model (borrow/set) rather than the ghost-model identity
/// writeback. Without this, df ops reached through a uid wrapper silently drop
/// their add (and a World-model reader of the same key sees it absent).
fn call_result_is_uid(program: &Program, fun: crate::ir::FunId) -> bool {
    let Some(f) = program.functions.get(&fun) else {
        return false;
    };
    match &f.signature.return_type {
        Type::Tuple(elems) => elems
            .first()
            .map(|t| is_uid_type(t, program))
            .unwrap_or(false),
        other => is_uid_type(other, program),
    }
}

/// Walk a function body recording (a) vars bound to a `BorrowField` of an
/// `object::UID` field -- the df "anchor" UIDs -- and (b) the key for each
/// `BorrowMapKey` keyed by its base var (the WriteBack edge doesn't carry
/// the key value, only its type, so we recover it from the borrow site).
fn collect_uid_info(
    program: &Program,
    b: &Block,
    uid_vars: &mut std::collections::HashSet<crate::ir::VarId>,
    key_for_var: &mut std::collections::HashMap<crate::ir::VarId, (Expr, Type, Type)>,
) {
    for st in &b.stmts {
        if let Stmt::Let { pattern, value } = st {
            if let Some(Some(v)) = pattern.first() {
                if let Expr::Borrow {
                    step:
                        PathStep::Field {
                            struct_id,
                            field_index,
                        },
                    ..
                } = value
                {
                    let is_uid = program
                        .structs
                        .get(struct_id)
                        .and_then(|s| s.fields.get(*field_index))
                        .map(|fld| is_uid_type(&fld.field_type, program))
                        .unwrap_or(false);
                    if is_uid {
                        uid_vars.insert(v.clone());
                    }
                }
                if let Expr::Call { fun, .. } = value {
                    if call_result_is_uid(program, *fun) {
                        uid_vars.insert(v.clone());
                    }
                }
            }
            if let Expr::Borrow {
                step:
                    PathStep::MapKey {
                        key,
                        key_type,
                        value_type,
                        df_value: _,
                    },
                base,
            } = value
            {
                if let Expr::Var(bv) = base.as_ref() {
                    key_for_var.insert(
                        bv.clone(),
                        ((**key).clone(), key_type.clone(), value_type.clone()),
                    );
                }
            }
        }
        let val = match st {
            Stmt::Let { value, .. } => value,
            Stmt::Eval(e) => e,
        };
        collect_uid_info_nested(program, val, uid_vars, key_for_var);
    }
}

fn collect_uid_info_nested(
    program: &Program,
    e: &Expr,
    uid_vars: &mut std::collections::HashSet<crate::ir::VarId>,
    key_for_var: &mut std::collections::HashMap<crate::ir::VarId, (Expr, Type, Type)>,
) {
    match e {
        Expr::If {
            then_branch,
            else_branch,
            ..
        } => {
            collect_uid_info(program, then_branch, uid_vars, key_for_var);
            collect_uid_info(program, else_branch, uid_vars, key_for_var);
        }
        Expr::While { header, body, .. } => {
            collect_uid_info(program, header, uid_vars, key_for_var);
            collect_uid_info(program, body, uid_vars, key_for_var);
        }
        Expr::Match { cases, .. } => {
            for a in cases {
                collect_uid_info(program, &a.body, uid_vars, key_for_var);
            }
        }
        Expr::Quantifier { body, .. } | Expr::LabeledBlock { body, .. } => {
            collect_uid_info(program, body, uid_vars, key_for_var)
        }
        _ => {}
    }
}

/// Structs whose fields (transitively) reference `bag::Bag` /
/// `object_bag::ObjectBag`. These are excluded from the closed `TyCode`
/// universe (see render::dyn_type_universe::collect), so a df whose
/// value type references one cannot be stored in `World.df_entries`.
/// Inlined here (rather than depending on the downstream `render`
/// module) to keep the stage-2 -> render layering one-directional.
fn collect_bag_containing_struct_ids(program: &Program) -> std::collections::HashSet<StructId> {
    fn struct_ids_in_type(ty: &Type, out: &mut Vec<StructId>) {
        match ty {
            Type::Struct {
                struct_id,
                type_args,
            } => {
                out.push(*struct_id);
                for a in type_args {
                    struct_ids_in_type(a, out);
                }
            }
            Type::Vector(inner) | Type::Reference(inner) => struct_ids_in_type(inner, out),
            Type::MutableRef { inner, root } => {
                struct_ids_in_type(inner, out);
                struct_ids_in_type(root, out);
            }
            Type::Tuple(ts) => ts.iter().for_each(|t| struct_ids_in_type(t, out)),
            _ => {}
        }
    }
    let is_container = |sid: &StructId| -> bool {
        program.structs.get(sid).map_or(false, |s| {
            s.qualified_name == "bag::Bag" || s.qualified_name == "object_bag::ObjectBag"
        })
    };
    let mut tainted: std::collections::HashSet<StructId> = std::collections::HashSet::new();
    for (sid, s) in program.structs.iter() {
        for f in &s.fields {
            let mut deps = Vec::new();
            struct_ids_in_type(&f.field_type, &mut deps);
            if deps.iter().any(|d| is_container(d)) {
                tainted.insert(*sid);
                break;
            }
        }
    }
    let mut changed = true;
    while changed {
        changed = false;
        for (sid, s) in program.structs.iter() {
            if tainted.contains(sid) {
                continue;
            }
            for f in &s.fields {
                let mut deps = Vec::new();
                struct_ids_in_type(&f.field_type, &mut deps);
                if deps.iter().any(|d| tainted.contains(d)) {
                    tainted.insert(*sid);
                    changed = true;
                    break;
                }
            }
        }
    }
    tainted
}

pub fn route_df_to_world(program: &mut Program) {
    let Some(df_mod) = find_df_module(program) else {
        return;
    };
    let Some(fids) = store_fids(program, df_mod) else {
        return;
    };
    let option_fids = find_option_fids(program);
    // df VALUE types that reference a Bag/ObjectBag aren't in the TyCode
    // universe, so they can't be stored in `World.df_entries`. Compute
    // the exclusion set once; `route_block`/`route_expr` leave such df
    // ops on the in-struct map-key model.
    let bag_ids = collect_bag_containing_struct_ids(program);
    let fn_ids: Vec<FunId> = program.functions.keys().copied().collect();
    for fid in fn_ids {
        let mut body = std::mem::replace(
            &mut program.functions.get_mut(&fid).unwrap().body,
            Block {
                stmts: Vec::new(),
                tail: BlockTail::Value(Expr::Unit),
            },
        );
        let mut uid_vars = std::collections::HashSet::new();
        let mut key_for_var = std::collections::HashMap::new();
        collect_uid_info(program, &body, &mut uid_vars, &mut key_for_var);
        // A dynamic field borrowed directly off a `&mut UID` (or `UID`)
        // PARAMETER is just as much a World-routed df as one off `self.id`:
        // e.g. `assert_not_equal_and_set(id: &mut UID, name, v)` does
        // `dynamic_field::borrow_mut(id, name); *current = v`. `collect_uid_info`
        // only records UIDs reached via a `BorrowField` of a UID field or a
        // uid-accessor call, so a bare UID param is missed and `route_block`
        // leaves its df borrow/writeback as a value-position identity stub
        // that silently drops the write (and reads `default`). Seed such
        // params so the borrow -> `borrow`/`bag_borrow` and writeback ->
        // `set`/`bag_set` World conversions in `route_block` fire.
        for p in &program.functions.get(&fid).unwrap().signature.params {
            if is_uid_type(&p.ty, program) {
                uid_vars.insert(p.var.clone());
            }
        }
        let ctx = RouteCtx {
            program,
            df_mod,
            fids: StoreFids { ..fids },
            uid_vars,
            key_for_var,
            bag_ids: &bag_ids,
            option_fids,
        };
        route_block(&mut body, &ctx);
        program.functions.get_mut(&fid).unwrap().body = body;
    }
    // Reborrow coalescing: merge the `nexts = &mut node.nexts` reborrow temp
    // into the named tracker so the loop carries ONE snapshot of the vector.
    // Upstream's MemoryInstrumentationProcessor would otherwise emit a
    // two-tracker is_parent dispatch whose path-dependent writeback leaves one
    // snapshot stale (skip_list find/remove). The now-degenerate
    // `isSameMutation(W, W)` node guards collapse to the negation of the head
    // guard. See plans/lean-pipeline/world-df-writeback-completion.md.
    coalesce_reborrow_aliases(program);
}

// ===================================================================
// Pre-stage-7 reborrow coalescing (replaces sync_aliased_vec_writebacks).
//
// Upstream's MemoryInstrumentationProcessor emits a two-tracker is_parent
// dispatch for `nexts = &mut node.nexts`: the named `nexts` and the reborrow
// temp become separate snapshots of the SAME vector, and swap_or_fill's
// writeback updates only one (path-dependent), leaving the other stale. We
// merge the reborrow temp into the named var (one snapshot), then collapse the
// now-degenerate `is_parent(W, W)` node guards into the negation of the head
// guard. Bails (reverts the function body) if any degenerate guard lacks a
// head pair, so only the clean 2-way head/node shape is rewritten.
// ===================================================================

fn coalesce_reborrow_aliases(program: &mut Program) {
    let Some(df_mod) = find_df_module(program) else {
        return;
    };
    let Some(fids) = store_fids(program, df_mod) else {
        return;
    };
    let store_fids: std::collections::HashSet<FunId> = [
        fids.borrow,
        fids.set,
        fids.has,
        fids.remove,
        fids.bag_borrow,
        fids.bag_set,
        fids.bag_has,
    ]
    .into_iter()
    .collect();
    let fn_ids: Vec<FunId> = program.functions.keys().copied().collect();
    for fid in fn_ids {
        let func = program.functions.get_mut(&fid).unwrap();
        if !block_uses_df_store(&func.body, &store_fids) {
            continue;
        }
        let original = func.body.clone();
        if !coalesce_in_body(&mut func.body) {
            func.body = original;
        }
    }
}

/// Rename one variable to another across a whole block -- every `VarId`
/// slot (references, borrow nodes, `MapKey.df_value`, and binders) via the
/// shared `visit_var_mut` walk.
struct VarRenamer<'a> {
    from: &'a VarId,
    to: &'a VarId,
}

impl MutVisitor for VarRenamer<'_> {
    fn visit_var_mut(&mut self, v: &mut VarId) {
        if v == self.from {
            *v = self.to.clone();
        }
    }
}

fn coalesce_in_body(body: &mut Block) -> bool {
    let mut reborrows: std::collections::HashSet<VarId> = std::collections::HashSet::new();
    collect_loop_borrowfields(body, false, &mut reborrows);

    let mut copies: Vec<(VarId, VarId)> = Vec::new();
    collect_reborrow_copies(body, &reborrows, &mut copies);
    if copies.is_empty() {
        return true;
    }
    for (v, w) in &copies {
        VarRenamer { from: v, to: w }.visit_block_mut(body);
    }
    drop_self_copies(body);
    let mut head: std::collections::HashMap<VarId, VarId> = std::collections::HashMap::new();
    let mut ok = true;
    fold_isparent(body, &mut head, &mut ok);
    ok
}

fn coalesce_blocks(e: &Expr) -> Vec<&Block> {
    match e {
        Expr::If {
            then_branch,
            else_branch,
            ..
        } => vec![then_branch, else_branch],
        Expr::While { header, body, .. } => vec![header, body],
        Expr::Match { cases, .. } => cases.iter().map(|a| a.body.as_ref()).collect(),
        Expr::LabeledBlock { body, .. } | Expr::Quantifier { body, .. } => vec![body],
        _ => vec![],
    }
}

fn stmt_expr(st: &Stmt) -> &Expr {
    match st {
        Stmt::Let { value, .. } => value,
        Stmt::Eval(e) => e,
    }
}

fn tail_expr(t: &BlockTail) -> &Expr {
    match t {
        BlockTail::Value(e) => e,
        BlockTail::Break { value, .. }
        | BlockTail::Continue { value, .. }
        | BlockTail::Return(value)
        | BlockTail::ReturnFromBlock { value, .. }
        | BlockTail::Abort { code: value } => value.as_ref(),
    }
}

// Collect vars defined as `&base.field` (BorrowField) INSIDE a loop body.
// These are the loop-carried reborrow temps -- the general `&mut`
// reborrow-alias pattern (`nexts = &mut node.nexts`, `cur = &mut node.next`,
// ...), NOT vector-specific. The two-tracker divergence is inherently
// loop-carried, so we require a loop-local def. This deliberately excludes:
//   - the stable anchor (`&list.head`): also a BorrowField, but defined
//     PRE-loop (loop-invariant), so the head/node `is_parent` dispatch
//     survives the fold instead of being merged away;
//   - the scalar element walkers (`&vec[i]`): those are BorrowVecIndex, the
//     leaves being mutated, not the traversal tracker.
fn collect_loop_borrowfields(b: &Block, in_loop: bool, set: &mut std::collections::HashSet<VarId>) {
    for st in &b.stmts {
        if in_loop {
            if let Stmt::Let { pattern, value } = st {
                if pattern.len() == 1 {
                    if let Some(Some(v)) = pattern.first() {
                        if matches!(
                            value,
                            Expr::Borrow {
                                step: PathStep::Field { .. },
                                ..
                            }
                        ) {
                            set.insert(v.clone());
                        }
                    }
                }
            }
        }
        collect_loop_borrowfields_expr(stmt_expr(st), in_loop, set);
    }
    collect_loop_borrowfields_expr(tail_expr(&b.tail), in_loop, set);
}

fn collect_loop_borrowfields_expr(
    e: &Expr,
    in_loop: bool,
    set: &mut std::collections::HashSet<VarId>,
) {
    match e {
        Expr::While { header, body, .. } => {
            collect_loop_borrowfields(header, true, set);
            collect_loop_borrowfields(body, true, set);
        }
        Expr::If {
            then_branch,
            else_branch,
            ..
        } => {
            collect_loop_borrowfields(then_branch, in_loop, set);
            collect_loop_borrowfields(else_branch, in_loop, set);
        }
        Expr::Match { cases, .. } => {
            for a in cases {
                collect_loop_borrowfields(&a.body, in_loop, set);
            }
        }
        Expr::LabeledBlock { body, .. } | Expr::Quantifier { body, .. } => {
            collect_loop_borrowfields(body, in_loop, set);
        }
        _ => {}
    }
}

fn collect_reborrow_copies(
    b: &Block,
    reborrows: &std::collections::HashSet<VarId>,
    out: &mut Vec<(VarId, VarId)>,
) {
    for st in &b.stmts {
        if let Stmt::Let {
            pattern,
            value: Expr::Var(v),
        } = st
        {
            if pattern.len() == 1 {
                if let Some(Some(w)) = pattern.first() {
                    if w != v && reborrows.contains(v) {
                        out.push((v.clone(), w.clone()));
                    }
                }
            }
        }
        for blk in coalesce_blocks(stmt_expr(st)) {
            collect_reborrow_copies(blk, reborrows, out);
        }
    }
    for blk in coalesce_blocks(tail_expr(&b.tail)) {
        collect_reborrow_copies(blk, reborrows, out);
    }
}

fn borrownode_var(n: &crate::ir::borrow::BorrowNode) -> Option<&VarId> {
    use crate::ir::borrow::BorrowNode;
    match n {
        BorrowNode::LocalRoot(v) | BorrowNode::Reference(v) => Some(v),
        BorrowNode::GlobalRoot(_) | BorrowNode::SpecGlobalRoot { .. } => None,
    }
}

fn is_self_copy(st: &Stmt) -> bool {
    if let Stmt::Let {
        pattern,
        value: Expr::Var(v),
    } = st
    {
        if pattern.len() == 1 {
            if let Some(Some(w)) = pattern.first() {
                return w == v;
            }
        }
    }
    false
}

fn drop_self_copies(b: &mut Block) {
    b.stmts.retain(|st| !is_self_copy(st));
    for st in &mut b.stmts {
        drop_self_copies_expr(match st {
            Stmt::Let { value, .. } => value,
            Stmt::Eval(e) => e,
        });
    }
    drop_self_copies_expr(match &mut b.tail {
        BlockTail::Value(e) => e,
        BlockTail::Break { value, .. }
        | BlockTail::Continue { value, .. }
        | BlockTail::Return(value)
        | BlockTail::ReturnFromBlock { value, .. }
        | BlockTail::Abort { code: value } => value.as_mut(),
    });
}

fn drop_self_copies_expr(e: &mut Expr) {
    match e {
        Expr::If {
            then_branch,
            else_branch,
            ..
        } => {
            drop_self_copies(then_branch);
            drop_self_copies(else_branch);
        }
        Expr::While { header, body, .. } => {
            drop_self_copies(header);
            drop_self_copies(body);
        }
        Expr::Match { cases, .. } => {
            for a in cases.iter_mut() {
                drop_self_copies(&mut a.body);
            }
        }
        Expr::LabeledBlock { body, .. } | Expr::Quantifier { body, .. } => drop_self_copies(body),
        _ => {}
    }
}

fn fold_isparent(b: &mut Block, head: &mut std::collections::HashMap<VarId, VarId>, ok: &mut bool) {
    for st in &mut b.stmts {
        let mut rewrite: Option<Expr> = None;
        let mut record: Option<(VarId, VarId)> = None;
        if let Stmt::Let { pattern, value } = st {
            if let Expr::IsParent { node, edge, child } = value {
                if matches!(edge, crate::ir::borrow::BorrowEdge::Direct) {
                    let nv = borrownode_var(node).cloned();
                    let child_c = child.clone();
                    if nv.as_ref() == Some(&child_c) {
                        if let Some(hg) = head.get(&child_c).cloned() {
                            rewrite = Some(Expr::UnOp {
                                op: crate::ir::ops::UnOp::Not,
                                operand: Box::new(Expr::Var(hg)),
                            });
                        } else {
                            *ok = false;
                        }
                    } else if pattern.len() == 1 {
                        if let Some(Some(g)) = pattern.first() {
                            record = Some((child_c, g.clone()));
                        }
                    }
                }
            }
        }
        if let Some(new_val) = rewrite {
            if let Stmt::Let { value, .. } = st {
                *value = new_val;
            }
        }
        if let Some((c, g)) = record {
            head.insert(c, g);
        }
        let e = match st {
            Stmt::Let { value, .. } => value,
            Stmt::Eval(e) => e,
        };
        fold_isparent_expr(e, head, ok);
    }
    let te = match &mut b.tail {
        BlockTail::Value(e) => e,
        BlockTail::Break { value, .. }
        | BlockTail::Continue { value, .. }
        | BlockTail::Return(value)
        | BlockTail::ReturnFromBlock { value, .. }
        | BlockTail::Abort { code: value } => value.as_mut(),
    };
    fold_isparent_expr(te, head, ok);
}

fn fold_isparent_expr(e: &mut Expr, head: &std::collections::HashMap<VarId, VarId>, ok: &mut bool) {
    match e {
        Expr::If {
            then_branch,
            else_branch,
            ..
        } => {
            let mut h1 = head.clone();
            fold_isparent(then_branch, &mut h1, ok);
            let mut h2 = head.clone();
            fold_isparent(else_branch, &mut h2, ok);
        }
        Expr::While { header, body, .. } => {
            let mut hh = head.clone();
            fold_isparent(header, &mut hh, ok);
            let mut hb = head.clone();
            fold_isparent(body, &mut hb, ok);
        }
        Expr::Match { cases, .. } => {
            for a in cases.iter_mut() {
                let mut h = head.clone();
                fold_isparent(&mut a.body, &mut h, ok);
            }
        }
        Expr::LabeledBlock { body, .. } | Expr::Quantifier { body, .. } => {
            let mut h = head.clone();
            fold_isparent(body, &mut h, ok);
        }
        _ => {}
    }
}

fn block_uses_df_store(b: &Block, store_fids: &std::collections::HashSet<FunId>) -> bool {
    for st in &b.stmts {
        let e = match st {
            Stmt::Let { value, .. } => value,
            Stmt::Eval(e) => e,
        };
        if expr_uses_df_store(e, store_fids) {
            return true;
        }
    }
    match &b.tail {
        BlockTail::Value(e) => expr_uses_df_store(e, store_fids),
        BlockTail::Break { value, .. }
        | BlockTail::Continue { value, .. }
        | BlockTail::Return(value)
        | BlockTail::ReturnFromBlock { value, .. }
        | BlockTail::Abort { code: value } => expr_uses_df_store(value, store_fids),
    }
}

fn expr_uses_df_store(e: &Expr, store_fids: &std::collections::HashSet<FunId>) -> bool {
    use Expr::*;
    match e {
        Call { fun, args, .. } => {
            store_fids.contains(fun) || args.iter().any(|a| expr_uses_df_store(a, store_fids))
        }
        If {
            then_branch,
            else_branch,
            ..
        } => {
            block_uses_df_store(then_branch, store_fids)
                || block_uses_df_store(else_branch, store_fids)
        }
        Match { cases, .. } => cases
            .iter()
            .any(|a| block_uses_df_store(&a.body, store_fids)),
        While { header, body, .. } => {
            block_uses_df_store(header, store_fids) || block_uses_df_store(body, store_fids)
        }
        Quantifier { body, .. } | LabeledBlock { body, .. } => {
            block_uses_df_store(body, store_fids)
        }
        BinOp { lhs, rhs, .. } => {
            expr_uses_df_store(lhs, store_fids) || expr_uses_df_store(rhs, store_fids)
        }
        UnOp { operand, .. } => expr_uses_df_store(operand, store_fids),
        Tuple(args) | Pack { fields: args, .. } => {
            args.iter().any(|a| expr_uses_df_store(a, store_fids))
        }
        Unpack { value: inner, .. }
        | Field { base: inner, .. }
        | ReadRef(inner)
        | ToProp(inner)
        | ToBool(inner) => expr_uses_df_store(inner, store_fids),
        WriteRef { reference, value } => {
            expr_uses_df_store(reference, store_fids) || expr_uses_df_store(value, store_fids)
        }
        _ => false,
    }
}

// In `let vT = WriteBack { edge: VecIndex, .. }` inside an if-then-branch,
// return `vT` (the vector being updated by the vec-index writeback).
fn route_block(b: &mut Block, ctx: &RouteCtx) {
    let mut out: Vec<Stmt> = Vec::with_capacity(b.stmts.len());
    for mut stmt in std::mem::take(&mut b.stmts) {
        match &mut stmt {
            Stmt::Let { value, .. } => route_expr(value, ctx),
            Stmt::Eval(e) => route_expr(e, ctx),
        }
        // df borrow_mut: `let m = BorrowMapKey(base=uid, key)` ->
        //   `let m__dfv = borrow(uid, key)` + `let m = BorrowLoc(m__dfv)`
        if let Stmt::Let {
            pattern,
            value:
                Expr::Borrow {
                    step:
                        PathStep::MapKey {
                            key,
                            key_type,
                            value_type,
                            df_value: _,
                        },
                    base,
                },
        } = &stmt
        {
            if let Expr::Var(bv) = base.as_ref() {
                // bag-valued df -> store_bag_borrow; everything else
                // (incl. bag-CONTAINING structs like Referral, now legal
                // TyCode df values) -> borrow. See
                // `plans/lean-pipeline/split-bag-df-universes.md`.
                let borrow_fid = if value_is_bag(value_type, ctx.program) {
                    Some(ctx.fids.bag_borrow)
                } else {
                    Some(ctx.fids.borrow)
                };
                if ctx.uid_vars.contains(bv) {
                    if let Some(bfid) = borrow_fid {
                        let stem = pattern.first().and_then(|o| o.as_deref()).unwrap_or("df");
                        let vf: crate::ir::VarId = format!("{stem}__dfv").into();
                        out.push(Stmt::Let {
                            pattern: vec![Some(vf.clone())],
                            value: Expr::Call {
                                fun: bfid,
                                type_args: vec![key_type.clone(), value_type.clone()],
                                args: vec![Expr::Var(bv.clone()), (**key).clone()],
                            },
                        });
                        // Path-EXTENDING borrow off the UID mutation, value
                        // supplied from the World read (`vf`). This keeps the
                        // df key in `m`'s Mutation path (`uid.path ++ [.mapKey
                        // key]`) so an escaping `&mut`-return writeback can
                        // recover it -- rather than `BorrowLoc` (ofLocal),
                        // which would reset the path and drop the df key.
                        out.push(Stmt::Let {
                            pattern: pattern.clone(),
                            value: Expr::Borrow {
                                step: PathStep::MapKey {
                                    key: key.clone(),
                                    key_type: key_type.clone(),
                                    value_type: value_type.clone(),
                                    df_value: Some(vf),
                                },
                                base: base.clone(),
                            },
                        });
                        continue;
                    }
                }
            }
        }
        // df borrow_mut writeback: `let p = WriteBack(node=uid, MapKey, child)` ->
        //   `let p = uid` (UID unchanged) + `set(uid, key, child)`
        if let Stmt::Let {
            pattern,
            value:
                Expr::WriteBack {
                    node,
                    edge,
                    child,
                    world: _,
                },
        } = &stmt
        {
            if matches!(edge, crate::ir::borrow::BorrowEdge::MapKey { .. }) {
                let nv = match node {
                    crate::ir::borrow::BorrowNode::Reference(v)
                    | crate::ir::borrow::BorrowNode::LocalRoot(v) => Some(v.clone()),
                    _ => None,
                };
                if let Some(nv) = nv {
                    if ctx.uid_vars.contains(&nv) {
                        if let Some((key, kt, vt)) = ctx.key_for_var.get(&nv) {
                            // bag-valued -> store_bag_set; everything
                            // else (incl. bag-containing structs) -> set.
                            let set_fid = if value_is_bag(vt, ctx.program) {
                                Some(ctx.fids.bag_set)
                            } else {
                                Some(ctx.fids.set)
                            };
                            if let Some(sfid) = set_fid {
                                out.push(Stmt::Let {
                                    pattern: pattern.clone(),
                                    value: Expr::Var(nv.clone()),
                                });
                                out.push(Stmt::Eval(Expr::Call {
                                    fun: sfid,
                                    type_args: vec![kt.clone(), vt.clone()],
                                    args: vec![
                                        Expr::Var(nv.clone()),
                                        key.clone(),
                                        Expr::Var(child.clone()),
                                    ],
                                }));
                                continue;
                            }
                        }
                    }
                }
            }
        }
        // df add: `let aug = add(uid, k, v)` -> `let aug = uid` + `set(uid, k, v)`
        if let Stmt::Let {
            pattern,
            value:
                Expr::Call {
                    fun,
                    type_args,
                    args,
                },
        } = &stmt
        {
            if df_op(ctx.program, ctx.df_mod, *fun) == Some(DfOp::Add)
                && args.len() == 3
                && type_args.len() >= 2
            {
                // Source-level add routes to `add` (same Lean body as
                // set, but with the spec_target'd abort-iff-PRESENT
                // companion -- EFieldAlreadyExists). Bag-valued adds route to
                // `store_bag_add` (same World action as store_bag_set, plus
                // the type-agnostic EFieldAlreadyExists companion that checks
                // BOTH the bag store AND the plain df_entries store).
                // Writebacks elsewhere use the total `set` / `store_bag_set`.
                let set_fid = if value_is_bag(&type_args[1], ctx.program) {
                    Some(ctx.fids.bag_add)
                } else {
                    Some(ctx.fids.add)
                };
                if let Some(sfid) = set_fid {
                    let set_call = Expr::Call {
                        fun: sfid,
                        type_args: vec![type_args[0].clone(), type_args[1].clone()],
                        args: args.clone(),
                    };
                    let aug_uid = args[0].clone();
                    out.push(Stmt::Let {
                        pattern: pattern.clone(),
                        value: aug_uid,
                    });
                    out.push(Stmt::Eval(set_call));
                    continue;
                }
            }
        }
        // df remove: `let (node, uid') = remove(uid, k)` ->
        //   `let node = remove(uid, k)` (world-threaded by stage 4)
        //   `let uid' = uid` (the parent UID is unchanged in the World model;
        //   only `World.df_entries` shrinks). Without this, `field::remove`
        //   stays the un-world ghost native that returns a DEFAULT node, so
        //   skip_list/linked_table `remove` relinks with garbage and loops.
        if let Stmt::Let {
            pattern,
            value:
                Expr::Call {
                    fun,
                    type_args,
                    args,
                },
        } = &stmt
        {
            if df_op(ctx.program, ctx.df_mod, *fun) == Some(DfOp::Remove)
                && args.len() == 2
                && type_args.len() >= 2
                && !value_is_bag(&type_args[1], ctx.program)
            {
                let node_slot = pattern.first().cloned().flatten();
                let uid_slot = pattern.get(1).cloned().flatten();
                out.push(Stmt::Let {
                    pattern: vec![node_slot],
                    value: Expr::Call {
                        fun: ctx.fids.remove,
                        type_args: vec![type_args[0].clone(), type_args[1].clone()],
                        args: args.clone(),
                    },
                });
                if uid_slot.is_some() {
                    out.push(Stmt::Let {
                        pattern: vec![uid_slot],
                        value: args[0].clone(),
                    });
                }
                continue;
            }
        }
        // df remove_if_exists: `let (opt, uid') = remove_if_exists(uid, k)` ->
        //   `let opt__rie_h = has(uid, k)`
        //   `let opt = if opt__rie_h { option::some(store_remove_if_exists(uid, k)) }
        //              else { option::none() }`
        //   `let uid' = uid`.
        // Faithful for USED results too (the bytecode always binds the
        // Option at this stage; only stage-6 DCE later discards dead
        // ones). Never aborts: store_remove_if_exists has no companion,
        // and the presence-gated remove is total. option::some/none are
        // the translated MoveStdlib functions; if they're absent while a
        // remove_if_exists call exists, crash loudly (no fallback).
        if let Stmt::Let {
            pattern,
            value:
                Expr::Call {
                    fun,
                    type_args,
                    args,
                },
        } = &stmt
        {
            if df_op(ctx.program, ctx.df_mod, *fun) == Some(DfOp::RemoveIfExists)
                && args.len() == 2
                && type_args.len() >= 2
                && !value_is_bag(&type_args[1], ctx.program)
            {
                let (some_fid, none_fid) = ctx.option_fids.unwrap_or_else(|| {
                    panic!(
                        "dynamic_field::remove_if_exists routed but MoveStdlib \
                         option::some / option::none are not in the program"
                    )
                });
                let opt_slot = pattern.first().cloned().flatten();
                let uid_slot = pattern.get(1).cloned().flatten();
                let stem = opt_slot.as_deref().unwrap_or("rie");
                let hv: crate::ir::VarId = format!("{stem}__rie_h").into();
                out.push(Stmt::Let {
                    pattern: vec![Some(hv.clone())],
                    value: Expr::Call {
                        fun: ctx.fids.has,
                        type_args: vec![type_args[0].clone()],
                        args: args.clone(),
                    },
                });
                // The world-threading remove must sit in STATEMENT
                // position (stage 4 rejects GlobalMut calls nested in
                // expressions), so the then-branch hoists it to a Let.
                let rv: crate::ir::VarId = format!("{stem}__rie_v").into();
                let opt_value = Expr::If {
                    cond: Box::new(Expr::Var(hv)),
                    then_branch: Box::new(Block {
                        stmts: vec![Stmt::Let {
                            pattern: vec![Some(rv.clone())],
                            value: Expr::Call {
                                fun: ctx.fids.remove_if_exists,
                                type_args: vec![type_args[0].clone(), type_args[1].clone()],
                                args: args.clone(),
                            },
                        }],
                        tail: BlockTail::Value(Expr::Call {
                            fun: some_fid,
                            type_args: vec![type_args[1].clone()],
                            args: vec![Expr::Var(rv)],
                        }),
                    }),
                    else_branch: Box::new(Block {
                        stmts: Vec::new(),
                        tail: BlockTail::Value(Expr::Call {
                            fun: none_fid,
                            type_args: vec![type_args[1].clone()],
                            args: vec![],
                        }),
                    }),
                };
                match opt_slot {
                    Some(_) => out.push(Stmt::Let {
                        pattern: vec![opt_slot],
                        value: opt_value,
                    }),
                    None => out.push(Stmt::Eval(opt_value)),
                }
                if uid_slot.is_some() {
                    out.push(Stmt::Let {
                        pattern: vec![uid_slot],
                        value: args[0].clone(),
                    });
                }
                continue;
            }
        }
        // Hyper df writeback (escaping &mut-return through a df<K, Bag>):
        // mark it world-threaded. stage-4 then extends the let pattern
        // with `world` (like a world-returning call) and the renderer
        // emits a World store. The object value is unchanged; only
        // `world` is re-produced. (Simple in-function df ops are already
        // converted to store_*/store_bag_* Calls in the sites above.)
        if let Stmt::Let {
            value: Expr::WriteBack { edge, world, .. },
            ..
        } = &mut stmt
        {
            if world.is_none() && hyper_has_df_mapkey(edge, ctx.program) {
                *world = Some(crate::stage_04_effects::common::world_varid());
            }
        }
        out.push(stmt);
    }
    b.stmts = out;
    route_tail(&mut b.tail, ctx);
}

fn route_tail(t: &mut BlockTail, ctx: &RouteCtx) {
    match t {
        BlockTail::Value(e) => route_expr(e, ctx),
        BlockTail::Break { value, .. }
        | BlockTail::Continue { value, .. }
        | BlockTail::Return(value)
        | BlockTail::ReturnFromBlock { value, .. }
        | BlockTail::Abort { code: value } => route_expr(value, ctx),
    }
}

fn route_expr(e: &mut Expr, ctx: &RouteCtx) {
    route_expr_children_world(e, ctx);
    if let Expr::Call { fun, type_args, .. } = e {
        // bag-valued df -> store_bag_*; everything else (incl.
        // bag-CONTAINING structs, now legal TyCode df values) -> store_*.
        let vt_is_bag = type_args
            .get(1)
            .map_or(false, |vt| value_is_bag(vt, ctx.program));
        match df_op(ctx.program, ctx.df_mod, *fun) {
            Some(DfOp::Borrow) if vt_is_bag => *fun = ctx.fids.bag_borrow,
            Some(DfOp::Borrow) => *fun = ctx.fids.borrow,
            Some(DfOp::Exists) if vt_is_bag => {
                *fun = ctx.fids.bag_has;
                type_args.truncate(1);
            }
            Some(DfOp::Exists) => {
                *fun = ctx.fids.has;
                type_args.truncate(1);
            }
            _ => {}
        }
    }
}

fn route_expr_children_world(e: &mut Expr, ctx: &RouteCtx) {
    use Expr::*;
    match e {
        Expr::Borrow { step, base } => {
            for __pe in step.exprs_mut() {
                route_expr(__pe, ctx);
            }
            route_expr(base, ctx);
        }
        Expr::Update { step, base, value } => {
            for __pe in step.exprs_mut() {
                route_expr(__pe, ctx);
            }
            route_expr(base, ctx);
            route_expr(value, ctx);
        }
        Var(_)
        | Const(_)
        | Unit
        | BorrowLoc(_)
        | BorrowGlobal(_)
        | WriteBack { .. }
        | IsParent { .. }
        | BitOp(_) => {}
        BinOp { lhs, rhs, .. } => {
            route_expr(lhs, ctx);
            route_expr(rhs, ctx);
        }
        UnOp { operand, .. } => route_expr(operand, ctx),
        Call { args, .. } | Tuple(args) | Pack { fields: args, .. } => {
            for a in args.iter_mut() {
                route_expr(a, ctx);
            }
        }
        Unpack { value: inner, .. }
        | Field { base: inner, .. }
        | ReadRef(inner)
        | ToProp(inner)
        | ToBool(inner) => route_expr(inner, ctx),
        WriteRef { reference, value } => {
            route_expr(reference, ctx);
            route_expr(value, ctx);
        }
        If {
            cond,
            then_branch,
            else_branch,
        } => {
            route_expr(cond, ctx);
            route_block(then_branch, ctx);
            route_block(else_branch, ctx);
        }
        Match {
            selector, cases, ..
        } => {
            route_expr(selector, ctx);
            for arm in cases {
                route_block(&mut arm.body, ctx);
            }
        }
        While {
            header,
            cond,
            body,
            iter_locals,
            header_exit_locals: _,
            live_out: _,
        } => {
            route_block(header, ctx);
            route_expr(cond, ctx);
            route_block(body, ctx);
            for (_, init) in iter_locals.iter_mut() {
                route_expr(init, ctx);
            }
        }
        Quantifier { body, .. } => route_block(body, ctx),
        LabeledBlock { body, .. } => route_block(body, ctx),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::program::Struct;

    /// A program with one struct at id 0 carrying `qualified_name`, plus
    /// the `Type::Struct` referring to it.
    fn prog_with_struct(qualified_name: &str) -> (Program, Type) {
        let mut p = Program::default();
        p.structs.insert(
            0,
            Struct {
                module_id: 0,
                name: "S".to_string(),
                qualified_name: qualified_name.to_string(),
                type_params: vec![],
                fields: vec![],
                variants: None,
                is_native: false,
            },
        );
        (
            p,
            Type::Struct {
                struct_id: 0,
                type_args: vec![],
            },
        )
    }

    fn mut_ref(inner: Type) -> Type {
        Type::MutableRef {
            inner: Box::new(inner.clone()),
            root: Box::new(inner),
        }
    }

    #[test]
    fn value_is_bag_recognizes_bag_and_object_bag() {
        let (p, bag) = prog_with_struct("bag::Bag");
        assert!(value_is_bag(&bag, &p));
        let (p2, obag) = prog_with_struct("object_bag::ObjectBag");
        assert!(value_is_bag(&obag, &p2));
    }

    #[test]
    fn value_is_bag_sees_through_ref_mutref_vector() {
        let (p, bag) = prog_with_struct("bag::Bag");
        assert!(value_is_bag(&Type::Reference(Box::new(bag.clone())), &p));
        assert!(value_is_bag(&Type::Vector(Box::new(bag.clone())), &p));
        assert!(value_is_bag(&mut_ref(bag), &p));
    }

    #[test]
    fn value_is_bag_false_for_other_struct_and_scalar() {
        let (p, other) = prog_with_struct("foo::Other");
        assert!(!value_is_bag(&other, &p));
        assert!(!value_is_bag(&Type::UInt(64), &p));
    }

    #[test]
    fn is_uid_type_recognizes_uid_through_refs_only() {
        let (p, uid) = prog_with_struct("object::UID");
        assert!(is_uid_type(&uid, &p));
        assert!(is_uid_type(&Type::Reference(Box::new(uid.clone())), &p));
        assert!(is_uid_type(&mut_ref(uid), &p));
        let (p2, bag) = prog_with_struct("bag::Bag");
        assert!(!is_uid_type(&bag, &p2));
        assert!(!is_uid_type(&Type::UInt(64), &p2));
    }

    use crate::ir::program::Field;

    fn add_struct(p: &mut Program, id: StructId, qn: &str, fields: Vec<Field>) {
        p.structs.insert(
            id,
            Struct {
                module_id: 0,
                name: qn.rsplit("::").next().unwrap_or(qn).to_string(),
                qualified_name: qn.to_string(),
                type_params: vec![],
                fields,
                variants: None,
                is_native: false,
            },
        );
    }

    fn sty(id: StructId) -> Type {
        Type::Struct {
            struct_id: id,
            type_args: vec![],
        }
    }

    /// Build the sui-system `candidate_validator_mut` writeback path:
    ///   `ValidatorSet.validator_candidates[addr].inner.id -> df<u64, Validator>`
    /// i.e. a Table lookup (in-value native map) + struct fields in the
    /// prefix, then the Versioned dynamic-field anchor at the tail. The df
    /// `key_type` is threaded so the generic-key rejection can be exercised.
    fn candidate_shape_program() -> Program {
        let mut p = Program::default();
        add_struct(&mut p, 10, "object::UID", vec![]);
        // Table content placeholder: gate reads only its qualified_name.
        add_struct(&mut p, 1, "table::Table", vec![]);
        add_struct(
            &mut p,
            2,
            "versioned::Versioned",
            vec![Field {
                name: "id".to_string(),
                field_type: sty(10),
            }],
        );
        add_struct(&mut p, 3, "validator_wrapper::ValidatorWrapper", vec![]);
        add_struct(&mut p, 4, "validator_set::ValidatorSet", vec![]);
        add_struct(&mut p, 5, "validator::Validator", vec![]);
        p
    }

    fn candidate_shape_edge(df_key: Type) -> crate::ir::borrow::BorrowEdge {
        use crate::ir::borrow::BorrowEdge;
        BorrowEdge::Hyper(vec![
            BorrowEdge::StructField {
                struct_id: 4,
                field_index: 6,
            },
            // Table content placeholder (Table.size), preceding the addr key.
            BorrowEdge::StructField {
                struct_id: 1,
                field_index: 1,
            },
            BorrowEdge::MapKey {
                key_type: Type::Address,
                value_type: sty(3),
            },
            BorrowEdge::StructField {
                struct_id: 3,
                field_index: 0,
            },
            BorrowEdge::StructField {
                struct_id: 2,
                field_index: 0,
            },
            BorrowEdge::MapKey {
                key_type: df_key,
                value_type: sty(5),
            },
        ])
    }

    #[test]
    fn hyper_has_df_mapkey_accepts_table_prefixed_versioned_df() {
        // Regression (ledger item 31): the candidate-path df writeback was
        // dropped in the value face because this Table-mapKey-prefixed shape
        // was NOT world-threaded. It must now be marked for world-threading.
        let p = candidate_shape_program();
        assert!(hyper_has_df_mapkey(
            &candidate_shape_edge(Type::UInt(64)),
            &p
        ));
    }

    #[test]
    fn prefix_is_world_reconstructable_pins_candidate_prefix() {
        use crate::ir::borrow::BorrowEdge;
        let p = candidate_shape_program();
        // The prefix up to (not incl.) the df anchor at index 5.
        let edges = match candidate_shape_edge(Type::UInt(64)) {
            BorrowEdge::Hyper(es) => es,
            _ => unreachable!(),
        };
        assert!(prefix_is_world_reconstructable(&edges[..5], &p));
        // A VecIndex (non-recon container) in the prefix is rejected, keeping
        // that shape on the non-world path.
        let bad = vec![
            BorrowEdge::StructField {
                struct_id: 4,
                field_index: 6,
            },
            BorrowEdge::VecIndex,
        ];
        assert!(!prefix_is_world_reconstructable(&bad, &p));
    }

    #[test]
    fn hyper_has_df_mapkey_rejects_generic_df_key_with_map_prefix() {
        // The map-prefixed renderer arm binds AnyKey constructors with no
        // FromAnyKey bridge, so a generic df key with a map prefix must stay
        // off the world path (lockstep with the renderer's rejection).
        let p = candidate_shape_program();
        assert!(!hyper_has_df_mapkey(
            &candidate_shape_edge(Type::TypeParam(0)),
            &p
        ));
    }

    #[test]
    fn prefix_is_world_reconstructable_rejects_illtyped_map_value() {
        use crate::ir::borrow::BorrowEdge;
        // Mirror sui-system's `get_candidate_or_active_validator_mut`: the
        // Table lookup's value_type collapsed to the inner df's `Validator`
        // (id 5) instead of the `ValidatorWrapper` (id 3) whose `.inner` the
        // next edge reads. Rendering `Table.borrow` there would mistype, so it
        // must stay on the non-world path.
        let p = candidate_shape_program();
        let bad_prefix = vec![
            BorrowEdge::StructField {
                struct_id: 4,
                field_index: 6,
            },
            BorrowEdge::StructField {
                struct_id: 1,
                field_index: 1,
            },
            BorrowEdge::MapKey {
                key_type: Type::UInt(64),
                value_type: sty(5), // Validator, but next edge reads ValidatorWrapper(3)
            },
            BorrowEdge::StructField {
                struct_id: 3,
                field_index: 0,
            },
            BorrowEdge::StructField {
                struct_id: 2,
                field_index: 0,
            },
        ];
        assert!(!prefix_is_world_reconstructable(&bad_prefix, &p));
    }

    // `dynamic_field::exists_` became `exists` upstream. Left unrecognised it
    // was never routed to the World `has` model and rendered as a call to
    // `Dynamic_field.exists_`, which no native file defines (blast
    // `launch_config::add_partner`). Both spellings stay routed, since the
    // name a package sees depends on its pinned framework revision.
    #[test]
    fn df_op_routes_both_spellings_of_exists() {
        use crate::ir::{Block, BlockTail, Effects, Function, FunctionKind, Module, Signature};

        let mut p = Program::default();
        for (mid, name) in [
            (0, "dynamic_field"),
            (1, "dynamic_object_field"),
            (2, "bag"),
        ] {
            p.modules.insert(
                mid,
                Module {
                    name: name.to_string(),
                    package_name: "Sui".to_string(),
                    address: String::new(),
                    required_imports: Vec::new(),
                    is_native: false,
                },
            );
        }
        let mut next = 0;
        let mut declare = |p: &mut Program, module: usize, name: &str| {
            let fid = next;
            next += 1;
            p.functions.insert(
                fid,
                Function {
                    module,
                    name: name.to_string(),
                    signature: Signature {
                        type_params: Vec::new(),
                        params: Vec::new(),
                        return_type: Type::Bool,
                    },
                    body: Block {
                        stmts: Vec::new(),
                        tail: BlockTail::Value(Expr::Unit),
                    },
                    kind: FunctionKind::Source,
                    effects: Effects::PURE,
                    explicit_pure: false,
                },
            );
            fid
        };

        for module in [0, 1] {
            for name in ["exists", "exists_", "exists_with_type"] {
                let fid = declare(&mut p, module, name);
                assert!(
                    matches!(df_op(&p, 0, fid), Some(DfOp::Exists)),
                    "module {module} `{name}` must route as an existence check"
                );
            }
        }
        let elsewhere = declare(&mut p, 2, "exists");
        assert!(df_op(&p, 0, elsewhere).is_none());
    }
}
