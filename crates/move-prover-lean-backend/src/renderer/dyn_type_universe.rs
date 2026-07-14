// Backport of the new-pipeline closed-universe `TyCode` model to the legacy
// renderer. Models Sui's heterogeneous `bag::*` / `object_bag::*` storage
// (one Bag holds entries of arbitrary `(K, V)` pairs) via a per-project
// closed inductive `TyCode` plus `Universe` / `HasCode` instances, instead of
// the per-(K, V) ghost-field approach (which can't apply to a framework
// struct without forming an import cycle).
//
// Mirrors `lean-pipeline/src/render/dyn_type_universe.rs`; adapted to the
// legacy `intermediate_theorem_format` IR. See
// `plans/lean-pipeline/dynamic-typing-via-repr-design.md`.

use std::collections::{BTreeSet, HashSet};
use std::fs;
use std::path::Path;

use intermediate_theorem_format::{IRNode, Module, Program, Struct, StructID, Type};

use crate::escape;

/// A generic struct shape used as a "wrapping" in TyCode -- the struct id +
/// its arity. Distinct `(struct_id, arity)` pairs become distinct recursive
/// TyCode constructors.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct WrappingStruct {
    pub struct_id: StructID,
    pub arity: usize,
}

/// Full type universe for the project: concrete leaf types + generic wrapping
/// struct shapes encountered across all heterogeneous-storage call sites.
#[derive(Debug, Default)]
pub struct DynTypeUniverse {
    pub leaves: Vec<Type>,
    pub wrappings: Vec<WrappingStruct>,
}

/// Lemma / framework packages whose types are provided by the prelude
/// `natives/` tree (imported directly, never via a user `_Types` file).
fn is_system_package(pkg: &str) -> bool {
    matches!(
        pkg,
        "MoveStdlib" | "Sui" | "SuiSystem" | "DeepBook" | "Prover" | "Bridge"
    )
}

fn is_heterogeneous_container_qn(qn: &str) -> bool {
    qn == "bag::Bag" || qn == "object_bag::ObjectBag"
}

/// FunctionIDs of `sui::bag` / `sui::object_bag` operations.
fn bag_fn_ids(program: &Program) -> HashSet<usize> {
    let bag_module_ids: HashSet<usize> = program
        .modules
        .iter()
        .filter(|(_, m)| m.package_name == "Sui" && (m.name == "bag" || m.name == "object_bag"))
        .map(|(id, _)| *id)
        .collect();
    let type_name_module_ids: HashSet<usize> = program
        .modules
        .iter()
        .filter(|(_, m)| m.name == "type_name")
        .map(|(id, _)| *id)
        .collect();
    // Both bag ops and the `type_name::get`-family index the closed type
    // universe: their type-args must appear as `BagU` leaves so a `HasCode BagU`
    // instance is generated (bag stores `(K, V)`; `type_name::get<T>` derives
    // `T`'s FQN from `Universe.typeName`).
    program
        .functions
        .iter()
        .filter(|(_, f)| {
            bag_module_ids.contains(&f.module_id)
                || (type_name_module_ids.contains(&f.module_id)
                    && matches!(
                        f.name.as_str(),
                        "get" | "with_defining_ids" | "get_with_original_ids" | "with_original_ids"
                    ))
        })
        .map(|(id, _)| id)
        .collect()
}

/// True iff the program references the `Bag` / `ObjectBag` struct anywhere (as
/// a field or signature type, or via a bag operation). Whenever a Bag type is
/// rendered it becomes `Bag TyCode`, so the per-project `Generated/TyCode`
/// must exist even when the bag is only stored and never operated on (the
/// universe is then empty -- just `dummy`). Note this is broader than
/// `bag_fn_ids`: sui-system's `StakingPool` carries a `Bag` field but performs
/// no bag operations.
pub fn program_uses_bag(program: &Program) -> bool {
    program
        .structs
        .iter()
        .any(|(_, s)| is_heterogeneous_container_qn(&s.qualified_name))
}

/// Collect the BAG universe (`BagU`): the (K, V) types flowing into bag ops,
/// EXCLUDING bag-containing structs (a Bag cannot be a member of its own
/// universe without a file-level import cycle: `BagUInterp` would have to
/// import the struct's defining file, which needs `Universe BagU` for its
/// `Bag BagU` field).
pub fn collect(program: &Program) -> DynTypeUniverse {
    collect_impl(program, true)
}

/// Collect the DF universe (`TyCode`): same call-site collection, but
/// bag-containing structs are INCLUDED — their `Bag` fields are typed over the
/// separate `BagU` universe, so `TyCodeInterp -> <Mod>_types -> BagUInterp ->
/// skeletons` stays a DAG (the DfU/BagU split, unified-backend design §3.2).
/// Only `bag::Bag` / `object_bag::ObjectBag` themselves stay out (a bag stored
/// directly under a dynamic field is represented structurally as
/// `Prover.World.DfVal.bag`).
pub fn collect_df(program: &Program) -> DynTypeUniverse {
    collect_impl(program, false)
}

fn collect_impl(program: &Program, exclude_bag_containing: bool) -> DynTypeUniverse {
    let mut leaves: HashSet<Type> = HashSet::new();
    let mut wrappings: BTreeSet<WrappingStruct> = BTreeSet::new();

    // Collect the (K, V) types that flow into bag/object_bag calls. The bag
    // K/V types appear as the type-args of `bag::add<K, V>` etc. at the call
    // site. (Unlike the new pipeline we do NOT over-approximate to every
    // call's type-args: in the legacy backport only bag-using functions get
    // `[HasCode TyCode T]` constraints, so only bag-flowing types need a code.)
    let bag_fns = bag_fn_ids(program);
    // World-mode (Phase 1): types flowing through the `World.*` typed views
    // (df keys/values, transferred objects, emitted events) are DF-universe
    // members — the df lowering feeds `TyCode`, as the DfU/BagU split
    // anticipated. Bag universe membership is unaffected.
    let world_fns: HashSet<usize> = if !exclude_bag_containing {
        program
            .world_functions
            .as_ref()
            .map(|w| w.all_ids().into_iter().collect())
            .unwrap_or_default()
    } else {
        HashSet::new()
    };
    for (_, f) in program.functions.iter() {
        for node in f.body.iter() {
            if let IRNode::Call {
                function,
                type_args,
                ..
            } = node
            {
                if bag_fns.contains(function) || world_fns.contains(function) {
                    for t in type_args {
                        classify(t, program, &mut leaves, &mut wrappings);
                    }
                }
                // BagU transitive rule: a call into a function with
                // BagU-constrained type params (bag ops or `type_name::get`)
                // instantiates them here — the CONCRETE instantiations are BagU
                // members so their `HasCode BagU` instance is generated (generic
                // ones resolve at this caller's own call sites via the same
                // rule). Runs for both universes; `classify` ignores bare type
                // params, so generic call sites contribute nothing.
                if let Some(idx) = program.fn_bagu_params.get(function) {
                    for &i in idx {
                        if let Some(t) = type_args.get(i as usize) {
                            classify(t, program, &mut leaves, &mut wrappings);
                        }
                    }
                }
                if !bag_fns.contains(function)
                    && !world_fns.contains(function)
                    && !exclude_bag_containing
                {
                    // Generic state ops (Phase 5): a call into a function with
                    // HasCode-constrained type params instantiates them here —
                    // the CONCRETE instantiations are DF-universe members
                    // (generic ones resolve at this caller's own call sites,
                    // via this same rule on the caller). `classify` ignores
                    // bare type parameters.
                    if let Some(idx) = program.fn_hascode_params.get(function) {
                        for &i in idx {
                            if let Some(t) = type_args.get(i as usize) {
                                classify(t, program, &mut leaves, &mut wrappings);
                            }
                        }
                    }
                }
            }
        }
    }

    // Exclude `bag::Bag` / `object_bag::ObjectBag` from both universes. For
    // the bag universe additionally exclude any struct that (transitively)
    // contains one (see `collect` doc).
    let bag_containing = if exclude_bag_containing {
        collect_bag_containing_struct_ids(program)
    } else {
        HashSet::new()
    };
    let excluded = |sid: &StructID| -> bool {
        bag_containing.contains(sid)
            || program
                .structs
                .has(*sid)
                .then(|| is_heterogeneous_container_qn(&program.structs.get(sid).qualified_name))
                .unwrap_or(false)
    };
    wrappings.retain(|w| !excluded(&w.struct_id));
    leaves.retain(|t| match t {
        Type::Struct { struct_id, .. } => !excluded(struct_id),
        _ => true,
    });

    let mut leaf_vec: Vec<Type> = leaves.into_iter().collect();
    leaf_vec.sort_by(|a, b| mangle(a, program).cmp(&mangle(b, program)));
    DynTypeUniverse {
        leaves: leaf_vec,
        wrappings: wrappings.into_iter().collect(),
    }
}

/// True iff `mid` contains at least one Bag-containing struct (drives the
/// `_Types` / `_Types_Skeleton` file split that breaks the import cycle).
pub fn module_has_bag_struct(program: &Program, mid: usize) -> bool {
    let bag_ids = collect_bag_containing_struct_ids(program);
    program
        .structs
        .iter()
        .any(|(sid, s)| s.module_id == mid && bag_ids.contains(sid))
}

/// Set of `StructID`s whose fields (transitively) reference `bag::Bag` or
/// `object_bag::ObjectBag`.
pub fn collect_bag_containing_struct_ids(program: &Program) -> HashSet<StructID> {
    fn struct_ids_in_type(ty: &Type, out: &mut Vec<StructID>) {
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
            Type::Vector(inner) | Type::Reference(inner) | Type::Option(inner) => {
                struct_ids_in_type(inner, out)
            }
            Type::MutableReference(inner, state) => {
                struct_ids_in_type(inner, out);
                struct_ids_in_type(state, out);
            }
            Type::Tuple(ts) => {
                for t in ts {
                    struct_ids_in_type(t, out);
                }
            }
            _ => {}
        }
    }

    // Collect every struct id referenced by a struct's field types — including
    // ENUM VARIANT fields, which the import-dependency walk also traverses.
    // Missing variant fields here would misclassify an enum whose bag lives in a
    // variant as bag-free, landing it in a skeleton that then references a
    // bag-bearing struct and reintroduces a `TyCodeInterp` import cycle.
    fn struct_field_deps(s: &Struct, out: &mut Vec<StructID>) {
        for f in &s.fields {
            struct_ids_in_type(&f.field_type, out);
        }
        if let Some(variants) = &s.variants {
            for v in variants {
                for f in &v.fields {
                    struct_ids_in_type(&f.field_type, out);
                }
            }
        }
    }

    let is_container = |sid: &StructID| -> bool {
        program.structs.has(*sid)
            && is_heterogeneous_container_qn(&program.structs.get(sid).qualified_name)
    };

    let mut tainted: HashSet<StructID> = HashSet::new();
    for (sid, s) in program.structs.iter() {
        let mut deps = Vec::new();
        struct_field_deps(s, &mut deps);
        if deps.iter().any(is_container) {
            tainted.insert(*sid);
        }
    }
    // Transitive closure: a struct containing a tainted struct is tainted.
    let mut changed = true;
    while changed {
        changed = false;
        for (sid, s) in program.structs.iter() {
            if tainted.contains(sid) {
                continue;
            }
            let mut deps = Vec::new();
            struct_field_deps(s, &mut deps);
            if deps.iter().any(|d| tainted.contains(d)) {
                tainted.insert(*sid);
                changed = true;
            }
        }
    }
    tainted
}

/// Classify `ty`: concrete struct (0 type-args) / primitive / concrete vector
/// => leaf; generic struct => wrapping shape + recurse into args.
pub fn classify(
    ty: &Type,
    program: &Program,
    leaves: &mut HashSet<Type>,
    wrappings: &mut BTreeSet<WrappingStruct>,
) {
    match ty {
        Type::Bool | Type::UInt(_) | Type::Address => {
            leaves.insert(ty.clone());
        }
        Type::Prop | Type::MoveAbort => {}
        Type::TypeParameter(_) => {}
        Type::Vector(inner) => {
            if is_concrete(inner) {
                leaves.insert(ty.clone());
            } else {
                classify(inner, program, leaves, wrappings);
            }
        }
        Type::Option(inner) | Type::Reference(inner) => classify(inner, program, leaves, wrappings),
        Type::MutableReference(inner, state) => {
            classify(inner, program, leaves, wrappings);
            classify(state, program, leaves, wrappings);
        }
        Type::Tuple(ts) => {
            for t in ts {
                classify(t, program, leaves, wrappings);
            }
        }
        Type::Struct {
            struct_id,
            type_args,
        } => {
            if type_args.is_empty() {
                leaves.insert(ty.clone());
            } else {
                wrappings.insert(WrappingStruct {
                    struct_id: *struct_id,
                    arity: type_args.len(),
                });
                for arg in type_args {
                    classify(arg, program, leaves, wrappings);
                }
            }
        }
    }
}

fn is_concrete(ty: &Type) -> bool {
    match ty {
        Type::Bool | Type::Prop | Type::UInt(_) | Type::Address | Type::MoveAbort => true,
        Type::TypeParameter(_) => false,
        Type::Vector(inner) | Type::Reference(inner) | Type::Option(inner) => is_concrete(inner),
        Type::MutableReference(inner, state) => is_concrete(inner) && is_concrete(state),
        Type::Tuple(ts) => ts.iter().all(is_concrete),
        Type::Struct { type_args, .. } => type_args.iter().all(is_concrete),
    }
}

// ---------------------------------------------------------------------------
// Mangling: collision-free TyCode constructor names.
// ---------------------------------------------------------------------------

pub fn mangle(ty: &Type, program: &Program) -> String {
    let mut s = String::new();
    mangle_into(ty, program, &mut s);
    s
}

fn mangle_into(ty: &Type, program: &Program, out: &mut String) {
    match ty {
        Type::Bool => out.push_str("bool"),
        Type::Prop => out.push_str("prop"),
        Type::UInt(n) => out.push_str(&format!("u{}", n)),
        Type::Address => out.push_str("address"),
        Type::MoveAbort => out.push_str("moveabort"),
        Type::Vector(inner) => {
            out.push_str("vec_");
            mangle_into(inner, program, out);
        }
        Type::Reference(inner) => mangle_into(inner, program, out),
        Type::Option(inner) => {
            out.push_str("opt_");
            mangle_into(inner, program, out);
        }
        Type::MutableReference(inner, _) => {
            out.push_str("mut_");
            mangle_into(inner, program, out);
        }
        Type::TypeParameter(i) => out.push_str(&format!("tp{}", i)),
        Type::Tuple(ts) => {
            out.push_str("tup");
            for t in ts {
                out.push('_');
                mangle_into(t, program, out);
            }
        }
        Type::Struct {
            struct_id,
            type_args,
        } => {
            if program.structs.has(*struct_id) {
                out.push_str(&struct_mangle_prefix(*struct_id, program));
                for arg in type_args {
                    out.push_str("_X_");
                    mangle_into(arg, program, out);
                }
            } else {
                out.push_str(&format!("sid{}", struct_id));
            }
        }
    }
}

/// `<module>__<Name>` for system-package structs, `<Package>__<module>__<Name>`
/// for user structs -- mirrors namespace uniqueness so colliding bare
/// `module::Name` pairs across packages get distinct constructors.
fn struct_mangle_prefix(struct_id: StructID, program: &Program) -> String {
    if !program.structs.has(struct_id) {
        return format!("sid{}", struct_id);
    }
    let s = program.structs.get(&struct_id);
    let qn = s.qualified_name.replace("::", "__");
    let pkg = if program.modules.has(s.module_id) {
        program.modules.get(&s.module_id).package_name.clone()
    } else {
        String::new()
    };
    if pkg.is_empty() || is_system_package(&pkg) {
        qn
    } else {
        format!("{}__{}", pkg.replace("::", "__"), qn)
    }
}

pub fn wrapping_ctor_name(w: &WrappingStruct, program: &Program) -> String {
    if program.structs.has(w.struct_id) {
        let mut name = struct_mangle_prefix(w.struct_id, program);
        for _ in 0..w.arity {
            name.push_str("_X_t");
        }
        name
    } else {
        format!("sid{}_X_arity{}", w.struct_id, w.arity)
    }
}

// ---------------------------------------------------------------------------
// Fully-qualified Move type names (for `Universe.typeName`).
// ---------------------------------------------------------------------------

fn struct_base_fqn(struct_id: StructID, program: &Program) -> String {
    if !program.structs.has(struct_id) {
        return format!("sid{}", struct_id);
    }
    program.structs.get(&struct_id).qualified_name.clone()
}

pub fn leaf_fqn(ty: &Type, program: &Program) -> String {
    match ty {
        Type::Bool => "bool".to_string(),
        Type::UInt(n) => format!("u{}", n),
        Type::Address => "address".to_string(),
        Type::Vector(inner) => format!("vector<{}>", leaf_fqn(inner, program)),
        Type::Reference(inner) | Type::MutableReference(inner, _) | Type::Option(inner) => {
            leaf_fqn(inner, program)
        }
        Type::TypeParameter(i) => format!("tp{}", i),
        Type::Tuple(_) | Type::Prop | Type::MoveAbort => "unit".to_string(),
        Type::Struct {
            struct_id,
            type_args,
        } => {
            let base = struct_base_fqn(*struct_id, program);
            if type_args.is_empty() {
                base
            } else {
                let args = type_args
                    .iter()
                    .map(|a| leaf_fqn(a, program))
                    .collect::<Vec<_>>()
                    .join(", ");
                format!("{}<{}>", base, args)
            }
        }
    }
}

fn lean_str(s: &str) -> String {
    s.replace('\\', "\\\\").replace('"', "\\\"")
}

/// If `ty` is a `key` object struct — one whose field 0 is a
/// `sui::object::UID` — return the escaped name of that field. Used to emit
/// the `Universe.uidNat` projection (`o.<field>.id.bytes.bytes.val`) for
/// world-mode generic-object keying. Non-struct or non-`key` leaves return
/// `None` (their `uidNat` is `0`).
fn leaf_uid_field(ty: &Type, program: &Program) -> Option<String> {
    let Type::Struct { struct_id, .. } = ty else {
        return None;
    };
    struct_uid_field(*struct_id, program)
}

/// Struct-id keyed variant of `leaf_uid_field`'s field-0-is-`UID` check. The
/// check is purely structural (field types, not type args), so it applies
/// unchanged to generic wrapping structs (`Vault<T,R>`, `Coin<T>`) — used so
/// `TyCode.uidNat`'s `wrappings` arm can key `key`-object generics by their
/// real UID instead of unconditionally falling back to `0`.
fn struct_uid_field(struct_id: StructID, program: &Program) -> Option<String> {
    if !program.structs.has(struct_id) {
        return None;
    }
    let s = program.structs.get(&struct_id);
    let f0 = s.fields.first()?;
    if let Type::Struct { struct_id: fsid, .. } = &f0.field_type {
        if program.structs.has(*fsid) && program.structs.get(fsid).name == "UID" {
            return Some(crate::escape::escape_identifier(&f0.name).to_string());
        }
    }
    None
}

/// The `import` line a `Generated/*Interp.lean` file needs in order to bring
/// a struct defined in module `mid` into scope. No package-based filtering:
/// the interp file is its own lib and must import the file that DEFINES each
/// type it names. The defining file depends on the module's shape:
///   * native module  -> `<Pkg>.<Stem>Natives`
///   * bag-free struct of a bag-bearing module -> `<Pkg>.<Stem>_types_skeleton`
///     (the bag-free half of the split)
///   * bag-CONTAINING struct (DF universe only) -> `<Pkg>.<Stem>_types` (the
///     bag-bearing half; it imports `Generated.BagUInterp`, never
///     `TyCodeInterp`, so this stays acyclic)
///   * otherwise -> `<Pkg>.<Stem>` (the module file; transitively re-exports a
///     `_types` split if any)
fn universe_struct_import(
    program: &Program,
    struct_id: StructID,
    tci_stems: &std::collections::HashSet<String>,
    bag_containing: &HashSet<StructID>,
    native_struct_keys: &HashSet<(usize, String)>,
) -> Option<String> {
    let mid = program.structs.get(&struct_id).module_id;
    if !program.modules.has(mid) {
        return None;
    }
    let m = program.modules.get(&mid);
    let pkg = if m.package_name.is_empty() {
        "Lean".to_string()
    } else {
        m.package_name.clone()
    };
    if m.is_native {
        let stem = super::program_renderer::get_namespace_file_stem(program, mid);
        return Some(format!("import {}.{}Natives", pkg, stem));
    }
    // A NATIVE STRUCT of an otherwise-non-native module (e.g. `Bag.Bag`) lives
    // in the hand-written `*Natives` file, never in any generated `_types`
    // split — resolve it there directly (mirrors `struct_defining_import`).
    if native_struct_keys.contains(&(mid, program.structs.get(&struct_id).name.clone())) {
        let stem = super::program_renderer::get_namespace_file_stem(program, mid);
        return Some(format!("import {}.{}Natives", pkg, stem));
    }
    let stem = program.module_to_file.get(&mid).map(|(_, s)| s.clone())?;
    if module_has_bag_struct(program, mid) {
        if bag_containing.contains(&struct_id) {
            Some(format!("import {}.{}_types", pkg, stem))
        } else {
            Some(format!("import {}.{}_types_skeleton", pkg, stem))
        }
    } else if tci_stems.contains(&stem) {
        // No bag-bearing struct, but the module file imports `BagUInterp`
        // (e.g. a `*_tests` module whose bodies use bags): its structs live in
        // the bag-free `_types` split, so importing them here stays acyclic.
        Some(format!("import {}.{}_types", pkg, stem))
    } else {
        Some(format!("import {}.{}", pkg, stem))
    }
}

/// Collect the `import` lines an interp file needs for every struct
/// referenced by a type.
fn collect_referenced_modules(
    ty: &Type,
    program: &Program,
    tci_stems: &std::collections::HashSet<String>,
    bag_containing: &HashSet<StructID>,
    native_struct_keys: &HashSet<(usize, String)>,
    out: &mut BTreeSet<String>,
) {
    match ty {
        Type::Struct {
            struct_id,
            type_args,
        } => {
            if program.structs.has(*struct_id) {
                if let Some(line) = universe_struct_import(
                    program,
                    *struct_id,
                    tci_stems,
                    bag_containing,
                    native_struct_keys,
                ) {
                    out.insert(line);
                }
            }
            for a in type_args {
                collect_referenced_modules(
                    a,
                    program,
                    tci_stems,
                    bag_containing,
                    native_struct_keys,
                    out,
                );
            }
        }
        Type::Vector(inner) | Type::Reference(inner) | Type::Option(inner) => {
            collect_referenced_modules(
                inner,
                program,
                tci_stems,
                bag_containing,
                native_struct_keys,
                out,
            )
        }
        Type::MutableReference(inner, state) => {
            collect_referenced_modules(
                inner,
                program,
                tci_stems,
                bag_containing,
                native_struct_keys,
                out,
            );
            collect_referenced_modules(
                state,
                program,
                tci_stems,
                bag_containing,
                native_struct_keys,
                out,
            );
        }
        Type::Tuple(ts) => {
            for t in ts {
                collect_referenced_modules(
                    t,
                    program,
                    tci_stems,
                    bag_containing,
                    native_struct_keys,
                    out,
                );
            }
        }
        _ => {}
    }
}

// ---------------------------------------------------------------------------
// DecidableEq derive closure: the `Universe.decEqInterp` field requires
// `DecidableEq` at every interpreted type. Generated structs only derive
// `BEq`, so each interp file post-hoc-derives `DecidableEq` for every
// GENERATED struct in the transitive field closure of its members (in
// dependency order). Native structs are expected to carry instances in their
// hand-written `*Natives.lean` (a missing one fails the lake build loudly --
// no fallback).
// ---------------------------------------------------------------------------

fn type_struct_ids_rec(ty: &Type, out: &mut Vec<StructID>) {
    match ty {
        Type::Struct {
            struct_id,
            type_args,
        } => {
            out.push(*struct_id);
            for a in type_args {
                type_struct_ids_rec(a, out);
            }
        }
        Type::Vector(inner) | Type::Reference(inner) | Type::Option(inner) => {
            type_struct_ids_rec(inner, out)
        }
        Type::MutableReference(inner, state) => {
            type_struct_ids_rec(inner, out);
            type_struct_ids_rec(state, out);
        }
        Type::Tuple(ts) => {
            for t in ts {
                type_struct_ids_rec(t, out);
            }
        }
        _ => {}
    }
}

/// Structs in the transitive field closure of `universe`'s member types,
/// topologically ordered so each `deriving instance DecidableEq for ...` line
/// sees its field instances. NATIVE structs are included too: their
/// hand-written declarations only derive `BEq`, and deriving `DecidableEq` at
/// the natives file is impossible when a native's field is a GENERATED struct
/// (`TypeName.name : Ascii.MoveString`) that has no instance yet at natives
/// compile time. Even `Bag`/`ObjectBag` are included when reachable (a
/// bag-CONTAINING DF-universe member's derive needs `DecidableEq (Bag BagU)`);
/// their `Entry` field instance lives in the prelude.
pub fn decidable_eq_derive_targets(
    universe: &DynTypeUniverse,
    program: &Program,
    _native_struct_keys: &HashSet<(usize, String)>,
) -> Vec<StructID> {
    let is_generated = |sid: &StructID| -> bool {
        if !program.structs.has(*sid) {
            return false;
        }
        let _ = program.structs.get(sid);
        true
    };

    let mut seed: Vec<StructID> = Vec::new();
    for leaf in &universe.leaves {
        type_struct_ids_rec(leaf, &mut seed);
    }
    for w in &universe.wrappings {
        seed.push(w.struct_id);
    }

    // DFS postorder over field deps => topological order (deps first).
    let mut visited: HashSet<StructID> = HashSet::new();
    let mut ordered: Vec<StructID> = Vec::new();
    fn visit(
        sid: StructID,
        program: &Program,
        is_generated: &dyn Fn(&StructID) -> bool,
        visited: &mut HashSet<StructID>,
        ordered: &mut Vec<StructID>,
    ) {
        if visited.contains(&sid) || !is_generated(&sid) {
            return;
        }
        visited.insert(sid);
        let s = program.structs.get(&sid);
        let mut deps: Vec<StructID> = Vec::new();
        for f in &s.fields {
            type_struct_ids_rec(&f.field_type, &mut deps);
        }
        if let Some(variants) = &s.variants {
            for v in variants {
                for f in &v.fields {
                    type_struct_ids_rec(&f.field_type, &mut deps);
                }
            }
        }
        for d in deps {
            visit(d, program, is_generated, visited, ordered);
        }
        ordered.push(sid);
    }
    for sid in seed {
        visit(sid, program, &is_generated, &mut visited, &mut ordered);
    }
    ordered
}

/// `_root_.<Namespace>.<Name>` path for any struct (leaf or wrapping base).
fn struct_lean_path(struct_id: StructID, program: &Program) -> String {
    let s = program.structs.get(&struct_id);
    let namespace = super::program_renderer::get_namespace(program, s.module_id);
    format!(
        "_root_.{}.{}",
        namespace,
        escape::escape_struct_name(&s.name)
    )
}

// ---------------------------------------------------------------------------
// Emission: Generated/{TyCode,BagU}.lean and Generated/{TyCode,BagU}Interp.lean.
// TyCode is the DF universe (bag-containing structs included); BagU is the bag
// universe (`Bag`/`ObjectBag` are rendered as `Bag BagU`).
// ---------------------------------------------------------------------------

fn write_universe_inductive_file(
    name: &str,
    universe: &DynTypeUniverse,
    program: &Program,
    output_dir: &Path,
    written: &mut crate::WrittenFiles,
) -> anyhow::Result<()> {
    let gen_dir = output_dir.join("Generated");
    fs::create_dir_all(&gen_dir)?;
    let path = gen_dir.join(format!("{}.lean", name));
    let mut out = String::new();
    out.push_str("-- Generated per project by the lean-backend renderer.\n");
    out.push_str("-- See `lean-backend/docs/unified-backend-design.md` (DfU/BagU split).\n");
    out.push_str("--\n");
    out.push_str("-- Bare inductive only. Interp + Universe + HasCode instances\n");
    out.push_str(&format!("-- live in Generated/{}Interp.lean.\n\n", name));
    out.push_str(&format!("inductive {} where\n", name));
    out.push_str("  | dummy\n");
    for leaf in &universe.leaves {
        out.push_str(&format!("  | {}\n", mangle(leaf, program)));
    }
    for w in &universe.wrappings {
        let stem = wrapping_ctor_name(w, program);
        let args: String = (0..w.arity)
            .map(|i| format!(" (a{} : {})", i, name))
            .collect();
        out.push_str(&format!("  | {}{}\n", stem, args));
    }
    out.push_str("  deriving DecidableEq, Repr\n");
    crate::write_if_changed(&path, &out, written)?;
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn write_universe_interp_file(
    name: &str,
    universe: &DynTypeUniverse,
    derive_targets: &[StructID],
    extra_imports: &[&str],
    bag_containing: &HashSet<StructID>,
    native_struct_keys: &HashSet<(usize, String)>,
    program: &Program,
    output_dir: &Path,
    written: &mut crate::WrittenFiles,
) -> anyhow::Result<()> {
    let gen_dir = output_dir.join("Generated");
    fs::create_dir_all(&gen_dir)?;
    let path = gen_dir.join(format!("{}Interp.lean", name));

    let mut out = String::new();
    out.push_str("-- Generated per project by the lean-backend renderer.\n");
    out.push_str("-- See `lean-backend/docs/unified-backend-design.md` (DfU/BagU split).\n\n");

    out.push_str("import Prelude.BoundedNat\n");
    out.push_str("import Prelude.Universe\n");
    out.push_str(&format!("import Generated.{}\n", name));
    for line in extra_imports {
        out.push_str(line);
        out.push('\n');
    }

    // Import the file that DEFINES every referenced struct (leaf, wrapping
    // base, or derive-closure member).
    let tci_stems =
        super::program_renderer::tycodeinterp_importing_stems(program, native_struct_keys);
    let mut imports: BTreeSet<String> = BTreeSet::new();
    for t in &universe.leaves {
        collect_referenced_modules(
            t,
            program,
            &tci_stems,
            bag_containing,
            native_struct_keys,
            &mut imports,
        );
    }
    for w in &universe.wrappings {
        collect_referenced_modules(
            &Type::Struct {
                struct_id: w.struct_id,
                type_args: vec![],
            },
            program,
            &tci_stems,
            bag_containing,
            native_struct_keys,
            &mut imports,
        );
    }
    for sid in derive_targets {
        collect_referenced_modules(
            &Type::Struct {
                struct_id: *sid,
                type_args: vec![],
            },
            program,
            &tci_stems,
            bag_containing,
            native_struct_keys,
            &mut imports,
        );
    }
    for line in &imports {
        out.push_str(line);
        out.push('\n');
    }
    out.push('\n');

    // Post-hoc DecidableEq derives for generated structs in the member
    // closure (`Universe.decEqInterp` needs them; generated structs only
    // derive `BEq` at declaration).
    if !derive_targets.is_empty() {
        for sid in derive_targets {
            out.push_str(&format!(
                "deriving instance DecidableEq for {}\n",
                struct_lean_path(*sid, program)
            ));
        }
        out.push('\n');
    }

    // interp
    out.push_str(&format!("abbrev {}.interp : {} -> Type\n", name, name));
    out.push_str("  | .dummy => Unit\n");
    for leaf in &universe.leaves {
        let stem = mangle(leaf, program);
        let ty_str = super::type_renderer::type_to_string(leaf, program, None);
        out.push_str(&format!("  | .{} => {}\n", stem, ty_str));
    }
    for w in &universe.wrappings {
        let stem = wrapping_ctor_name(w, program);
        let struct_path = wrapping_struct_path(w, program);
        let pat: String = (0..w.arity).map(|i| format!(" a{}", i)).collect();
        let interp_args: String = (0..w.arity)
            .map(|i| format!(" ({}.interp a{})", name, i))
            .collect();
        out.push_str(&format!(
            "  | .{}{} => {}{}\n",
            stem, pat, struct_path, interp_args
        ));
    }
    out.push('\n');

    // decEqInterp
    out.push_str(&format!(
        "def {}.decEqInterp : \u{2200} u : {}, DecidableEq ({}.interp u)\n",
        name, name, name
    ));
    out.push_str("  | .dummy => inferInstance\n");
    for leaf in &universe.leaves {
        out.push_str(&format!(
            "  | .{} => inferInstance\n",
            mangle(leaf, program)
        ));
    }
    for w in &universe.wrappings {
        let stem = wrapping_ctor_name(w, program);
        let pat: String = (0..w.arity).map(|i| format!(" a{}", i)).collect();
        out.push_str(&format!("  | .{}{} =>\n", stem, pat));
        for i in 0..w.arity {
            out.push_str(&format!(
                "    have : DecidableEq ({0}.interp a{1}) := {0}.decEqInterp a{1}\n",
                name, i
            ));
        }
        out.push_str("    inferInstance\n");
    }
    out.push('\n');

    // typeName
    out.push_str(&format!(
        "def {}.typeName : {} \u{2192} String\n",
        name, name
    ));
    out.push_str("  | .dummy => \"dummy\"\n");
    for leaf in &universe.leaves {
        out.push_str(&format!(
            "  | .{} => \"{}\"\n",
            mangle(leaf, program),
            lean_str(&leaf_fqn(leaf, program))
        ));
    }
    for w in &universe.wrappings {
        let stem = wrapping_ctor_name(w, program);
        let pat: String = (0..w.arity).map(|i| format!(" a{}", i)).collect();
        let base = lean_str(&struct_base_fqn(w.struct_id, program));
        let args: String = (0..w.arity)
            .map(|i| format!("{}.typeName a{}", name, i))
            .collect::<Vec<_>>()
            .join(" ++ \", \" ++ ");
        out.push_str(&format!(
            "  | .{}{} => \"{}<\" ++ {} ++ \">\"\n",
            stem, pat, base, args
        ));
    }
    out.push('\n');

    // uidNat: object-UID-as-Nat for `key`-object leaves; 0 otherwise. Lets
    // world-mode key a GENERIC object (`transfer::*` / `test_scenario::return_*`
    // over `T: key`) into the World store without structural field projection.
    out.push_str(&format!(
        "def {}.uidNat : (u : {}) \u{2192} {}.interp u \u{2192} Nat\n",
        name, name, name
    ));
    out.push_str("  | .dummy => fun _ => 0\n");
    for leaf in &universe.leaves {
        let stem = mangle(leaf, program);
        if let Some(fld) = leaf_uid_field(leaf, program) {
            out.push_str(&format!(
                "  | .{} => fun o => o.{}.id.bytes.bytes.val\n",
                stem, fld
            ));
        } else {
            out.push_str(&format!("  | .{} => fun _ => 0\n", stem));
        }
    }
    for w in &universe.wrappings {
        let stem = wrapping_ctor_name(w, program);
        let pat: String = (0..w.arity).map(|_| " _".to_string()).collect();
        if let Some(fld) = struct_uid_field(w.struct_id, program) {
            out.push_str(&format!(
                "  | .{}{} => fun o => o.{}.id.bytes.bytes.val\n",
                stem, pat, fld
            ));
        } else {
            out.push_str(&format!("  | .{}{} => fun _ => 0\n", stem, pat));
        }
    }
    out.push('\n');

    // Universe instance
    out.push_str(&format!("instance : Universe {} where\n", name));
    out.push_str("  decEq       := inferInstance\n");
    out.push_str(&format!("  interp      := {}.interp\n", name));
    out.push_str(&format!("  decEqInterp := {}.decEqInterp\n", name));
    out.push_str(&format!("  typeName    := {}.typeName\n", name));
    out.push_str(&format!("  uidNat      := {}.uidNat\n\n", name));

    // Concrete HasCode instances for leaves.
    for leaf in &universe.leaves {
        let stem = mangle(leaf, program);
        let ty_str = super::type_renderer::type_to_string(leaf, program, None);
        out.push_str(&format!(
            "instance : HasCode {} ({}) := \u{27E8}.{}, rfl\u{27E9}\n",
            name, ty_str, stem
        ));
    }

    // Derived HasCode instances for wrappings.
    for w in &universe.wrappings {
        let stem = wrapping_ctor_name(w, program);
        let struct_path = wrapping_struct_path(w, program);
        let constraints: String = (0..w.arity)
            .map(|i| format!(" [hc{0} : HasCode {1} T{0}]", i, name))
            .collect();
        let type_params_intro: String = (0..w.arity)
            .map(|i| format!(" {{T{} : Type}}", i))
            .collect();
        let applied_types: String = (0..w.arity).map(|i| format!(" T{}", i)).collect();
        let ctor_args: String = (0..w.arity).map(|i| format!(" hc{}.code", i)).collect();
        let show_args: String = (0..w.arity)
            .map(|i| format!(" (Universe.interp hc{}.code)", i))
            .collect();
        let rw_args: String = (0..w.arity)
            .map(|i| format!("hc{}.proof", i))
            .collect::<Vec<_>>()
            .join(", ");
        out.push_str(&format!(
            "\ninstance{cs_ty}{cs}: HasCode {un} ({sp}{ats}) where\n  code := .{stem}{ca}\n  proof := by show {sp}{sa} = {sp}{ats}; rw [{rw}]\n",
            cs_ty = type_params_intro,
            cs = constraints,
            un = name,
            sp = struct_path,
            ats = applied_types,
            stem = stem,
            ca = ctor_args,
            sa = show_args,
            rw = rw_args,
        ));
    }

    crate::write_if_changed(&path, &out, written)?;
    Ok(())
}

/// Emit all four universe files. `TyCode` (DF universe) additionally imports
/// `Generated.BagUInterp` and skips derive targets already derived there.
pub fn write_universes(
    program: &Program,
    output_dir: &Path,
    native_struct_keys: &HashSet<(usize, String)>,
    written: &mut crate::WrittenFiles,
) -> anyhow::Result<()> {
    let bag_universe = collect(program);
    let df_universe = collect_df(program);
    let bag_containing = collect_bag_containing_struct_ids(program);

    let bag_targets = decidable_eq_derive_targets(&bag_universe, program, native_struct_keys);
    let df_targets_all = decidable_eq_derive_targets(&df_universe, program, native_struct_keys);
    let bag_set: HashSet<StructID> = bag_targets.iter().copied().collect();
    let df_targets: Vec<StructID> = df_targets_all
        .into_iter()
        .filter(|sid| !bag_set.contains(sid))
        .collect();

    write_universe_inductive_file("BagU", &bag_universe, program, output_dir, written)?;
    write_universe_interp_file(
        "BagU",
        &bag_universe,
        &bag_targets,
        &[],
        &bag_containing,
        native_struct_keys,
        program,
        output_dir,
        written,
    )?;
    write_universe_inductive_file("TyCode", &df_universe, program, output_dir, written)?;
    write_universe_interp_file(
        "TyCode",
        &df_universe,
        &df_targets,
        &["import Generated.BagUInterp"],
        &bag_containing,
        native_struct_keys,
        program,
        output_dir,
        written,
    )?;
    Ok(())
}

// ---------------------------------------------------------------------------
// World-mode: Generated/World.lean (unified-backend design Phase 1).
// ---------------------------------------------------------------------------

/// True iff module `mid` touches the World: a function signature mentions the
/// synthetic World struct or a body calls a `World.*` typed-view native.
/// Drives the `import Generated.World` injection — and the acyclicity
/// constraint that DF-universe member structs must be defined in modules that
/// do NOT themselves use the World (TyCodeInterp imports the defining module;
/// the world-using module imports Generated.World which imports TyCodeInterp).
pub fn module_uses_world(program: &Program, mid: usize) -> bool {
    let Some(world) = &program.world_functions else {
        return false;
    };
    let world_fn_ids: HashSet<usize> = world.all_ids().into_iter().collect();
    let world_sids: HashSet<StructID> = std::iter::once(world.struct_id).collect();
    let mentions_world = |ty: &Type| -> bool {
        let mut ids = Vec::new();
        fn rec(ty: &Type, out: &mut Vec<StructID>) {
            match ty {
                Type::Struct {
                    struct_id,
                    type_args,
                } => {
                    out.push(*struct_id);
                    for a in type_args {
                        rec(a, out);
                    }
                }
                Type::Vector(i) | Type::Reference(i) | Type::Option(i) => rec(i, out),
                Type::MutableReference(i, s) => {
                    rec(i, out);
                    rec(s, out);
                }
                Type::Tuple(ts) => {
                    for t in ts {
                        rec(t, out);
                    }
                }
                _ => {}
            }
        }
        rec(ty, &mut ids);
        ids.iter().any(|sid| world_sids.contains(sid))
    };
    for (_, f) in program.functions.iter() {
        if f.module_id != mid {
            continue;
        }
        if f.signature
            .parameters
            .iter()
            .any(|p| mentions_world(&p.param_type))
            || mentions_world(&f.signature.return_type)
            || f.body.calls().any(|fid| world_fn_ids.contains(&fid))
        {
            return true;
        }
    }
    false
}

/// Emit `Generated/World.lean`: the per-project `World` abbrev (World v2 over
/// the DF/Bag universes, events as typed `ValEntry` records) plus the
/// `World.*` typed-view wrappers the lowered generated code calls. The
/// wrappers take their type params explicitly (matching the renderer's
/// positional type-arg convention) and are `@[world_simp]` so proofs unfold
/// them straight onto the prelude round-trip laws.
pub fn write_world_file(
    program: &Program,
    output_dir: &Path,
    written: &mut crate::WrittenFiles,
) -> anyhow::Result<()> {
    let world = program
        .world_functions
        .as_ref()
        .expect("write_world_file requires world_functions");

    // Acyclicity with world-using defining modules is handled by the
    // `_types` split: `tycodeinterp_importing_stems` includes any module that
    // both defines a DF-universe member and uses World ops, so TyCodeInterp
    // imports the struct-only `_types` half, never the world-importing module
    // file.
    let _ = world;

    let gen_dir = output_dir.join("Generated");
    fs::create_dir_all(&gen_dir)?;
    let path = gen_dir.join("World.lean");

    let out = r#"-- Generated per project by the lean-backend renderer (world-mode pin).
-- See `lean-backend/docs/unified-backend-design.md` Phase 1.
--
-- `World` is the per-project instantiation of the prelude World v2 model:
-- events are typed `ValEntry TyCode` records, dynamic fields live in the
-- DF universe `TyCode`, inline bags in `BagU`. The `World.*` wrappers below
-- are the render targets of the `world_threading` lowering; they take their
-- type params explicitly (the renderer emits type args positionally) and are
-- `@[world_simp]` so proofs collapse them onto the prelude round-trip laws.

import Prelude.World
import Prelude.WorldSimp
import Sui.ObjectNatives
import Sui.BagNatives
import MoveStdlib.MoveOption
import Generated.TyCodeInterp

abbrev World := Prover.World.World (Prover.World.ValEntry TyCode) TyCode BagU

namespace World

@[world_simp] def uidNat (uid : Object.UID) : Nat := uid.id.bytes.bytes.val

@[world_simp] def getDf (K V : Type) [HasCode TyCode K] [HasCode TyCode V]
    (w : World) (uid : Object.UID) (k : K) : Option V :=
  Prover.World.World.getDf w (uidNat uid) k

@[world_simp] def setDf (K V : Type) [HasCode TyCode K] [HasCode TyCode V]
    (w : World) (uid : Object.UID) (k : K) (v : V) : World :=
  Prover.World.World.setDf w (uidNat uid) k v

@[world_simp] def eraseDf (K V : Type) [HasCode TyCode K] [HasCode TyCode V]
    (w : World) (uid : Object.UID) (k : K) : World :=
  Prover.World.World.eraseDf w (uidNat uid) k

@[world_simp] def hasDf (K : Type) [HasCode TyCode K]
    (w : World) (uid : Object.UID) (k : K) : Bool :=
  Prover.World.World.hasDf w (uidNat uid) k

@[world_simp] def hasDfTyped (K V : Type) [HasCode TyCode K] [HasCode TyCode V]
    (w : World) (uid : Object.UID) (k : K) : Bool :=
  (Prover.World.World.getDf w (uidNat uid) k (V := V)).isSome

-- Structural bag-df views: a `bag::Bag` value cannot be a `TyCode` universe
-- member, so `world_threading` routes df ops whose VALUE type is `Bag` here
-- instead of through the `HasCode`-typed views. The bag is stored as its raw
-- parts (`id`, `size`, `storage`) in the `DfVal.bag` arm and reconstructed on
-- read. Only the key type `K` is a universe member.
@[world_simp] def setDfBag (K : Type) [HasCode TyCode K]
    (w : World) (uid : Object.UID) (k : K) (b : Bag.Bag BagU) : World :=
  Prover.World.World.setDfBag w (uidNat uid) k b.id.id.bytes b.size b.storage

@[world_simp] def getDfBag (K : Type) [HasCode TyCode K]
    (w : World) (uid : Object.UID) (k : K) : Option (Bag.Bag BagU) :=
  match Prover.World.World.getDfBagParts w (uidNat uid) k with
  | some (id, size, storage) => some (Bag.Bag.ofParts ⟨⟨id⟩⟩ size storage)
  | none => none

@[world_simp] def hasDfBag (K : Type) [HasCode TyCode K]
    (w : World) (uid : Object.UID) (k : K) : Bool :=
  Prover.World.World.hasDfBag w (uidNat uid) k

@[world_simp] def eraseDfBag (K : Type) [HasCode TyCode K]
    (w : World) (uid : Object.UID) (k : K) : World :=
  Prover.World.World.eraseDf w (uidNat uid) k

-- Heterogeneous mutable phi unification (M1): a function returning
-- `&mut T` from BOTH a value-carried location (state `S`) and a
-- World-carried location (state `World`) returns `Mutable T (S × World)`;
-- each branch lifts its Mutable with the sibling state it leaves untouched.
@[reducible, world_simp] def mutLiftWorld (A S : Type) (m : Mutable A (World → World)) (s : S) :
    Mutable A (S × (World → World)) :=
  Mutable.mk m.val (fun v => (s, m.reconstruct v))

@[reducible, world_simp] def mutLiftState (A S : Type) (m : Mutable A S) (w : World) :
    Mutable A (S × (World → World)) :=
  Mutable.mk m.val (fun v => (m.reconstruct v, fun _ => w))

-- Single-line tuple projections (bundle substitution of destructured callee
-- results; implicit type args so call sites carry no explicit types).
@[reducible, world_simp] def pfst {A B : Type} (p : A × B) : A := p.1
@[reducible, world_simp] def psnd {A B : Type} (p : A × B) : B := p.2

@[world_simp] def putOwned (T : Type) [HasCode TyCode T]
    (w : World) (x : T) (recipient : Address) (uid : Object.UID) : World :=
  Prover.World.World.putOwned w recipient (uidNat uid) x

@[world_simp] def putShared (T : Type) [HasCode TyCode T]
    (w : World) (x : T) (uid : Object.UID) : World :=
  Prover.World.World.putShared w (uidNat uid) x

@[world_simp] def putFrozen (T : Type) [HasCode TyCode T]
    (w : World) (x : T) (uid : Object.UID) : World :=
  Prover.World.World.putFrozen w (uidNat uid) x

@[world_simp] def emitEvent (T : Type) [HasCode TyCode T]
    (w : World) (e : T) : World :=
  Prover.World.World.emit w (Prover.World.ValEntry.of e)

-- `memberUid` builds the `Object.UID` of a GENERIC `key` object from its
-- per-constructor `Universe.uidNat` projection. world-mode's transfer lowering
-- routes generic-object transfers (`T: key`) here because it can't project the
-- UID field of an abstract `T` structurally. `World.uidNat` round-trips this
-- back to the same key.
@[world_simp] def memberUid (T : Type) [HasCode TyCode T] (obj : T) : Object.UID :=
  { id := { bytes := Address.mk ⟨Universe.uidNatOf TyCode T obj % 2 ^ 256, Nat.mod_lt _ (by decide)⟩ } }

-- Transfer-marker reads (World-resident replacement for the retired
-- transfer spec-ghost slots; stamped by `putOwned`).
@[world_simp] def transferExists (w : World) : Bool :=
  Prover.World.World.transferExists w

@[world_simp] def lastTransfer (w : World) : Address :=
  Prover.World.World.lastTransfer w

-- test_scenario inventory reads: `putOwned` stores each transferred object in
-- the World keyed by `uidNat`; these views recover it by owner. `Object.ID`
-- and the World's `Nat` key round-trip through `uidNat`.
def natToId (n : Nat) : Object.ID := { bytes := Address.mk ⟨n % 2 ^ 256, Nat.mod_lt _ (by decide)⟩ }
def idToNat (id : Object.ID) : Nat := id.bytes.bytes.val

@[world_simp] def idsForAddress (T : Type) [HasCode TyCode T]
    (w : World) (account : Address) : List Object.ID :=
  (w.uidsOwnedByT T account).map natToId

@[world_simp] def mostRecentIdForAddress (T : Type) [HasCode TyCode T]
    (w : World) (account : Address) : MoveOption.MoveOption Object.ID :=
  match w.mostRecentOwnedByT T account with
  | some n => MoveOption.some Object.ID (natToId n)
  | none => MoveOption.none Object.ID

@[world_simp] def wasTakenFromAddress
    (w : World) (account : Address) (id : Object.ID) : Bool :=
  !(w.ownedBy account (idToNat id))

@[world_simp] def takeFromAddressById (T : Type) [HasCode TyCode T] [Inhabited T]
    (w : World) (id : Object.ID) : T × World :=
  w.takeObj T (idToNat id)

-- Shared-object custody: `share_object` stores under `.shared` ownership;
-- these views recover it. Type-filtered — distinct shared singletons of
-- different types coexist in one scenario.
@[world_simp] def mostRecentIdShared (T : Type) [HasCode TyCode T]
    (w : World) : MoveOption.MoveOption Object.ID :=
  match w.mostRecentShared T with
  | some n => MoveOption.some Object.ID (natToId n)
  | none => MoveOption.none Object.ID

@[world_simp] def wasTakenShared
    (w : World) (id : Object.ID) : Bool :=
  !(w.isShared (idToNat id))

@[world_simp] def takeSharedById (T : Type) [HasCode TyCode T] [Inhabited T]
    (w : World) (id : Object.ID) : T × World :=
  w.takeObj T (idToNat id)

-- `test_scenario::end_transaction`: reads and resets the per-tx user-event
-- counter that `emitEvent` bumps. Call sites pack the rest of
-- `TransactionEffects` from empty/default values (the world model does not
-- track created/written/deleted/transferred/shared/frozen object sets).
@[world_simp] def takeTxUserEvents (w : World) : BoundedNat (2^64) × World :=
  Prover.World.World.takeTxUserEvents w

-- Frame leaves over the wrappers (unified-backend design §5.4, Phase 4):
-- the per-function `frame_thm` combinator trees chain these so their steps
-- match the generated call shapes exactly (no wrapper unfolding in proofs).
-- Worlds and stored values are IMPLICIT — the elaborator infers them from
-- the goal by definitional unfolding of the (reducible) generated def, so
-- render-sensitive value expressions (WriteBack chains) are never copied
-- into proof terms. Only the uid/key footprint sources are explicit,
-- mirroring the rendered `dfFootprint` entries.

theorem frame_setDf (K V : Type) [HasCode TyCode K] [HasCode TyCode V]
    {w : World} (uid : Object.UID) (k : K) {v : V} :
    Prover.World.FrameDf w (World.setDf K V w uid k v)
      [Prover.World.DfKey.mk (World.uidNat uid) (Prover.World.KeyEntry.of k)] :=
  Prover.World.FrameDf.setDf w (World.uidNat uid) k v

theorem frame_eraseDf (K V : Type) [HasCode TyCode K] [HasCode TyCode V]
    {w : World} (uid : Object.UID) (k : K) :
    Prover.World.FrameDf w (World.eraseDf K V w uid k)
      [Prover.World.DfKey.mk (World.uidNat uid) (Prover.World.KeyEntry.of k)] :=
  Prover.World.FrameDf.eraseDf w (World.uidNat uid) k

theorem frame_putOwned (T : Type) [HasCode TyCode T]
    {w : World} {x : T} {recipient : Address} {uid : Object.UID} :
    Prover.World.FrameDf w (World.putOwned T w x recipient uid) [] :=
  Prover.World.FrameDf.step_df_eq (World.putOwned T w x recipient uid)
    (Prover.World.FrameDf.refl w) rfl

theorem frame_putShared (T : Type) [HasCode TyCode T]
    {w : World} {x : T} {uid : Object.UID} :
    Prover.World.FrameDf w (World.putShared T w x uid) [] :=
  Prover.World.FrameDf.step_df_eq (World.putShared T w x uid)
    (Prover.World.FrameDf.refl w) rfl

theorem frame_putFrozen (T : Type) [HasCode TyCode T]
    {w : World} {x : T} {uid : Object.UID} :
    Prover.World.FrameDf w (World.putFrozen T w x uid) [] :=
  Prover.World.FrameDf.step_df_eq (World.putFrozen T w x uid)
    (Prover.World.FrameDf.refl w) rfl

theorem frame_emitEvent (T : Type) [HasCode TyCode T]
    {w : World} {e : T} :
    Prover.World.FrameDf w (World.emitEvent T w e) [] :=
  Prover.World.FrameDf.step_df_eq (World.emitEvent T w e)
    (Prover.World.FrameDf.refl w) rfl

end World
"#;
    crate::write_if_changed(&path, out, written)?;
    Ok(())
}

/// `_root_.<Namespace>.<Name>` for a wrapping struct's base type.
fn wrapping_struct_path(w: &WrappingStruct, program: &Program) -> String {
    let s = program.structs.get(&w.struct_id);
    let namespace = super::program_renderer::get_namespace(program, s.module_id);
    format!(
        "_root_.{}.{}",
        namespace,
        escape::escape_struct_name(&s.name)
    )
}

#[allow(dead_code)]
fn _module_marker(_m: &Module) {}
