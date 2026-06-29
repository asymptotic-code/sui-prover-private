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
    program
        .functions
        .iter()
        .filter(|(_, f)| bag_module_ids.contains(&f.module_id))
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

pub fn collect(program: &Program) -> DynTypeUniverse {
    let mut leaves: HashSet<Type> = HashSet::new();
    let mut wrappings: BTreeSet<WrappingStruct> = BTreeSet::new();

    // Collect the (K, V) types that flow into bag/object_bag calls. The bag
    // K/V types appear as the type-args of `bag::add<K, V>` etc. at the call
    // site. (Unlike the new pipeline we do NOT over-approximate to every
    // call's type-args: in the legacy backport only bag-using functions get
    // `[HasCode TyCode T]` constraints, so only bag-flowing types need a code.)
    let bag_fns = bag_fn_ids(program);
    for (_, f) in program.functions.iter() {
        for node in f.body.iter() {
            if let IRNode::Call {
                function,
                type_args,
                ..
            } = node
            {
                if bag_fns.contains(function) {
                    for t in type_args {
                        classify(t, program, &mut leaves, &mut wrappings);
                    }
                }
            }
        }
    }

    // Exclude `bag::Bag` / `object_bag::ObjectBag` and any struct that
    // (transitively) contains one: including them as TyCode entries would
    // force `TyCodeInterp.lean` to reference `Bag.Bag TyCode` before the
    // `Universe TyCode` instance is declared (forward reference).
    let bag_containing = collect_bag_containing_struct_ids(program);
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

/// The `import` line `Generated/TyCodeInterp.lean` needs in order to bring a
/// struct defined in module `mid` into scope. No package-based filtering: the
/// interp file is its own lib and must import the file that DEFINES each type
/// it names. The defining file depends on the module's shape:
///   * native module  -> `<Pkg>.<Stem>Natives`
///   * has a bag-bearing struct -> `<Pkg>.<Stem>_types_skeleton` (the bag-free
///     half of the split; importing the regular file would cycle, since it
///     imports TyCodeInterp for the `Bag` field)
///   * otherwise -> `<Pkg>.<Stem>` (the module file; transitively re-exports a
///     `_types` split if any)
fn tycode_struct_import(
    program: &Program,
    mid: usize,
    tci_stems: &std::collections::HashSet<String>,
) -> Option<String> {
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
    let stem = program.module_to_file.get(&mid).map(|(_, s)| s.clone())?;
    if module_has_bag_struct(program, mid) {
        Some(format!("import {}.{}_types_skeleton", pkg, stem))
    } else if tci_stems.contains(&stem) {
        // No bag-bearing struct, but the module file imports `TyCodeInterp`
        // (e.g. a `*_tests` module whose bodies use bags): its structs live in
        // the bag-free `_types` split, so importing them here stays acyclic.
        Some(format!("import {}.{}_types", pkg, stem))
    } else {
        Some(format!("import {}.{}", pkg, stem))
    }
}

/// Collect the `import` lines `TyCodeInterp.lean` needs for every struct
/// referenced by a type.
fn collect_referenced_modules(
    ty: &Type,
    program: &Program,
    tci_stems: &std::collections::HashSet<String>,
    out: &mut BTreeSet<String>,
) {
    match ty {
        Type::Struct {
            struct_id,
            type_args,
        } => {
            if program.structs.has(*struct_id) {
                let mid = program.structs.get(struct_id).module_id;
                if let Some(line) = tycode_struct_import(program, mid, tci_stems) {
                    out.insert(line);
                }
            }
            for a in type_args {
                collect_referenced_modules(a, program, tci_stems, out);
            }
        }
        Type::Vector(inner) | Type::Reference(inner) | Type::Option(inner) => {
            collect_referenced_modules(inner, program, tci_stems, out)
        }
        Type::MutableReference(inner, state) => {
            collect_referenced_modules(inner, program, tci_stems, out);
            collect_referenced_modules(state, program, tci_stems, out);
        }
        Type::Tuple(ts) => {
            for t in ts {
                collect_referenced_modules(t, program, tci_stems, out);
            }
        }
        _ => {}
    }
}

// ---------------------------------------------------------------------------
// Emission: Generated/TyCode.lean and Generated/TyCodeInterp.lean.
// ---------------------------------------------------------------------------

pub fn write_ty_code_file(
    universe: &DynTypeUniverse,
    program: &Program,
    output_dir: &Path,
    written: &mut crate::WrittenFiles,
) -> anyhow::Result<()> {
    let gen_dir = output_dir.join("Generated");
    fs::create_dir_all(&gen_dir)?;
    let path = gen_dir.join("TyCode.lean");
    let mut out = String::new();
    out.push_str("-- Generated per project by the lean-backend renderer.\n");
    out.push_str("-- See `plans/lean-pipeline/dynamic-typing-via-repr-design.md`.\n");
    out.push_str("--\n");
    out.push_str("-- Bare inductive only. Interp + Universe + HasCode instances\n");
    out.push_str("-- live in Generated/TyCodeInterp.lean.\n\n");
    out.push_str("inductive TyCode where\n");
    out.push_str("  | dummy\n");
    for leaf in &universe.leaves {
        out.push_str(&format!("  | {}\n", mangle(leaf, program)));
    }
    for w in &universe.wrappings {
        let stem = wrapping_ctor_name(w, program);
        let args: String = (0..w.arity)
            .map(|i| format!(" (a{} : TyCode)", i))
            .collect();
        out.push_str(&format!("  | {}{}\n", stem, args));
    }
    out.push_str("  deriving DecidableEq, Repr\n");
    crate::write_if_changed(&path, &out, written)?;
    Ok(())
}

pub fn write_ty_code_interp_file(
    universe: &DynTypeUniverse,
    program: &Program,
    output_dir: &Path,
    written: &mut crate::WrittenFiles,
) -> anyhow::Result<()> {
    let gen_dir = output_dir.join("Generated");
    fs::create_dir_all(&gen_dir)?;
    let path = gen_dir.join("TyCodeInterp.lean");

    let mut out = String::new();
    out.push_str("-- Generated per project by the lean-backend renderer.\n");
    out.push_str("-- See `plans/lean-pipeline/dynamic-typing-via-repr-design.md`.\n\n");

    out.push_str("import Prelude.BoundedNat\n");
    out.push_str("import Prelude.Universe\n");
    out.push_str("import Generated.TyCode\n");

    // Import the file that DEFINES every referenced struct (leaf or wrapping
    // base). A bag-bearing struct's module contributes its `_types_skeleton`
    // (the bag-free half) so this file never closes an import cycle.
    let tci_stems = super::program_renderer::tycodeinterp_importing_stems(program);
    let mut imports: BTreeSet<String> = BTreeSet::new();
    for t in &universe.leaves {
        collect_referenced_modules(t, program, &tci_stems, &mut imports);
    }
    for w in &universe.wrappings {
        collect_referenced_modules(
            &Type::Struct {
                struct_id: w.struct_id,
                type_args: vec![],
            },
            program,
            &tci_stems,
            &mut imports,
        );
    }
    for line in &imports {
        out.push_str(line);
        out.push('\n');
    }
    out.push('\n');

    // interp
    out.push_str("abbrev TyCode.interp : TyCode -> Type\n");
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
            .map(|i| format!(" (TyCode.interp a{})", i))
            .collect();
        out.push_str(&format!(
            "  | .{}{} => {}{}\n",
            stem, pat, struct_path, interp_args
        ));
    }
    out.push('\n');

    // beqInterp
    out.push_str("def TyCode.beqInterp : \u{2200} u : TyCode, BEq (TyCode.interp u)\n");
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
                "    have : BEq (TyCode.interp a{0}) := TyCode.beqInterp a{0}\n",
                i
            ));
        }
        out.push_str("    inferInstance\n");
    }
    out.push('\n');

    // typeName
    out.push_str("def TyCode.typeName : TyCode \u{2192} String\n");
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
            .map(|i| format!("TyCode.typeName a{}", i))
            .collect::<Vec<_>>()
            .join(" ++ \", \" ++ ");
        out.push_str(&format!(
            "  | .{}{} => \"{}<\" ++ {} ++ \">\"\n",
            stem, pat, base, args
        ));
    }
    out.push('\n');

    // Universe instance
    out.push_str("instance : Universe TyCode where\n");
    out.push_str("  decEq       := inferInstance\n");
    out.push_str("  interp      := TyCode.interp\n");
    out.push_str("  beqInterp   := TyCode.beqInterp\n");
    out.push_str("  typeName    := TyCode.typeName\n\n");

    // Concrete HasCode instances for leaves.
    for leaf in &universe.leaves {
        let stem = mangle(leaf, program);
        let ty_str = super::type_renderer::type_to_string(leaf, program, None);
        out.push_str(&format!(
            "instance : HasCode TyCode ({}) := \u{27E8}.{}, rfl\u{27E9}\n",
            ty_str, stem
        ));
    }

    // Derived HasCode instances for wrappings.
    for w in &universe.wrappings {
        let stem = wrapping_ctor_name(w, program);
        let struct_path = wrapping_struct_path(w, program);
        let constraints: String = (0..w.arity)
            .map(|i| format!(" [hc{0} : HasCode TyCode T{0}]", i))
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
            "\ninstance{cs_ty}{cs}: HasCode TyCode ({sp}{ats}) where\n  code := .{stem}{ca}\n  proof := by show {sp}{sa} = {sp}{ats}; rw [{rw}]\n",
            cs_ty = type_params_intro,
            cs = constraints,
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
