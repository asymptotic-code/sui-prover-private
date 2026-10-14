//! Per-project closed-universe `TyCode` emission.
//! See `plans/lean-pipeline/dynamic-typing-via-repr-design.md`.
//!
//! Phase 3d closed-form HasCode derivation:
//!
//! Types passed to `bag::*` / `object_bag::*` / `dynamic_field::*` /
//! `dynamic_object_field::*` calls decompose into two flavors:
//!
//!   * **Leaves** -- concrete types with no struct type args
//!     (primitives, `Address`, `vec<u8>`, `Type_name.TypeName`,
//!     `USDC`/`SUI`/etc., `Bag.Bag`, ...). Each leaf gets a
//!     non-recursive TyCode constructor, an interp case, and a
//!     concrete `HasCode TyCode <leaf> := ⟨.<ctor>, rfl⟩` instance.
//!   * **Wrappings** -- struct shapes with type parameters
//!     (`SupportedAsset T`, `Node T`, `MyPair A B`, ...). Each
//!     wrapping gets a recursive TyCode constructor that takes one
//!     TyCode arg per type parameter, a recursive interp case, and a
//!     derived `[HasCode TyCode T] → HasCode TyCode (S T)` instance.
//!     Generic functions whose type params flow through wrappings
//!     get their `HasCode TyCode (Wrapper t_tv0)` constraint
//!     resolved by Lean's instance search: it reduces to
//!     `HasCode TyCode t_tv0`, supplied via the function's
//!     `[HasCode TyCode T]` signature constraint.
//!
//! Output split across two files:
//!   * `Generated/TyCode.lean` -- bare inductive only. No user
//!     imports. User `_Types` files import this.
//!   * `Generated/TyCodeInterp.lean` -- interp + Universe + HasCode
//!     instances. Imports user `_Types` files.

use std::collections::{BTreeSet, HashSet};
use std::fs;
use std::io;
use std::path::Path;

use crate::ir::analysis::substitute_type_params;
use crate::ir::expr::{Block, BlockTail, Expr, Stmt};
use crate::ir::{Module, Program, Struct, StructId, Type};

use super::escape;
use super::ty;

/// A struct shape used as a "wrapping" in TyCode -- the struct id +
/// its arity. Distinct (struct_id, arity) pairs become distinct
/// recursive TyCode constructors.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct WrappingStruct {
    pub struct_id: StructId,
    pub arity: usize,
}

/// Full type universe for the project: concrete leaf types + wrapping
/// struct shapes encountered across all heterogeneous-storage call
/// sites and augmented ghost fields.
#[derive(Debug, Default)]
pub struct DynTypeUniverse {
    pub leaves: Vec<Type>,
    pub wrappings: Vec<WrappingStruct>,
}

pub fn collect(program: &Program) -> DynTypeUniverse {
    let mut leaves: HashSet<Type> = HashSet::new();
    let mut wrappings: BTreeSet<WrappingStruct> = BTreeSet::new();
    // (The ghost-era step that walked struct fields for
    // `Prelude::TypedMap K V` pairs was deleted 2026-06-11: nothing
    // can register that struct since step-2C removed
    // register_typed_map_natives, so the harvest was a no-op.)
    // 2) Walk all function bodies for direct heterogeneous-storage calls.
    for (_, f) in program.functions.iter() {
        walk_block(&f.body, program, &mut leaves, &mut wrappings);
    }
    // 3) Bag-CONTAINING structs (e.g. current-lending `Referral`) ARE
    //    now legal TyCode df values. Their `Bag` / `ObjectBag` field is
    //    typed over the SEPARATE `BagU` universe (see `bag_universe.rs`
    //    + `render::ty`), so a `<Mod>_Types.lean` defining such a struct
    //    imports `Generated.BagUInterp` -- NOT `TyCodeInterp` -- for the
    //    field's `[Universe BagU]`. BagU excludes Bag-containing structs,
    //    so the old `_Types -> TyCodeInterp -> _Types` cycle no longer
    //    forms and these structs need no exclusion here.
    //
    //    We DO still exclude `bag::Bag` / `object_bag::ObjectBag`
    //    THEMSELVES: a Bag VALUE stored in a dynamic field rides the
    //    dedicated `df_bag_entries` / `store_bag_*` path (typed over
    //    BagU), never `df_entries` as a TyCode code.
    //    See `plans/lean-pipeline/split-bag-df-universes.md`.
    let is_heterogeneous_container_struct = |sid: &StructId| -> bool {
        program.structs.get(sid).map_or(false, |s| {
            s.qualified_name == "bag::Bag" || s.qualified_name == "object_bag::ObjectBag"
        })
    };
    wrappings.retain(|w| !is_heterogeneous_container_struct(&w.struct_id));
    leaves.retain(|t| match t {
        Type::Struct { struct_id, .. } => !is_heterogeneous_container_struct(struct_id),
        _ => true,
    });

    let mut leaf_vec: Vec<Type> = leaves.into_iter().collect();
    leaf_vec.sort_by(|a, b| mangle(a, program).cmp(&mangle(b, program)));
    DynTypeUniverse {
        leaves: leaf_vec,
        wrappings: wrappings.into_iter().collect(),
    }
}

/// Returns the set of `StructId`s whose fields (transitively)
/// reference `Sui::bag::Bag` or `Sui::object_bag::ObjectBag`.
/// Used to filter `Bag`-containing structs out of the TyCode
/// universe AND to drive the per-module `_Types` / `_Types_Skeleton`
/// file split that breaks the cycle.
/// True iff `mid` contains at least one Bag-containing struct.
/// Used by `render::mod` to decide whether the module's `_Types`
/// file needs to be split into Skeleton + WithBag files.
pub fn module_has_bag_struct(program: &Program, mid: crate::ir::ModId) -> bool {
    let bag_ids = collect_bag_containing_struct_ids(program);
    program
        .structs
        .iter()
        .any(|(sid, s)| s.module_id == mid && bag_ids.contains(&sid))
}

pub fn collect_bag_containing_struct_ids(program: &Program) -> HashSet<StructId> {
    let is_heterogeneous_container = |sid: &StructId| -> bool {
        program.structs.get(sid).map_or(false, |s| {
            // qualified_name is `module::name` (no package prefix).
            s.qualified_name == "bag::Bag" || s.qualified_name == "object_bag::ObjectBag"
        })
    };

    // BFS from each struct over its field types, looking for a Bag.
    let mut tainted: HashSet<StructId> = HashSet::new();
    fn collect_struct_ids_in_type(ty: &Type, out: &mut Vec<StructId>) {
        match ty {
            Type::Struct {
                struct_id,
                type_args,
            } => {
                out.push(*struct_id);
                for a in type_args {
                    collect_struct_ids_in_type(a, out);
                }
            }
            Type::Vector(inner) | Type::Reference(inner) => {
                collect_struct_ids_in_type(inner, out);
            }
            Type::MutableRef { inner, root } => {
                collect_struct_ids_in_type(inner, out);
                collect_struct_ids_in_type(root, out);
            }
            Type::Tuple(ts) => {
                for t in ts {
                    collect_struct_ids_in_type(t, out);
                }
            }
            _ => {}
        }
    }

    // Direct references: for each struct, check if any field type
    // references a Bag/ObjectBag directly.
    let mut direct: HashSet<StructId> = HashSet::new();
    for (_, s) in program.structs.iter() {
        for f in &s.fields {
            let mut deps: Vec<StructId> = Vec::new();
            collect_struct_ids_in_type(&f.field_type, &mut deps);
            if deps.iter().any(|sid| is_heterogeneous_container(sid)) {
                direct.insert(
                    program
                        .structs
                        .iter()
                        .find(|(_, ss)| std::ptr::eq(*ss, s))
                        .map(|(id, _)| *id)
                        .unwrap_or_else(|| panic!("struct not found in store")),
                );
                break;
            }
        }
    }
    tainted.extend(direct.iter());

    // Transitive: if struct A contains struct B (tainted), A is tainted too.
    // Fixed-point iteration.
    let mut changed = true;
    while changed {
        changed = false;
        for (sid, s) in program.structs.iter() {
            if tainted.contains(&sid) {
                continue;
            }
            for f in &s.fields {
                let mut deps: Vec<StructId> = Vec::new();
                collect_struct_ids_in_type(&f.field_type, &mut deps);
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

/// Classify `ty` and recurse:
///   * Primitives / Address / Vector / Reference / MutableRef /
///     Tuple / TypeParam: handled below (leaves or recurse)
///   * Struct with 0 type_args: leaf (register concrete)
///   * Struct with N>=1 type_args: wrapping (register shape; recurse
///     into each arg)
pub fn classify(
    ty: &Type,
    program: &Program,
    leaves: &mut HashSet<Type>,
    wrappings: &mut BTreeSet<WrappingStruct>,
) {
    match ty {
        // Pure leaves
        Type::Unit | Type::Bool | Type::Prop | Type::UInt(_) | Type::Address => {
            // Only register concrete (primitive) leaves we may need
            // a HasCode for. Skip Unit / Prop (rarely used as bag K/V).
            // Bool IS registered: it appears as a native-map value type
            // (e.g. scallop's `Wit_table<TypeName, Bool>` flag tables),
            // which needs `HasCode TyCode Bool` at the `wit_table::*`
            // call sites.
            if matches!(ty, Type::UInt(_) | Type::Address | Type::Bool) {
                leaves.insert(ty.clone());
            }
        }
        Type::TypeParam(_) => {
            // Type-param leaf -- the function gets a [HasCode TyCode T]
            // constraint per type param via render_function.
        }
        Type::Vector(inner) => {
            // Vector of primitives is a common leaf (vec<u8> for keys).
            // Treat Vector as a wrapping only if the inner is itself
            // non-trivial; for primitive inners, emit as a concrete
            // leaf for efficiency. For now: always emit as leaf if the
            // inner is concrete; recurse otherwise.
            if is_concrete(inner) {
                leaves.insert(ty.clone());
            } else {
                classify(inner, program, leaves, wrappings);
            }
        }
        Type::Reference(inner) => classify(inner, program, leaves, wrappings),
        Type::MutableRef { inner, root } => {
            classify(inner, program, leaves, wrappings);
            classify(root, program, leaves, wrappings);
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
                // Concrete leaf struct (e.g. USDC, TypeName, Bag.Bag with 0-arity in IR).
                leaves.insert(ty.clone());
            } else {
                // Wrapping: register the shape, recurse into args.
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

pub fn walk_block(
    block: &Block,
    program: &Program,
    leaves: &mut HashSet<Type>,
    wrappings: &mut BTreeSet<WrappingStruct>,
) {
    for stmt in &block.stmts {
        match stmt {
            Stmt::Let { value, .. } => walk_expr(value, program, leaves, wrappings),
            Stmt::Eval(e) => walk_expr(e, program, leaves, wrappings),
        }
    }
    match &block.tail {
        BlockTail::Value(e) => walk_expr(e, program, leaves, wrappings),
        BlockTail::Break { value, .. } => walk_expr(value, program, leaves, wrappings),
        BlockTail::Continue { value, .. } => walk_expr(value, program, leaves, wrappings),
        BlockTail::Return(e) => walk_expr(e, program, leaves, wrappings),
        BlockTail::ReturnFromBlock { value, .. } => walk_expr(value, program, leaves, wrappings),
        BlockTail::Abort { code } => walk_expr(code, program, leaves, wrappings),
    }
}

pub fn walk_expr(
    expr: &Expr,
    program: &Program,
    leaves: &mut HashSet<Type>,
    wrappings: &mut BTreeSet<WrappingStruct>,
) {
    match expr {
        Expr::Borrow { step, base } => {
            for __pe in step.exprs() {
                walk_expr(__pe, program, leaves, wrappings);
            }
            walk_expr(base, program, leaves, wrappings);
        }
        Expr::Update { step, base, value } => {
            for __pe in step.exprs() {
                walk_expr(__pe, program, leaves, wrappings);
            }
            walk_expr(base, program, leaves, wrappings);
            walk_expr(value, program, leaves, wrappings);
        }
        Expr::Call {
            type_args, args, ..
        } => {
            // Collect ALL type_args of every call -- not just calls to
            // heterogeneous-storage natives. Every non-lemma user
            // function carries `[HasCode _root_.TyCode T]` constraints
            // for its type params (Phase 3d), so concrete types passed
            // at any call site need a HasCode instance in scope.
            // Over-approximation is fine: extra `HasCode` instances
            // for unused types are harmless.
            for t in type_args {
                classify(t, program, leaves, wrappings);
            }
            for a in args {
                walk_expr(a, program, leaves, wrappings);
            }
        }
        Expr::Tuple(es) | Expr::Pack { fields: es, .. } => {
            for x in es {
                walk_expr(x, program, leaves, wrappings);
            }
        }
        Expr::Unpack { value, .. }
        | Expr::Field { base: value, .. }
        | Expr::ReadRef(value)
        | Expr::ToProp(value)
        | Expr::ToBool(value) => walk_expr(value, program, leaves, wrappings),
        Expr::WriteRef { reference, value } => {
            walk_expr(reference, program, leaves, wrappings);
            walk_expr(value, program, leaves, wrappings);
        }
        Expr::BinOp { lhs, rhs, .. } => {
            walk_expr(lhs, program, leaves, wrappings);
            walk_expr(rhs, program, leaves, wrappings);
        }
        Expr::UnOp { operand, .. } => walk_expr(operand, program, leaves, wrappings),
        Expr::If {
            cond,
            then_branch,
            else_branch,
        } => {
            walk_expr(cond, program, leaves, wrappings);
            walk_block(then_branch, program, leaves, wrappings);
            walk_block(else_branch, program, leaves, wrappings);
        }
        Expr::Match {
            selector, cases, ..
        } => {
            walk_expr(selector, program, leaves, wrappings);
            for c in cases {
                walk_block(&c.body, program, leaves, wrappings);
            }
        }
        Expr::While {
            header,
            cond,
            body,
            iter_locals,
            header_exit_locals: _,
            live_out: _,
        } => {
            for (_, init) in iter_locals {
                walk_expr(init, program, leaves, wrappings);
            }
            walk_block(header, program, leaves, wrappings);
            walk_expr(cond, program, leaves, wrappings);
            walk_block(body, program, leaves, wrappings);
        }
        Expr::Quantifier { domain, body, .. } => {
            use crate::ir::quant::QuantDomain;
            match domain {
                QuantDomain::Unbounded => {}
                QuantDomain::Range { start, end } => {
                    walk_expr(start, program, leaves, wrappings);
                    walk_expr(end, program, leaves, wrappings);
                }
                QuantDomain::Collection(c) => walk_expr(c, program, leaves, wrappings),
                QuantDomain::VecRange { vec, start, end } => {
                    walk_expr(vec, program, leaves, wrappings);
                    walk_expr(start, program, leaves, wrappings);
                    walk_expr(end, program, leaves, wrappings);
                }
            }
            walk_block(body, program, leaves, wrappings);
        }
        Expr::Var(_)
        | Expr::Const(_)
        | Expr::Unit
        | Expr::BitOp(_)
        | Expr::BorrowLoc(_)
        | Expr::BorrowGlobal(_)
        | Expr::WriteBack { .. }
        | Expr::IsParent { .. } => {}
        Expr::LabeledBlock { .. } => {
            unreachable!("Expr::LabeledBlock should be eliminated by stage 7 helper extraction")
        }
    }
}

fn is_heterogeneous_storage_module(module: &Module) -> bool {
    if module.package_name != "Sui" {
        return false;
    }
    matches!(
        module.name.as_str(),
        "bag" | "object_bag" | "dynamic_field" | "dynamic_object_field"
    )
}

fn is_concrete(ty: &Type) -> bool {
    match ty {
        Type::Unit | Type::Bool | Type::Prop | Type::UInt(_) | Type::Address => true,
        Type::TypeParam(_) => false,
        Type::Vector(inner) | Type::Reference(inner) => is_concrete(inner),
        Type::MutableRef { inner, root } => is_concrete(inner) && is_concrete(root),
        Type::Tuple(ts) => ts.iter().all(is_concrete),
        Type::Struct { type_args, .. } => type_args.iter().all(is_concrete),
    }
}

pub fn mangle(ty: &Type, program: &Program) -> String {
    let mut s = String::new();
    mangle_into(ty, program, &mut s);
    s
}

fn mangle_into(ty: &Type, program: &Program, out: &mut String) {
    match ty {
        Type::Unit => out.push_str("unit"),
        Type::Bool => out.push_str("bool"),
        Type::Prop => out.push_str("prop"),
        Type::UInt(n) => out.push_str(&format!("u{}", n)),
        Type::Address => out.push_str("address"),
        Type::Vector(inner) => {
            out.push_str("vec_");
            mangle_into(inner, program, out);
        }
        Type::Reference(inner) => mangle_into(inner, program, out),
        Type::MutableRef { inner, .. } => {
            out.push_str("mut_");
            mangle_into(inner, program, out);
        }
        Type::TypeParam(i) => out.push_str(&format!("tp{}", i)),
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
            if program.structs.get(struct_id).is_some() {
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

/// Mangled, collision-free prefix for a struct: `<module>__<Name>` for
/// lemma-package structs, `<Package>__<module>__<Name>` for user-package
/// structs. Mirrors `escape::module_render_namespace`'s uniqueness rule
/// so two structs whose bare `module::Name` collide (e.g. Sui's
/// `linked_table::Node` and a vendored `MoveSTL::linked_table::Node`)
/// get distinct TyCode / ObjType constructor names. `qualified_name`
/// alone (`module::Name`) is NOT unique across packages, which produced
/// duplicate inductive constructors and a Lean "Cannot define multiple
/// constructors with the same name" error.
pub(crate) fn struct_mangle_prefix(struct_id: StructId, program: &Program) -> String {
    let s = match program.structs.get(&struct_id) {
        Some(s) => s,
        None => return format!("sid{}", struct_id),
    };
    let qn = s.qualified_name.replace("::", "__");
    let pkg = program
        .modules
        .get(&s.module_id)
        .map(|m| m.package_name.as_str())
        .unwrap_or("");
    if pkg.is_empty() || crate::render::escape::is_lemma_package(pkg) {
        qn
    } else {
        format!("{}__{}", pkg.replace("::", "__"), qn)
    }
}

pub fn wrapping_ctor_name(w: &WrappingStruct, program: &Program) -> String {
    if program.structs.get(&w.struct_id).is_some() {
        let mut name = struct_mangle_prefix(w.struct_id, program);
        for _ in 0..w.arity {
            name.push_str("_X_t");
        }
        name
    } else {
        format!("sid{}_X_arity{}", w.struct_id, w.arity)
    }
}

/// Move fully-qualified type name of a (concrete) leaf type:
/// `<64hex-addr>::<module>::<Name>` for structs (with `<args>` for
/// concrete generic instantiations), the primitive keyword for
/// primitives. Matches `std::type_name::get`'s string so coin-ordering
/// comparisons (`bcs(type_name X) < bcs(type_name Y)`) agree with Move.
pub fn leaf_fqn(ty: &Type, program: &Program) -> String {
    match ty {
        Type::Bool => "bool".to_string(),
        Type::UInt(n) => format!("u{}", n),
        Type::Address => "address".to_string(),
        Type::Vector(inner) => format!("vector<{}>", leaf_fqn(inner, program)),
        Type::Reference(inner) | Type::MutableRef { inner, .. } => leaf_fqn(inner, program),
        Type::TypeParam(i) => format!("tp{}", i),
        Type::Tuple(_) | Type::Unit | Type::Prop => "unit".to_string(),
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

/// `<64hex-addr>::<module>::<Name>` for a struct, no type args.
pub fn struct_base_fqn(struct_id: StructId, program: &Program) -> String {
    match program.structs.get(&struct_id) {
        Some(s) => {
            let addr = program
                .modules
                .get(&s.module_id)
                .map(|m| m.address.as_str())
                .unwrap_or("");
            // `qualified_name` is `module::Name`.
            format!("{}::{}", addr, s.qualified_name)
        }
        None => format!("sid{}", struct_id),
    }
}

/// Escape a string for embedding inside a Lean `"..."` literal.
pub fn lean_str(s: &str) -> String {
    s.replace('\\', "\\\\").replace('"', "\\\"")
}

// ====================================================================
// TyCode type-param taint analysis
// ====================================================================
//
// `MoveStdlib::type_name::{get, with_defining_ids, with_original_ids,
// get_with_original_ids}` are universe-generic and the renderer pins
// `(U := _root_.TyCode)` at each call site (see `render::expr`), which
// makes the native require `[HasCode _root_.TyCode T]`. User-package
// functions carry that constraint on every type param unconditionally,
// but LEMMA-package functions (e.g. the translated `sui::package::claim`)
// do not -- so a lemma function that calls a type_name native with its
// own type param would fail typeclass resolution.
//
// This pass mirrors `obj_type_universe::compute_obj_typeparam_deps`:
// a forward fixpoint over the call graph that taints any type param
// flowing into a type_name native call's type args, so the renderer
// can emit `[HasCode _root_.TyCode T]` exactly where needed (including
// lemma packages) without over-approximating onto helpers instantiated
// with non-universe types.

fn is_tycode_pin_constraint_call(program: &Program, fid: crate::ir::FunId) -> bool {
    let Some(callee) = program.lookup_callee(fid) else {
        return false;
    };
    let name = callee.name();
    let Some(m) = program.modules.get(&callee.module()) else {
        return false;
    };
    // Mirror `render::expr::call` `needs_tycode_pin` /
    // `render::function::is_tycode_pin_native`: EVERY native the renderer
    // pins `(U := __TyU)` at the call site must taint the type params
    // flowing into it, so the enclosing function binds `{__TyU}` +
    // `[HasCode __TyU T]`. Previously only `type_name::*` was handled here;
    // `types::is_one_time_witness` and `bcs::to_bytes` were missing, so a
    // translated fn calling one of them on a type param WITHOUT also hitting
    // `type_name` (e.g. `sui::coin::create_currency`, newly translated when
    // coin moved off the natives allowlist) got the call-site pin but no
    // binder -> "Unknown identifier `__TyU`".
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

/// Propagate per-type-param taint from a source function to its `Spec`
/// companions (`.aborts` / `.requires` / `.ensures`), which share the
/// source's type-param list but whose own (often abort-trivial) bodies
/// under-report the taint. Without this a companion can declare a
/// DIFFERENT instance-constraint set than its source -- e.g. the source
/// drops `[HasCode TyCode T]` for an object param while the abort
/// companion keeps it -- so a cross-companion call fails to supply the
/// instance. Fixpoint-OR the target's taint into each companion (by
/// index; Spec companions share the source's type-param list).
pub fn inherit_spec_companion_typeparam_deps(
    program: &Program,
    deps: &mut std::collections::HashMap<crate::ir::FunId, Vec<bool>>,
) {
    use crate::ir::function::FunctionKind;
    // (module, name) -> fid, for resolving the parent of `.cont_N`
    // continuation fragments (Synthetic, named `<parent>.cont_<slot>`,
    // sharing the parent's type-param list -- see stage_07_dejumps::
    // return_lift). They carry no `target` field, so resolve by name.
    let mut name_index: std::collections::HashMap<(crate::ir::ModId, &str), crate::ir::FunId> =
        std::collections::HashMap::new();
    for (fid, f) in program.functions.iter() {
        name_index.insert((f.module, f.name.as_str()), *fid);
    }
    // Per-function inheritance target (the source whose type-param
    // constraints this function must mirror).
    let mut targets: std::collections::HashMap<crate::ir::FunId, crate::ir::FunId> =
        std::collections::HashMap::new();
    for (fid, f) in program.functions.iter() {
        let target = match &f.kind {
            FunctionKind::Spec { target, .. } => Some(*target),
            // Proof obligations (`<impl>_correct` / `<impl>_asserts_correct`,
            // emitted by stage_12) clone the impl's type-param list and call its
            // `.aborts`/`.asserts`/`.ensures` companions, so they need every
            // per-typeparam universe constraint the impl carries. The main taint
            // fixpoint misses a constraint a companion only acquires via THIS
            // inherit pass (which runs after the fixpoint) -- leaving e.g.
            // `is_owner_asserts_correct` with `HasCode TyCode t_tv1` instead of
            // `HasCode ObjType t_tv1` + `HasObjectId t_tv1`. Mirror the impl's
            // constraints downward (the obligation's type params are the impl's).
            FunctionKind::Theorem { target, .. } | FunctionKind::Axiom { target, .. } => {
                Some(*target)
            }
            FunctionKind::Synthetic => {
                // Walk up `.cont_N` levels to the NEAREST EXISTING
                // ancestor. cont_inline drops intermediate fragments
                // (e.g. `.cont_1` is inlined but its child `.cont_1.cont_0`
                // survives), so a single strip can land on a non-existent
                // parent and orphan the fragment from its family. Keep
                // stripping until a real function is found.
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
            let Some(target_deps) = deps.get(target).cloned() else {
                continue;
            };
            // Downward: a spec companion / cont fragment mirrors its
            // source / parent's per-typeparam constraints.
            if let Some(local) = deps.get_mut(fid) {
                if local.len() == target_deps.len() {
                    for (l, t) in local.iter_mut().zip(target_deps.iter()) {
                        if *t && !*l {
                            *l = true;
                            changed = true;
                        }
                    }
                }
            }
            // Upward (cont fragments only): a `.cont_N` fragment is one
            // piece of a single source function -- every piece shares the
            // SAME type-param list and the pieces call one another, so a
            // bag/df op originating in a DEEP fragment must also constrain
            // its parent (and, transitively, its sibling fragments). The
            // downward-only pass missed a taint born in a deep fragment,
            // leaving a sibling caller without the `[HasCode _ T]` the
            // callee requires (cetus-clmm / ember `HasCode BagU` synthesis
            // failures). The Spec->source edge stays downward-only so a
            // companion's taint never leaks into the value function.
            let fid_is_cont = matches!(
                program.functions.get(fid).map(|f| &f.kind),
                Some(FunctionKind::Synthetic)
            );
            if fid_is_cont {
                if let Some(fid_deps) = deps.get(fid).cloned() {
                    if let Some(parent) = deps.get_mut(target) {
                        if parent.len() == fid_deps.len() {
                            for (p, l) in parent.iter_mut().zip(fid_deps.iter()) {
                                if *l && !*p {
                                    *p = true;
                                    changed = true;
                                }
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
}

/// Whether a USER-package (non-lemma) callee emits `[HasCode _root_.TyCode T]`
/// on its type param at slot `k`. `render_function` gives every user-package
/// type param that constraint UNCONDITIONALLY -- except in the `needs_obj`
/// arm, where an object-tainted param carries `[HasCode _root_.ObjType T]
/// [Object.HasObjectId T]` and gets TyCode back only when its own tycode
/// taint fires. Callers must mirror whatever the callee binds.
fn user_callee_binds_tycode(
    program: &Program,
    callee_fid: crate::ir::FunId,
    slot: usize,
    obj_deps: &std::collections::HashMap<crate::ir::FunId, Vec<bool>>,
    tycode_deps: &std::collections::HashMap<crate::ir::FunId, Vec<bool>>,
) -> bool {
    let Some(callee) = program.functions.get(&callee_fid) else {
        return false;
    };
    let is_user_pkg = program
        .modules
        .get(&callee.module)
        .is_some_and(|m| !super::function::name_is_lemma_package(&m.package_name));
    if !is_user_pkg {
        return false;
    }
    let obj_tainted = obj_deps
        .get(&callee_fid)
        .and_then(|v| v.get(slot))
        .copied()
        .unwrap_or(false);
    let tycode_tainted = tycode_deps
        .get(&callee_fid)
        .and_then(|v| v.get(slot))
        .copied()
        .unwrap_or(false);
    !obj_tainted || tycode_tainted
}

/// `obj_deps` is `compute_obj_typeparam_deps`'s output and MUST be computed
/// first: a caller whose own param is object-tainted loses the unconditional
/// user-package `[HasCode _root_.TyCode T]` binder, so it has to re-acquire it
/// from every callee that still demands one. The case that exposed this
/// (bluefin-timelock): `new_stored_internal_spec` calls `object::id(&cap)` on a
/// `Cap: key + store`, so it was rendered `[HasCode ObjType Cap]` alone, while
/// the impl it delegates to parks that same cap in a dynamic field and is
/// rendered `[HasCode TyCode Cap]` -- 53 "failed to synthesize instance of type
/// class HasCode TyCode t_tv1" at the call into the impl.
pub fn compute_tycode_typeparam_deps(
    program: &Program,
    obj_deps: &std::collections::HashMap<crate::ir::FunId, Vec<bool>>,
) -> std::collections::HashMap<crate::ir::FunId, Vec<bool>> {
    let mut deps: std::collections::HashMap<crate::ir::FunId, Vec<bool>> =
        std::collections::HashMap::new();
    for (fid, f) in program.functions.iter() {
        deps.insert(*fid, vec![false; f.signature.type_params.len()]);
    }
    // The call-edge fixpoint and the companion inheritance feed each other, so
    // they run to a JOINT fixpoint. A taint a `.cont_N` fragment only acquires
    // by inheritance has callers of its own that are not its family: a loop
    // helper tail-calling the continuation `aborts_live_loop` routed its
    // accumulator into (`coin_registry::new_currency_with_otw`, whose
    // `.aborts.labeled_0.while_0` calls `.aborts.cont_0.cont_1`). Inheriting
    // once after the call edges settled left that helper without the
    // `[HasCode __TyU T]` its callee binds.
    loop {
        loop {
            let mut changed = false;
            let keys: Vec<crate::ir::FunId> = program.functions.keys().copied().collect();
            for fid in keys {
                let f = program.functions.get(&fid).expect("fid present");
                let mut local = deps.get(&fid).cloned().unwrap_or_default();
                let before = local.clone();
                tc_walk_block(&f.body, program, &deps, obj_deps, &mut local);
                if before != local {
                    deps.insert(fid, local);
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }
        let before = deps.clone();
        inherit_spec_companion_typeparam_deps(program, &mut deps);
        if deps == before {
            break;
        }
    }
    deps
}

fn tc_walk_block(
    block: &Block,
    program: &Program,
    deps: &std::collections::HashMap<crate::ir::FunId, Vec<bool>>,
    obj_deps: &std::collections::HashMap<crate::ir::FunId, Vec<bool>>,
    local: &mut Vec<bool>,
) {
    for stmt in &block.stmts {
        match stmt {
            Stmt::Let { value, .. } => tc_walk_expr(value, program, deps, obj_deps, local),
            Stmt::Eval(e) => tc_walk_expr(e, program, deps, obj_deps, local),
        }
    }
    match &block.tail {
        BlockTail::Value(e) => tc_walk_expr(e, program, deps, obj_deps, local),
        BlockTail::Break { value, .. } => tc_walk_expr(value, program, deps, obj_deps, local),
        BlockTail::Continue { value, .. } => tc_walk_expr(value, program, deps, obj_deps, local),
        BlockTail::Return(e) => tc_walk_expr(e, program, deps, obj_deps, local),
        BlockTail::ReturnFromBlock { value, .. } => {
            tc_walk_expr(value, program, deps, obj_deps, local)
        }
        BlockTail::Abort { code } => tc_walk_expr(code, program, deps, obj_deps, local),
    }
}

fn tc_walk_expr(
    expr: &Expr,
    program: &Program,
    deps: &std::collections::HashMap<crate::ir::FunId, Vec<bool>>,
    obj_deps: &std::collections::HashMap<crate::ir::FunId, Vec<bool>>,
    local: &mut Vec<bool>,
) {
    match expr {
        Expr::Borrow { step, base } => {
            for __pe in step.exprs() {
                tc_walk_expr(__pe, program, deps, obj_deps, local);
            }
            tc_walk_expr(base, program, deps, obj_deps, local);
        }
        Expr::Update { step, base, value } => {
            for __pe in step.exprs() {
                tc_walk_expr(__pe, program, deps, obj_deps, local);
            }
            tc_walk_expr(base, program, deps, obj_deps, local);
            tc_walk_expr(value, program, deps, obj_deps, local);
        }
        Expr::Call {
            fun,
            type_args,
            args,
            ..
        } => {
            tc_handle_call(*fun, type_args, program, deps, obj_deps, local);
            for a in args {
                tc_walk_expr(a, program, deps, obj_deps, local);
            }
        }
        Expr::Tuple(es) | Expr::Pack { fields: es, .. } => {
            for x in es {
                tc_walk_expr(x, program, deps, obj_deps, local);
            }
        }
        Expr::Unpack { value, .. }
        | Expr::Field { base: value, .. }
        | Expr::ReadRef(value)
        | Expr::ToProp(value)
        | Expr::ToBool(value) => tc_walk_expr(value, program, deps, obj_deps, local),
        Expr::WriteRef { reference, value } => {
            tc_walk_expr(reference, program, deps, obj_deps, local);
            tc_walk_expr(value, program, deps, obj_deps, local);
        }
        Expr::BinOp { lhs, rhs, .. } => {
            tc_walk_expr(lhs, program, deps, obj_deps, local);
            tc_walk_expr(rhs, program, deps, obj_deps, local);
        }
        Expr::UnOp { operand, .. } => tc_walk_expr(operand, program, deps, obj_deps, local),
        Expr::If {
            cond,
            then_branch,
            else_branch,
        } => {
            tc_walk_expr(cond, program, deps, obj_deps, local);
            tc_walk_block(then_branch, program, deps, obj_deps, local);
            tc_walk_block(else_branch, program, deps, obj_deps, local);
        }
        Expr::Match {
            selector, cases, ..
        } => {
            tc_walk_expr(selector, program, deps, obj_deps, local);
            for c in cases {
                tc_walk_block(&c.body, program, deps, obj_deps, local);
            }
        }
        Expr::While {
            header,
            cond,
            body,
            iter_locals,
            header_exit_locals: _,
            live_out: _,
        } => {
            for (_, init) in iter_locals {
                tc_walk_expr(init, program, deps, obj_deps, local);
            }
            tc_walk_block(header, program, deps, obj_deps, local);
            tc_walk_expr(cond, program, deps, obj_deps, local);
            tc_walk_block(body, program, deps, obj_deps, local);
        }
        Expr::Var(_)
        | Expr::Const(_)
        | Expr::Unit
        | Expr::BorrowLoc(_)
        | Expr::BorrowGlobal(_)
        | Expr::IsParent { .. }
        | Expr::Quantifier { .. }
        | Expr::BitOp(_)
        | Expr::WriteBack { .. } => {}
        Expr::LabeledBlock { .. } => {
            unreachable!("Expr::LabeledBlock should be eliminated by stage 7 helper extraction")
        }
    }
}

fn tc_handle_call(
    callee_fid: crate::ir::FunId,
    type_args: &[Type],
    program: &Program,
    deps: &std::collections::HashMap<crate::ir::FunId, Vec<bool>>,
    obj_deps: &std::collections::HashMap<crate::ir::FunId, Vec<bool>>,
    local: &mut Vec<bool>,
) {
    if is_tycode_pin_constraint_call(program, callee_fid) {
        for ta in type_args {
            if let Type::TypeParam(i) = ta {
                let i = *i as usize;
                if i < local.len() {
                    local[i] = true;
                }
            }
        }
        return;
    }
    if let Some(callee_taint) = deps.get(&callee_fid) {
        for (k, &is_tainted) in callee_taint.iter().enumerate() {
            // A user-package callee binds `[HasCode _root_.TyCode T]` on its
            // OWN account (unconditionally, unless object-tainted), so the
            // caller must supply one even when the callee's tycode taint bit
            // is clear. Only matters for a caller param that is itself
            // object-tainted -- otherwise the caller already binds TyCode
            // unconditionally and the extra taint is a no-op.
            if !is_tainted && !user_callee_binds_tycode(program, callee_fid, k, obj_deps, deps) {
                continue;
            }
            if let Some(Type::TypeParam(i)) = type_args.get(k) {
                let i = *i as usize;
                if i < local.len() {
                    local[i] = true;
                }
            }
        }
    }
}

pub fn write_ty_code_file(
    universe: &DynTypeUniverse,
    program: &Program,
    output_dir: &Path,
) -> io::Result<()> {
    let gen_dir = output_dir.join("Generated");
    fs::create_dir_all(&gen_dir)?;
    let path = gen_dir.join("TyCode.lean");
    let mut out = String::new();
    out.push_str("-- Generated per project by the lean-pipeline renderer.\n");
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
    fs::write(&path, &out)?;
    Ok(())
}

// ====================================================================
// BCS serialization emitter (shared by TyCode + BagU universes).
// ====================================================================
//
// EXACT BYTE FORMAT emitted by the generated `<Universe>.serialize`
// arms. Phase 2's hand-written Lean decoder MUST mirror this verbatim:
//
//   * struct      = its fields, serialized in DECLARATION order and
//                   `++`-concatenated. NO length prefix, NO tag.
//   * enum        = `bcsUleb128 <variant tag>` ++ that variant's
//                   fields in declaration order.
//   * u8          = `[v]`.
//   * uN (N > 8)  = `bcsUIntLe (N/8) v.val`  (little-endian, N/8 bytes).
//   * bool        = `[if v then 1 else 0]`.
//   * address     = `bcsUIntBe 32 v.bytes.val`  (32 big-endian bytes;
//                   a Lean `Address` is `{ bytes : BoundedNat (2^256) }`).
//   * vector<u8>  = `bcsUleb128 v.length ++ v`.
//   * vector<T>   = `bcsUleb128 v.length ++ (v.flatMap (fun x => <T x>))`.
//   * Option<T>   = `match v.vec with | [] => [0] | x :: _ => 1 :: <T x>`
//                   (Lean `MoveOption { vec : List T }` -- BCS's 0/1 tag,
//                   NOT the vector rule that its Move layout would imply).
//   * String / ascii::String (Lean `{ bytes : List u8 }`) and Url (Lean
//                   `{ url : ascii::String }`) all reduce to the generic
//                   struct rule -> `bcsUleb128 bytes.length ++ bytes`.
//                   `ascii::String` / `Url` get there on their own;
//                   `std::string::String` needs the explicit arm in
//                   `serialize_struct_value`, since it is a REGISTERED
//                   native and would otherwise hit the opaque-native
//                   `[]` catch-all.
//   * object::ID (Lean `{ bytes : Address }`) = `bcsUIntBe 32
//                   v.bytes.bytes.val`, and object::UID (Lean
//                   `{ id : ID, key : Nat }`) = the same 32 bytes via
//                   `v.id.bytes.bytes.val`. A UID's Move layout is
//                   exactly its ID; `key` is a MODEL-ONLY projection
//                   (`ObjectNatives.lean`) and is NEVER serialized.
//   * Bag / ObjectBag (Lean `{ id : UID, size : u64, storage }`) and
//     Table / ObjectTable (Lean `{ id : UID, size : u64,
//                   dynamic_fields }`) = `bcsUIntBe 32
//                    v.id.id.bytes.bytes.val ++ bcsUIntLe 8 v.size.val`.
//                   Move gives all four exactly `{ id: UID, size: u64 }`;
//                   the entries live in dynamic-field storage, so the
//                   Lean-only contents field (`storage` /
//                   `dynamic_fields`) is NEVER part of the BCS. The UID
//                   address path is `id`(UID)`.id`(ID)`.bytes`(Address)
//                   `.bytes`(BoundedNat)`.val`, per `ObjectNatives.lean`.
//   * VecSet<T> (Lean `{ contents : List T }`) reduces to the generic
//                   struct rule over its single `vector` field ->
//                   `bcsUleb128 v.contents.length ++ flatMap ...`.
//                   Unlike Option, a VecSet IS a vector on the wire.
//   * type param i (only reachable INSIDE a wrapping arm, where the
//                   struct's i-th param maps to the code `aᵢ`) =
//                   `<Universe>.serialize aᵢ v` -- structural recursion
//                   on the strict subterm `aᵢ`.
//
// A struct whose transitive field graph is self-recursive THROUGH a
// vector or Option (e.g. `Node { children : vector<Node> }`) cannot be
// inlined without a `partial def`, so its arm falls back to `[]` (logged
// via `log_serialize_skip`). Direct struct-in-struct recursion is
// already rejected by `struct_def::ensure_type_supports_decidable_eq`.
//
// Which REGISTERED natives get real bytes at all is decided by
// [`NATIVE_BCS`] below -- see its doc comment for why `is_native` is
// not, by itself, an answer to that question.

struct SerializeCtx<'a> {
    program: &'a Program,
    /// The universe's own `serialize` name, used for the recursive call
    /// on a type-param's code: `"TyCode.serialize"` / `"BagU.serialize"`.
    self_serialize: &'a str,
}

fn fresh_binder(n: &mut usize) -> String {
    let s = format!("x{}", *n);
    *n += 1;
    s
}

/// Lean expression of type `List (BoundedNat (2^8))` giving the BCS
/// bytes of the value denoted by `val` (a Lean expression) at Move type
/// `ty`. `tp_arg_codes[i]` is the universe code bound to type-param `i`
/// in the enclosing wrapping arm (empty for a leaf arm). `visiting`
/// tracks the struct ids currently being inlined so vector/Option-
/// mediated self-recursion is detected and rejected (returns `Err`).
fn serialize_field_expr(
    ty: &Type,
    val: &str,
    cx: &SerializeCtx,
    tp_arg_codes: &[String],
    visiting: &mut Vec<StructId>,
    binder: &mut usize,
) -> Result<String, String> {
    match ty {
        Type::UInt(8) => Ok(format!("[{}]", val)),
        Type::UInt(bits @ (16 | 32 | 64 | 128 | 256)) => {
            Ok(format!("bcsUIntLe {} {}.val", bits / 8, val))
        }
        Type::UInt(other) => Err(format!("unsupported integer width u{}", other)),
        Type::Bool => Ok(format!(
            "[if {} then (1 : BoundedNat (2^8)) else (0 : BoundedNat (2^8))]",
            val
        )),
        Type::Address => Ok(format!("bcsUIntBe 32 {}.bytes.val", val)),
        Type::Vector(inner) => {
            if matches!(inner.as_ref(), Type::UInt(8)) {
                Ok(format!("bcsUleb128 {v}.length ++ {v}", v = val))
            } else {
                let x = fresh_binder(binder);
                let inner_expr =
                    serialize_field_expr(inner, &x, cx, tp_arg_codes, visiting, binder)?;
                Ok(format!(
                    "bcsUleb128 {v}.length ++ ({v}.flatMap (fun {x} => {inner}))",
                    v = val,
                    x = x,
                    inner = inner_expr
                ))
            }
        }
        Type::TypeParam(i) => match tp_arg_codes.get(*i as usize) {
            Some(code) => Ok(format!("{} {} {}", cx.self_serialize, code, val)),
            None => Err(format!("type param {} not bound to a code", i)),
        },
        Type::Struct {
            struct_id,
            type_args,
        } => serialize_struct_value(
            *struct_id,
            type_args,
            val,
            cx,
            tp_arg_codes,
            visiting,
            binder,
        ),
        Type::Reference(inner) => {
            serialize_field_expr(inner, val, cx, tp_arg_codes, visiting, binder)
        }
        Type::Unit | Type::Prop | Type::Tuple(_) | Type::MutableRef { .. } => {
            Err(format!("unserializable field type {:?}", ty))
        }
    }
}

/// How a REGISTERED native struct -- one listed in
/// `stage_02_ir_cfg::natives::NATIVE_STRUCTS` -- serializes.
///
/// `is_native` on its own is NOT an answer to "does this type have
/// BCS bytes". It means only that the Lean PRELUDE, not the renderer,
/// owns the `structure` declaration (`render::mod`'s emitter skips
/// native structs entirely); `stage_02_ir_cfg::module_lift::lift_struct`
/// still records the Move field list verbatim for every struct, native
/// or not. So whether the generic field walk is CORRECT depends on
/// whether the prelude's hand-written Lean structure exposes those same
/// fields -- a per-type fact, recorded in [`NATIVE_BCS`].
///
/// Treating `is_native` as "no bytes" is what made every Move `String`
/// (fixed earlier), and then every `ID` / `UID` / `Table` / `VecSet`,
/// serialize to NOTHING.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(super) enum NativeBcs {
    /// The prelude's Lean structure carries the Move fields under the
    /// same names, so the generic walk below IS Move's BCS. It may
    /// carry MODEL-ONLY extras on top (`UID.key`, `Bag.storage`,
    /// `Table.dynamic_fields`); those sit after the Move fields in the
    /// Lean declaration and the walk never reaches them, because it
    /// iterates the IR (= Move) field list, not the Lean one.
    Walk,
    /// Handled by an explicit arm ABOVE, because the byte format is not
    /// the generic struct rule (`option::Option`'s 0/1 tag) or the
    /// projection path is spelled out by hand (`bag::Bag`).
    Special,
    /// The rendered Lean type does NOT carry the Move fields, so the
    /// walk cannot be expressed at all -- serialize to `[]`.
    Opaque,
    /// Real-fielded and walkable in principle, but NOT yet flipped:
    /// turning one of these on changes the bytes at a live call site in
    /// a corpus this change was not validated against, so it needs its
    /// own regen + proof pass. Serializes to `[]` exactly like
    /// [`NativeBcs::Opaque`] -- the distinction is the census: these
    /// rows record a KNOWN-wrong encoding with a known fix (change the
    /// row to `Walk`), not a type that has no bytes.
    ///
    /// The case worth naming is `type_name::TypeName`. Concrete
    /// `bcs::to_bytes<TypeName>` is routed to `Type_nameNatives.to_bytes`
    /// (real bytes: a length prefix plus the FQN) and never reaches this
    /// universe; momentum's `comparator::compare_spec<X>` is GENERIC, so
    /// it does. A 2026-08-02 probe asked whether that obligation is
    /// therefore proved over EMPTY byte strings, and the answer is NO:
    /// the theorem quantifies over `t_tv0` and its `HasCode` instance, so
    /// it must hold at every arm, and its proof `generalize`s both
    /// `Bcs.to_bytes` applications to opaque byte lists before any
    /// byte-level reasoning. Flipping this row cannot refute it -- the
    /// change is a delta inside a definition the proof never unfolds.
    /// So `Deferred` here records a knowingly-wrong encoding, not a
    /// latent vacuity.
    Deferred,
}

/// Classification of EVERY entry in
/// `stage_02_ir_cfg::natives::NATIVE_STRUCTS`, keyed on
/// [`Struct::qualified_name`] (`<module>::<Name>`, which is what the IR
/// carries -- no two registered natives share one). Evidence for each
/// verdict is the prelude's `structure` declaration under
/// `lemmas/natives/**` versus the Move source's field list.
///
/// A registered native MISSING from this table falls back to
/// [`NativeBcs::Opaque`] -- the conservative pre-existing behavior. Add
/// a row here whenever you add one to `NATIVE_STRUCTS`; the census is
/// pinned by `render::tests::serialize`.
pub(super) const NATIVE_BCS: &[(&str, NativeBcs)] = &[
    // ---- MoveStdlib ----
    // `abbrev Integer := Int` / `abbrev Real := Rat`: spec-only numeric
    // types with no Lean fields to project at all.
    ("integer::Integer", NativeBcs::Opaque),
    ("real::Real", NativeBcs::Opaque),
    // `{ bytes : vector<u8> }`; explicit arm above (it must NOT gain the
    // generic walk's extra parens -- the emitted text is pinned).
    ("string::String", NativeBcs::Special),
    // `{ name : ascii::String }` on both sides. Walkable; the only
    // consumer is momentum's generic `compare_spec<X>`, whose proof is
    // encoder-agnostic (see `NativeBcs::Deferred`), so flipping this is a
    // regen-and-check, not a proof risk.
    ("type_name::TypeName", NativeBcs::Deferred),
    // ---- Sui ----
    ("bag::Bag", NativeBcs::Special),
    // Move declares these five with NO fields (`public struct G1 {}`);
    // move_model reports the compiler's synthetic `dummy_field : bool`,
    // which the prelude's genuinely-empty `structure G1 where` does not
    // have. Nothing to serialize.
    ("bls12381::G1", NativeBcs::Opaque),
    ("bls12381::G2", NativeBcs::Opaque),
    ("bls12381::GT", NativeBcs::Opaque),
    ("bls12381::Scalar", NativeBcs::Opaque),
    ("bls12381::UncompressedG1", NativeBcs::Opaque),
    // Registered so their Move bodies are not translated, but the
    // prelude defines no Lean `structure` for them at all -- only
    // `ConfigNatives.read_setting_impl`, which takes the config /
    // setting ADDRESSES rather than the objects. There is no Lean type
    // whose fields we could walk.
    ("config::Config", NativeBcs::Opaque),
    ("config::Setting", NativeBcs::Opaque),
    ("config::SettingData", NativeBcs::Opaque),
    // Everything from here to `object::ID` is real-fielded and matches
    // its prelude structure 1:1 (checked against the sui-framework
    // sources), but no corpus in this change's validation set exercises
    // it -- see `NativeBcs::Deferred`.
    ("dynamic_field::Field", NativeBcs::Deferred),
    ("dynamic_object_field::Wrapper", NativeBcs::Deferred),
    ("ecdsa_k1::KeyPair", NativeBcs::Deferred),
    ("funds_accumulator::Withdrawal", NativeBcs::Deferred),
    ("groth16::Curve", NativeBcs::Deferred),
    ("groth16::PreparedVerifyingKey", NativeBcs::Deferred),
    ("groth16::ProofPoints", NativeBcs::Deferred),
    ("groth16::PublicProofInputs", NativeBcs::Deferred),
    ("group_ops::Element", NativeBcs::Deferred),
    (
        "nitro_attestation::NitroAttestationDocument",
        NativeBcs::Deferred,
    ),
    ("nitro_attestation::PCREntry", NativeBcs::Deferred),
    // ---- validated `Walk` rows (sui-system staking corpus) ----
    // `{ bytes : address }` -> the 32 big-endian address bytes.
    ("object::ID", NativeBcs::Walk),
    // `{ id : ID, key : Nat := id.bytes.bytes.val }`: `key` is a
    // model-only map key, not a Move field, and is never reached.
    ("object::UID", NativeBcs::Walk),
    ("object_bag::ObjectBag", NativeBcs::Special),
    // Move declares `ObjectTable` byte-identically to `Table` (and to
    // `Bag` / `ObjectBag`, whose hard-coded arm emits the same two
    // projections), so the pair moves together -- shipping one fixed and
    // its twin broken would be a landmine.
    ("object_table::ObjectTable", NativeBcs::Walk),
    ("random::Random", NativeBcs::Deferred),
    ("random::RandomGenerator", NativeBcs::Deferred),
    ("random::RandomInner", NativeBcs::Deferred),
    ("table::Table", NativeBcs::Walk),
    ("transfer::Receiving", NativeBcs::Deferred),
    ("tx_context::TxContext", NativeBcs::Deferred),
    // `VecMap { contents : vector<Entry<K, V>> }` and
    // `Entry { key : K, value : V }` on both sides, field-for-field, so
    // the generic walk is Move's BCS: `bcsUleb128 len ++ flatMap (key
    // bytes ++ value bytes)`. The pair moves together -- an `Entry` left
    // deferred would silently zero out every entry of a walked `VecMap`.
    ("vec_map::Entry", NativeBcs::Walk),
    ("vec_map::VecMap", NativeBcs::Walk),
    ("vec_set::VecSet", NativeBcs::Walk),
    // Same as `config::*`: registered, but the prelude defines no Lean
    // structure for either (no `*Natives.lean` sibling exists).
    ("zklogin_verified_id::VerifiedID", NativeBcs::Opaque),
    ("zklogin_verified_issuer::VerifiedIssuer", NativeBcs::Opaque),
];

fn native_bcs_shape(qualified_name: &str) -> NativeBcs {
    NATIVE_BCS
        .iter()
        .find(|(name, _)| *name == qualified_name)
        .map(|(_, shape)| *shape)
        .unwrap_or(NativeBcs::Opaque)
}

/// True for the field list move_model synthesizes for a Move struct with
/// NO source fields: a single `dummy_field : bool`. The renderer emits
/// that field for ordinary structs (so `sui::SUI` really does serialize
/// to one byte), but a native's hand-written prelude `structure` is
/// genuinely empty, so walking would emit `v.dummy_field` and fail to
/// elaborate. Demotes a [`NativeBcs::Walk`] row to `[]` if the upstream
/// Move framework ever drops that type's fields, turning a would-be
/// lake-build break back into the conservative empty encoding.
fn has_synthetic_placeholder_fields(s: &Struct) -> bool {
    s.fields.len() == 1 && s.fields[0].name == "dummy_field"
}

/// BCS bytes of a struct / enum value `val` at struct `struct_id`
/// instantiated with `type_args`. Handles the special-cased shapes
/// (Option, Bag / ObjectBag, `string::String`), the opaque-native `[]`
/// fallback, and the generic field walk.
fn serialize_struct_value(
    struct_id: StructId,
    type_args: &[Type],
    val: &str,
    cx: &SerializeCtx,
    tp_arg_codes: &[String],
    visiting: &mut Vec<StructId>,
    binder: &mut usize,
) -> Result<String, String> {
    let s = cx
        .program
        .structs
        .get(&struct_id)
        .ok_or_else(|| format!("unknown struct id {}", struct_id))?;

    // Option<T>: BCS's 0/1-tag encoding. Its Move layout is
    // `{ vec : vector<T> }`, but BCS never treats it as a vector.
    if s.qualified_name == "option::Option" {
        let elem = type_args
            .first()
            .ok_or_else(|| "option::Option without a type arg".to_string())?;
        let vec_field = s
            .fields
            .first()
            .map(|f| escape::escape_identifier(&f.name))
            .ok_or_else(|| "option::Option has no field".to_string())?;
        let x = fresh_binder(binder);
        let elem_expr = serialize_field_expr(elem, &x, cx, tp_arg_codes, visiting, binder)?;
        return Ok(format!(
            "(match {val}.{vec} with | [] => [(0 : BoundedNat (2^8))] | {x} :: _ => (1 : BoundedNat (2^8)) :: ({elem}))",
            val = val,
            vec = vec_field,
            x = x,
            elem = elem_expr
        ));
    }

    // Bag / ObjectBag: 32-byte object-id address ++ 8-byte LE size. The
    // heterogeneous contents are NEVER serialized (Move's BCS of a Bag is
    // exactly its `UID` + `u64` fields).
    if s.qualified_name == "bag::Bag" || s.qualified_name == "object_bag::ObjectBag" {
        return Ok(format!(
            "bcsUIntBe 32 {val}.id.id.bytes.bytes.val ++ bcsUIntLe 8 {val}.size.val",
            val = val
        ));
    }

    // `std::string::String`: `bcsUleb128 len ++ bytes`, i.e. exactly the
    // `vector<u8>` rule applied to its single field. It is a REGISTERED
    // native (the prelude owns `MoveString.MoveString`), but unlike the
    // opaque natives its Move field `bytes : vector<u8>` is real and is
    // the rendered Lean structure's only field, so the generic walk is
    // already correct -- run it here, ahead of the `is_native` catch-all
    // below, which would otherwise serialize every Move `String` to
    // NOTHING. (`ascii::String` and `url::Url` are not registered
    // natives, so they reach the generic walk on their own and already
    // emit the length prefix.)
    if s.qualified_name == "string::String" {
        let f = s
            .fields
            .first()
            .ok_or_else(|| "string::String has no field".to_string())?;
        let ft = substitute_type_params(&f.field_type, type_args);
        let fval = format!("{}.{}", val, escape::escape_identifier(&f.name));
        return serialize_field_expr(&ft, &fval, cx, tp_arg_codes, visiting, binder);
    }

    // Native struct that does not get the walk. Either the prelude
    // renders it WITHOUT the Move fields -- no fields to project
    // (`bls12381::G1`, whose IR carries only the compiler's synthetic
    // `dummy_field`), or no Lean `structure` at all (`config::*`,
    // `zklogin_verified_*`) -- in which case field-walking would emit
    // accessors that do not elaborate; or it is `Deferred`, i.e. real
    // -fielded but not yet validated against the corpora that would see
    // the new bytes. Either way, `[]`.
    //
    // This is NOT all of `is_native`: [`NATIVE_BCS`] classifies every
    // registered native, and the `Walk` ones (`object::ID` / `UID`,
    // `table::Table` / `ObjectTable`, `vec_set::VecSet`) fall through to
    // the generic walk below, which is exactly Move's BCS for them.
    if s.is_native
        && (native_bcs_shape(&s.qualified_name) != NativeBcs::Walk
            || has_synthetic_placeholder_fields(s))
    {
        return Ok("[]".to_string());
    }

    if visiting.contains(&struct_id) {
        return Err(format!(
            "self-recursive struct {} (vector/Option-mediated)",
            s.qualified_name
        ));
    }
    visiting.push(struct_id);

    let result = if let Some(variants) = &s.variants {
        // Enum: bcsUleb128(variant tag) ++ variant fields.
        let mut arms: Vec<String> = Vec::new();
        for v in variants {
            let mut pat_binders: Vec<String> = Vec::new();
            let mut parts: Vec<String> = vec![format!("bcsUleb128 {}", v.tag)];
            let mut arm_err: Option<String> = None;
            for f in &v.fields {
                let b = fresh_binder(binder);
                let ft = substitute_type_params(&f.field_type, type_args);
                match serialize_field_expr(&ft, &b, cx, tp_arg_codes, visiting, binder) {
                    Ok(e) => {
                        pat_binders.push(b.clone());
                        parts.push(format!("({})", e));
                    }
                    Err(e) => {
                        arm_err = Some(e);
                        break;
                    }
                }
            }
            if let Some(e) = arm_err {
                arms.clear();
                arms.push(format!("__ERR:{}", e));
                break;
            }
            let pat: String = pat_binders.iter().map(|b| format!(" {}", b)).collect();
            arms.push(format!(
                "| .{}{} => {}",
                escape::escape_identifier(&v.name),
                pat,
                parts.join(" ++ ")
            ));
        }
        if let Some(first) = arms.first() {
            if let Some(reason) = first.strip_prefix("__ERR:") {
                Err(reason.to_string())
            } else {
                Ok(format!("(match {} with {})", val, arms.join(" ")))
            }
        } else {
            // No variants: an uninhabited enum never has a value here.
            Ok("[]".to_string())
        }
    } else {
        // Plain struct: fields concatenated in declaration order.
        let mut parts: Vec<String> = Vec::new();
        let mut err: Option<String> = None;
        for f in &s.fields {
            let ft = substitute_type_params(&f.field_type, type_args);
            let fval = format!("{}.{}", val, escape::escape_identifier(&f.name));
            match serialize_field_expr(&ft, &fval, cx, tp_arg_codes, visiting, binder) {
                Ok(e) => parts.push(format!("({})", e)),
                Err(e) => {
                    err = Some(e);
                    break;
                }
            }
        }
        match err {
            Some(e) => Err(e),
            None if parts.is_empty() => Ok("[]".to_string()),
            None => Ok(parts.join(" ++ ")),
        }
    };

    visiting.pop();
    result
}

/// Note (stderr) that a code's `serialize` arm is kept as `[]` because
/// its value graph can't be inlined. Deduplicated so the per-module
/// render passes (TyCode + BagU) don't spam the same line.
fn log_serialize_skip(
    context: Option<&super::context::RenderContext<'_>>,
    name: &str,
    reason: &str,
) {
    if let Some(context) = context {
        context.log_serialize_skip_once(name, reason);
    } else {
        eprintln!("[bcs-serialize] keeping [] for `{name}`: {reason}");
    }
}

/// Lean lambda body for a LEAF code's `serialize` arm. Real BCS for
/// primitives, `Address`, `vector<_>`, and inlinable (acyclic) leaf
/// structs / enums; `fun _ => []` (logged) for a leaf struct whose value
/// graph is self-recursive. `self_serialize` is the universe's own
/// `serialize` name for the (unreachable-in-a-leaf) type-param recursion.
pub(crate) fn bcs_serialize_body(leaf: &Type, program: &Program, self_serialize: &str) -> String {
    bcs_serialize_body_in(leaf, program, self_serialize, None)
}

pub(crate) fn bcs_serialize_body_in(
    leaf: &Type,
    program: &Program,
    self_serialize: &str,
    context: Option<&super::context::RenderContext<'_>>,
) -> String {
    let cx = SerializeCtx {
        program,
        self_serialize,
    };
    let mut visiting: Vec<StructId> = Vec::new();
    let mut binder = 0usize;
    match serialize_field_expr(leaf, "v", &cx, &[], &mut visiting, &mut binder) {
        Ok(expr) => format!("fun v => {}", expr),
        Err(reason) => {
            log_serialize_skip(context, &mangle(leaf, program), &reason);
            "fun _ => []".to_string()
        }
    }
}

/// Lean lambda body for a WRAPPING code's `serialize` arm. The value is
/// the struct applied to `interp aᵢ`; walk its fields under the identity
/// type-arg substitution, with `aᵢ` as the per-param recursion codes so a
/// `TypeParam(i)` field emits `<self_serialize> aᵢ`. Falls back to
/// `fun _ => []` (logged) when the walk can't be completed.
pub(crate) fn bcs_serialize_wrapping_body(
    w: &WrappingStruct,
    program: &Program,
    self_serialize: &str,
) -> String {
    bcs_serialize_wrapping_body_in(w, program, self_serialize, None)
}

pub(crate) fn bcs_serialize_wrapping_body_in(
    w: &WrappingStruct,
    program: &Program,
    self_serialize: &str,
    context: Option<&super::context::RenderContext<'_>>,
) -> String {
    let cx = SerializeCtx {
        program,
        self_serialize,
    };
    let mut visiting: Vec<StructId> = Vec::new();
    let mut binder = 0usize;
    let tp_arg_codes: Vec<String> = (0..w.arity).map(|i| format!("a{}", i)).collect();
    let type_args: Vec<Type> = (0..w.arity).map(|i| Type::TypeParam(i as u16)).collect();
    match serialize_struct_value(
        w.struct_id,
        &type_args,
        "v",
        &cx,
        &tp_arg_codes,
        &mut visiting,
        &mut binder,
    ) {
        Ok(expr) => format!("fun v => {}", expr),
        Err(reason) => {
            log_serialize_skip(context, &wrapping_ctor_name(w, program), &reason);
            "fun _ => []".to_string()
        }
    }
}

pub fn write_ty_code_interp_file(
    universe: &DynTypeUniverse,
    context: &super::context::RenderContext<'_>,
    output_dir: &Path,
    lemma_libs: &BTreeSet<String>,
) -> io::Result<()> {
    let program = context.program;
    let gen_dir = output_dir.join("Generated");
    fs::create_dir_all(&gen_dir)?;
    let path = gen_dir.join("TyCodeInterp.lean");

    let mut out = String::new();
    out.push_str("-- Generated per project by the lean-pipeline renderer.\n");
    out.push_str("-- See `plans/lean-pipeline/dynamic-typing-via-repr-design.md`.\n\n");

    // Collect every package whose types we reference, importing _Types
    // for non-lemma packages and the regular module for lemma packages.
    let mut packages: HashSet<(String, String, bool)> = HashSet::new();
    for t in &universe.leaves {
        collect_struct_modules(t, program, lemma_libs, &mut packages);
    }
    for w in &universe.wrappings {
        if let Some(s) = program.structs.get(&w.struct_id) {
            if let Some(m) = program.modules.get(&s.module_id) {
                let pkg = if m.package_name.is_empty() {
                    "NewPipeline".to_string()
                } else {
                    m.package_name.clone()
                };
                let ns = escape::module_name_to_namespace(&m.name);
                let is_lemma = lemma_libs.contains(&pkg);
                packages.insert((pkg, ns, is_lemma));
            }
        }
    }

    out.push_str("import Prelude.BoundedNat\n");
    out.push_str("import Prelude.Universe\n");
    out.push_str("import Generated.TyCode\n");
    // Import each referenced module's regular `_Types`. Bag-containing
    // `_Types` files now import `Generated.BagUInterp` (not
    // `TyCodeInterp`), and `BagU` excludes Bag-containing structs, so
    // importing them here cannot close a `TyCodeInterp -> _Types ->
    // TyCodeInterp` cycle -- the skeleton split is gone.
    // See `plans/lean-pipeline/split-bag-df-universes.md`.
    let mut import_lines: Vec<String> = Vec::new();
    for (pkg, ns, is_lemma) in packages.iter() {
        if *is_lemma {
            if super::lemma_module_has_types_leaf(context, pkg, ns) {
                import_lines.push(format!("import {}.{}_Types\n", pkg, ns));
            } else {
                import_lines.push(format!("import {}.{}\n", pkg, ns));
            }
        } else {
            import_lines.push(format!("import {}.{}_Types\n", pkg, ns));
        }
    }
    import_lines.sort();
    import_lines.dedup();
    for line in import_lines {
        out.push_str(&line);
    }
    out.push('\n');
    out.push_str("set_option linter.unusedVariables false\n\n");

    // Interp cases.
    out.push_str("abbrev TyCode.interp : TyCode -> Type\n");
    out.push_str("  | .dummy => Unit\n");
    for leaf in &universe.leaves {
        let stem = mangle(leaf, program);
        let ty_str = ty::type_to_string(leaf, program, None, None);
        out.push_str(&format!("  | .{} => {}\n", stem, ty_str));
    }
    for w in &universe.wrappings {
        let stem = wrapping_ctor_name(w, program);
        let s = program
            .structs
            .get(&w.struct_id)
            .expect("wrapping struct missing");
        let module = program
            .modules
            .get(&s.module_id)
            .expect("struct module missing");
        let namespace = escape::module_render_namespace(&module.package_name, &module.name);
        let struct_path = format!(
            "_root_.{}.{}",
            namespace,
            escape::escape_struct_name(&s.name),
        );
        let pattern_args: String = (0..w.arity).map(|i| format!(" a{}", i)).collect();
        let interp_args: String = (0..w.arity)
            .map(|i| format!(" (TyCode.interp a{})", i))
            .collect();
        out.push_str(&format!(
            "  | .{}{} => {}{}\n",
            stem, pattern_args, struct_path, interp_args
        ));
    }
    out.push('\n');

    // Recursive `TyCode.decEqInterp`: gives `DecidableEq` for `interp u`
    // at every code `u`. Wrappings recurse on each type-arg first to bring
    // the inner `DecidableEq (interp aᵢ)` into scope, so `inferInstance`
    // can compose `DecidableEq (Wrap T0 ... Tn)` from the per-T instances.
    out.push_str(
        "@[reducible] def TyCode.decEqInterp : \u{2200} u : TyCode, DecidableEq (TyCode.interp u)\n",
    );
    out.push_str("  | .dummy => inferInstance\n");
    for leaf in &universe.leaves {
        let stem = mangle(leaf, program);
        out.push_str(&format!("  | .{} => inferInstance\n", stem));
    }
    for w in &universe.wrappings {
        let stem = wrapping_ctor_name(w, program);
        let pattern_args: String = (0..w.arity).map(|i| format!(" a{}", i)).collect();
        out.push_str(&format!("  | .{}{} =>\n", stem, pattern_args));
        for i in 0..w.arity {
            out.push_str(&format!(
                "    have : DecidableEq (TyCode.interp a{0}) := TyCode.decEqInterp a{0}\n",
                i
            ));
        }
        out.push_str("    inferInstance\n");
    }
    out.push('\n');

    // `TyCode.typeName`: each code's Move fully-qualified type name.
    // Used by `Type_name.get` (via `Universe.typeName`) so coin-ordering
    // byte comparisons match Move. Wrappings recurse into their type-arg
    // codes to render `Base<argName, ...>`, mirroring Move's generic
    // `type_name` form.
    out.push_str("def TyCode.typeName : TyCode \u{2192} String\n");
    out.push_str("  | .dummy => \"dummy\"\n");
    for leaf in &universe.leaves {
        let stem = mangle(leaf, program);
        out.push_str(&format!(
            "  | .{} => \"{}\"\n",
            stem,
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

    // `TyCode.serialize`: real BCS bytes of a value at its code. Primitive
    // leaves serialize exactly (uN, bool, address, vec<u8>); leaf structs /
    // enums and wrappings walk their fields in declaration order per the
    // EXACT BYTE FORMAT documented atop `serialize_field_expr` (Phase 2's
    // Lean decoder mirrors it). `bcs::to_bytes<X>` reaches this generically
    // through the framework `Bcs.to_bytes` stub (e.g. `comparator::
    // compare<X>`, value-derived keys, and validator-metadata validation).
    // A struct whose value graph is vector/Option-mediated self-recursive
    // stays `[]` (logged): inlining it would need a `partial def`. Concrete
    // `bcs::to_bytes<TypeName>` is still routed to a per-type native at the
    // call site, not here.
    out.push_str(
        "def TyCode.serialize : (u : TyCode) \u{2192} TyCode.interp u \u{2192} List (BoundedNat (2^8))\n",
    );
    out.push_str("  | .dummy => fun _ => []\n");
    for leaf in &universe.leaves {
        let stem = mangle(leaf, program);
        out.push_str(&format!(
            "  | .{} => {}\n",
            stem,
            bcs_serialize_body_in(leaf, program, "TyCode.serialize", Some(context))
        ));
    }
    for w in &universe.wrappings {
        let stem = wrapping_ctor_name(w, program);
        let pat: String = (0..w.arity).map(|i| format!(" a{}", i)).collect();
        out.push_str(&format!(
            "  | .{}{} => {}\n",
            stem,
            pat,
            bcs_serialize_wrapping_body_in(w, program, "TyCode.serialize", Some(context))
        ));
    }
    out.push('\n');

    out.push_str("instance : Universe TyCode where\n");
    out.push_str("  decEq       := inferInstance\n");
    out.push_str("  interp      := TyCode.interp\n");
    out.push_str("  decEqInterp := TyCode.decEqInterp\n");
    out.push_str("  typeName    := TyCode.typeName\n");
    out.push_str("  serialize   := TyCode.serialize\n\n");

    // Concrete HasCode instances for leaves.
    for leaf in &universe.leaves {
        let stem = mangle(leaf, program);
        let ty_str = ty::type_to_string(leaf, program, None, None);
        out.push_str(&format!(
            "instance : HasCode TyCode ({}) := \u{27E8}.{}, rfl\u{27E9}\n",
            ty_str, stem
        ));
    }

    // Derived HasCode instances for wrappings: a struct shape (S, n)
    // gets `instance [HasCode TyCode T0] ... [HasCode TyCode Tn] :
    //          HasCode TyCode (S T0 ... Tn) where
    //   code := .stem T0_inst.code ... Tn_inst.code
    //   proof := by show S (Universe.interp ...) ... = S T0 ...; rw [...]`
    for w in &universe.wrappings {
        let stem = wrapping_ctor_name(w, program);
        let s = program
            .structs
            .get(&w.struct_id)
            .expect("wrapping struct missing");
        let module = program
            .modules
            .get(&s.module_id)
            .expect("struct module missing");
        let namespace = escape::module_render_namespace(&module.package_name, &module.name);
        let struct_path = format!(
            "_root_.{}.{}",
            namespace,
            escape::escape_struct_name(&s.name),
        );
        // [hc_i : HasCode TyCode T_i] constraints
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

    fs::write(&path, &out)?;
    Ok(())
}

pub fn collect_struct_modules(
    ty: &Type,
    program: &Program,
    lemma_libs: &BTreeSet<String>,
    packages: &mut HashSet<(String, String, bool)>,
) {
    match ty {
        Type::Struct {
            struct_id,
            type_args,
        } => {
            if let Some(s) = program.structs.get(struct_id) {
                if let Some(m) = program.modules.get(&s.module_id) {
                    let pkg = if m.package_name.is_empty() {
                        "NewPipeline".to_string()
                    } else {
                        m.package_name.clone()
                    };
                    let ns = escape::module_name_to_namespace(&m.name);
                    let is_lemma = lemma_libs.contains(&pkg);
                    packages.insert((pkg, ns, is_lemma));
                }
            }
            for arg in type_args {
                collect_struct_modules(arg, program, lemma_libs, packages);
            }
        }
        Type::Vector(inner) | Type::Reference(inner) => {
            collect_struct_modules(inner, program, lemma_libs, packages);
        }
        Type::MutableRef { inner, root } => {
            collect_struct_modules(inner, program, lemma_libs, packages);
            collect_struct_modules(root, program, lemma_libs, packages);
        }
        Type::Tuple(ts) => {
            for t in ts {
                collect_struct_modules(t, program, lemma_libs, packages);
            }
        }
        _ => {}
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::{Block, BlockTail, Effects, Function, FunctionKind, Signature};

    fn user_module() -> Module {
        Module {
            name: "m".to_string(),
            package_name: "UserPkg".to_string(),
            address: String::new(),
            required_imports: Vec::new(),
            is_native: false,
        }
    }

    fn one_typaram_fn(name: &str, body: Block) -> Function {
        Function {
            module: 0,
            name: name.to_string(),
            signature: Signature {
                type_params: vec!["T".to_string()],
                params: Vec::new(),
                return_type: Type::Unit,
            },
            body,
            kind: FunctionKind::Source,
            effects: Effects::PURE,
            explicit_pure: true,
        }
    }

    // A user-package callee binds `[HasCode TyCode T]` unconditionally, so a
    // caller passing its own type param there must carry one even though the
    // callee's own tycode taint bit is clear. Without this the caller drops the
    // constraint whenever ITS param is object-tainted (bluefin-timelock's
    // `Cap: key + store`: `object::id` in the spec, `dynamic_field::add` in the
    // impl) and the call fails to synthesize `HasCode TyCode`.
    #[test]
    fn user_package_callee_taints_the_callers_type_param() {
        let mut program = Program::default();
        program.modules.insert(0, user_module());
        program.functions.insert(
            0,
            one_typaram_fn(
                "callee",
                Block {
                    stmts: Vec::new(),
                    tail: BlockTail::Value(Expr::Unit),
                },
            ),
        );
        program.functions.insert(
            1,
            one_typaram_fn(
                "caller",
                Block {
                    stmts: Vec::new(),
                    tail: BlockTail::Value(Expr::Call {
                        fun: 0,
                        type_args: vec![Type::TypeParam(0)],
                        args: Vec::new(),
                    }),
                },
            ),
        );

        let obj_deps = std::collections::HashMap::from([(0, vec![false]), (1, vec![true])]);
        let deps = compute_tycode_typeparam_deps(&program, &obj_deps);
        assert_eq!(deps.get(&1).map(Vec::as_slice), Some(&[true][..]));
    }

    // The mirror case: an object-tainted callee param carries ObjType instead,
    // so a caller with no other tycode reason must NOT be forced into a
    // `HasCode TyCode` it cannot discharge (scallop's Bag-containing
    // `Obligation` is excluded from the TyCode universe).
    #[test]
    fn object_tainted_callee_param_does_not_taint_the_caller() {
        let mut program = Program::default();
        program.modules.insert(0, user_module());
        program.functions.insert(
            0,
            one_typaram_fn(
                "callee",
                Block {
                    stmts: Vec::new(),
                    tail: BlockTail::Value(Expr::Unit),
                },
            ),
        );
        program.functions.insert(
            1,
            one_typaram_fn(
                "caller",
                Block {
                    stmts: Vec::new(),
                    tail: BlockTail::Value(Expr::Call {
                        fun: 0,
                        type_args: vec![Type::TypeParam(0)],
                        args: Vec::new(),
                    }),
                },
            ),
        );

        let obj_deps = std::collections::HashMap::from([(0, vec![true]), (1, vec![true])]);
        let deps = compute_tycode_typeparam_deps(&program, &obj_deps);
        assert_eq!(deps.get(&1).map(Vec::as_slice), Some(&[false][..]));
    }

    // `coin_registry::new_currency_with_otw`: only the source reaches the
    // `types::is_one_time_witness` pin, so its `.aborts` companion and that
    // companion's `.cont_N` fragment are tainted by INHERITANCE alone. The
    // abort loop helper tail-calls the fragment yet belongs to neither family,
    // so it sees the taint only if the call edges are re-run afterwards.
    // Before that it rendered without `[HasCode __TyU T]` while its callee
    // bound one: "failed to synthesize HasCode ?m t_tv0".
    #[test]
    fn caller_of_a_fragment_tainted_by_inheritance_is_tainted() {
        use crate::ir::SpecKind;

        const OTW: usize = 0;
        const SOURCE: usize = 1;
        const ABORTS: usize = 2;
        const CONT: usize = 3;
        const LOOP: usize = 4;

        let lemma_module = |name: &str| Module {
            name: name.to_string(),
            package_name: "Sui".to_string(),
            address: String::new(),
            required_imports: Vec::new(),
            is_native: false,
        };
        let unit = || Block {
            stmts: Vec::new(),
            tail: BlockTail::Value(Expr::Unit),
        };
        let calls = |fun: usize| Block {
            stmts: Vec::new(),
            tail: BlockTail::Value(Expr::Call {
                fun,
                type_args: vec![Type::TypeParam(0)],
                args: Vec::new(),
            }),
        };

        let mut program = Program::default();
        program.modules.insert(0, lemma_module("coin_registry"));
        program.modules.insert(1, lemma_module("types"));
        let mut otw = one_typaram_fn("is_one_time_witness", unit());
        otw.module = 1;
        program.functions.insert(OTW, otw);
        program
            .functions
            .insert(SOURCE, one_typaram_fn("f", calls(OTW)));
        let mut aborts = one_typaram_fn("f.aborts", unit());
        aborts.kind = FunctionKind::Spec {
            kind: SpecKind::Aborts,
            target: SOURCE,
        };
        program.functions.insert(ABORTS, aborts);
        let mut cont = one_typaram_fn("f.aborts.cont_0", unit());
        cont.kind = FunctionKind::Synthetic;
        program.functions.insert(CONT, cont);
        let mut loop_body = one_typaram_fn("f.aborts.while_0", calls(CONT));
        loop_body.kind = FunctionKind::LoopBody {
            parent: ABORTS,
            slot: 0,
        };
        program.functions.insert(LOOP, loop_body);

        let deps = compute_tycode_typeparam_deps(&program, &std::collections::HashMap::new());
        assert_eq!(deps.get(&CONT).map(Vec::as_slice), Some(&[true][..]));
        assert_eq!(deps.get(&LOOP).map(Vec::as_slice), Some(&[true][..]));
    }
}
