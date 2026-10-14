//! Per-project closed-universe `ObjType` emission for object types.
//!
//! Parallel of `dyn_type_universe.rs` but with a different scope:
//! ObjType is the universe of types that flow through `transfer::*`
//! and `test_scenario::take_*` callsites. No cycle with user
//! `_Types.lean` files because user struct fields never reference
//! `ObjType`.

use std::collections::{BTreeSet, HashMap, HashSet};
use std::fs;
use std::io;
use std::path::Path;

use crate::ir::expr::{Block, BlockTail, Expr, Stmt};
use crate::ir::visit::{walk_expr_default, Visitor};
use crate::ir::{Program, StructId, Type};

use super::dyn_type_universe::{
    classify, leaf_fqn, mangle, struct_base_fqn, wrapping_ctor_name, WrappingStruct,
};
use super::escape;

/// True iff `sid`'s first field is typed `object::UID`, i.e. the
/// struct has Sui's `key` ability shape and therefore a usable
/// `Object.HasObjectId` instance. Phantom-token marker types (like
/// `USDC` / `UltraUSDC` that appear inside `Coin<USDC>`) live in
/// ObjType because they're type args at object-storage call sites,
/// but they don't carry an `id : UID` field; emitting a
/// `HasObjectId` instance for them produces lake-build errors
/// (`Invalid field id`).
///
/// For NATIVE structs (Sui framework types like `Coin`, `TreasuryCap`),
/// stage 2 lifts only the name + type-params without populating
/// fields, so the user-struct walk above can't see the `id: UID`
/// the Lean prelude declares for them. Whitelist the ones that
/// `lemmas/natives/Sui/*.lean` defines with `id : Object.UID` as
/// the first field -- the renderer-emitted `HasObjectId` body
/// `where uid s := s.id` resolves at Lean elaboration time against
/// those prelude struct definitions.
pub(crate) fn struct_has_uid_first_field(s: &crate::ir::Struct, program: &Program) -> bool {
    if !s.is_native {
        let Some(first) = s.fields.first() else {
            return false;
        };
        let Type::Struct {
            struct_id: inner_sid,
            ..
        } = &first.field_type
        else {
            return false;
        };
        let Some(inner) = program.structs.get(inner_sid) else {
            return false;
        };
        return inner.qualified_name == "object::UID";
    }
    // Native struct whitelist. The matching prelude definitions live
    // in `lemmas/natives/Sui/*.lean`. Keep this list in sync.
    let Some(m) = program.modules.get(&s.module_id) else {
        return false;
    };
    if m.package_name != "Sui" {
        return false;
    }
    // NOTE: coin (Coin / TreasuryCap / CoinMetadata) is translated from
    // source now, so its structs are non-native and get UID detection from
    // their real `id: UID` first field via the branch above. Only
    // genuinely-native object structs need whitelisting here.
    matches!(
        (m.name.as_str(), s.name.as_str()),
        ("object_table", "ObjectTable")
    )
}

fn has_uid_first_field(program: &Program, sid: &StructId) -> bool {
    program
        .structs
        .get(sid)
        .is_some_and(|s| struct_has_uid_first_field(s, program))
}

#[derive(Debug, Default)]
pub struct ObjTypeUniverse {
    pub leaves: Vec<Type>,
    pub wrappings: Vec<WrappingStruct>,
}

fn is_object_storage_call(program: &Program, fid: usize) -> bool {
    // Resolve the (module, name) pair from either translated
    // functions (`program.functions`) or native declarations
    // (`program.natives.decls`). User code calling `Sui::transfer::*`
    // resolves to native FunIds, so the natives.decls lookup is
    // required -- without it, ObjType comes up empty for projects
    // whose transfer/take_* calls all target natives.
    let Some(callee) = program.lookup_callee(fid) else {
        return false;
    };
    let name = callee.name();
    let Some(m) = program.modules.get(&callee.module()) else {
        return false;
    };
    if m.package_name != "Sui" {
        return false;
    }
    match m.name.as_str() {
        "transfer" => matches!(
            name,
            "transfer"
                | "public_transfer"
                | "share_object"
                | "public_share_object"
                | "freeze_object"
                | "public_freeze_object"
                | "receive"
                | "public_receive"
                | "party_transfer"
                | "public_party_transfer"
                | "transfer_impl"
                | "share_object_impl"
                | "freeze_object_impl"
                | "receive_impl"
                | "party_transfer_impl"
        ),
        "object" => matches!(
            name,
            // `object::id<T: key>(obj)` and friends take a generic
            // `obj: &T` and now read the object's UID via
            // `[HasObjectId T]` (see ObjectNatives::id). T is always a
            // key-type here (Move requires `T: key`), so tainting it is
            // safe -- it is never instantiated with a non-object type.
            "id" | "id_address" | "id_bytes" | "borrow_id"
        ),
        "test_scenario" => matches!(
            name,
            "take_shared"
                | "take_shared_by_id"
                | "take_from_address"
                | "take_from_address_by_id"
                | "take_from_sender"
                | "take_immutable"
                | "take_immutable_by_id"
                | "return_shared"
                | "return_to_address"
                | "return_to_sender"
                | "return_immutable"
                | "most_recent_id_shared"
                | "most_recent_id_for_address"
                | "most_recent_immutable_id"
                | "ids_for_address"
                | "allocate_receiving_ticket_for_object"
        ),
        _ => false,
    }
}

pub fn collect(program: &Program) -> ObjTypeUniverse {
    let deps = compute_obj_typeparam_deps(program);
    collect_with_deps(program, &deps)
}

pub(crate) fn collect_in(context: &super::context::RenderContext<'_>) -> ObjTypeUniverse {
    collect_with_deps(context.program, context.obj_typeparam_deps())
}

fn collect_with_deps(
    program: &Program,
    deps: &HashMap<crate::ir::FunId, Vec<bool>>,
) -> ObjTypeUniverse {
    let mut leaves: HashSet<Type> = HashSet::new();
    let mut wrappings: BTreeSet<WrappingStruct> = BTreeSet::new();
    for (_, f) in program.functions.iter() {
        walk_block_obj(&f.body, program, &mut leaves, &mut wrappings);
    }
    // A type passed at a callee slot that the taint pass constrains with
    // `HasCode ObjType` (e.g. the object arg of
    // `X::ownership::assert_owner`) must be in the universe too -- even
    // though that callsite is a user function, not a `transfer::*` /
    // `take_*` native. Reuse the SAME taint that emits those bounds
    // (`compute_obj_typeparam_deps`) to classify the type-arg at each
    // tainted slot, so its `HasCode ObjType` instance gets emitted.
    for (_, f) in program.functions.iter() {
        TaintedObjArgCollector {
            program,
            deps,
            leaves: &mut leaves,
            wrappings: &mut wrappings,
        }
        .visit_block(&f.body);
    }
    let mut leaf_vec: Vec<Type> = leaves.into_iter().collect();
    leaf_vec.sort_by(|a, b| mangle(a, program).cmp(&mangle(b, program)));
    ObjTypeUniverse {
        leaves: leaf_vec,
        wrappings: wrappings.into_iter().collect(),
    }
}

/// Adds to the ObjType universe every type-arg sitting at a callee slot
/// that the taint pass marks `HasCode ObjType` -- the membership the
/// transfer/take walk misses for objects that reach the universe only
/// through a user-defined object-typed helper (e.g. `assert_owner`).
struct TaintedObjArgCollector<'a> {
    program: &'a Program,
    deps: &'a HashMap<crate::ir::FunId, Vec<bool>>,
    leaves: &'a mut HashSet<Type>,
    wrappings: &'a mut BTreeSet<WrappingStruct>,
}

impl Visitor for TaintedObjArgCollector<'_> {
    fn visit_expr(&mut self, e: &Expr) {
        if let Expr::Call { fun, type_args, .. } = e {
            if let Some(tainted) = self.deps.get(fun) {
                for (i, t) in type_args.iter().enumerate() {
                    if tainted.get(i).copied().unwrap_or(false) {
                        classify(t, self.program, self.leaves, self.wrappings);
                    }
                }
            }
        }
        walk_expr_default(self, e);
    }
}

/// Per-function tainting of type parameters: which of a function's
/// type params transitively flow into a `Sui::transfer::*` or
/// `Sui::test_scenario::take_*` callsite's type arguments. For each
/// `(fid, i)` with `result[fid][i] == true`, the renderer must emit
/// `[HasCode _root_.ObjType T_i] [Object.HasObjectId T_i]` on that
/// type param so Lean's typeclass resolution succeeds at the call
/// site.
///
/// Precise per-typeparam tracking (rather than over-approximation
/// over all user functions) avoids breaking generic helpers like
/// `queue::new<T>` whose `T` is instantiated with non-object types
/// like `u64` -- those Lean instances don't exist and emitting the
/// constraint would make the call fail to elaborate.
///
/// Algorithm: forward fixpoint over the call graph. Each iteration
/// (a) finds direct calls to transfer/take_* natives and taints any
/// caller type-param that appears in their type_args, and (b)
/// propagates taint across user-function call edges: if callee G has
/// type-param index k tainted, and caller F passes its TypeParam(i)
/// at slot k of G's type_args, then F's type-param i becomes tainted.
/// Runs to a fixed point.
pub fn compute_obj_typeparam_deps(
    program: &Program,
) -> std::collections::HashMap<crate::ir::FunId, Vec<bool>> {
    let mut deps: std::collections::HashMap<crate::ir::FunId, Vec<bool>> =
        std::collections::HashMap::new();
    for (fid, f) in program.functions.iter() {
        deps.insert(*fid, vec![false; f.signature.type_params.len()]);
    }
    loop {
        let mut changed = false;
        let keys: Vec<crate::ir::FunId> = program.functions.keys().copied().collect();
        for fid in keys {
            let f = program.functions.get(&fid).expect("fid present");
            let mut local = deps.get(&fid).cloned().unwrap_or_default();
            let before = local.clone();
            walk_block_taint(&f.body, program, &deps, &mut local);
            if before != local {
                deps.insert(fid, local);
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
    super::dyn_type_universe::inherit_spec_companion_typeparam_deps(program, &mut deps);
    deps
}

fn walk_block_taint(
    block: &Block,
    program: &Program,
    deps: &std::collections::HashMap<crate::ir::FunId, Vec<bool>>,
    local: &mut Vec<bool>,
) {
    for stmt in &block.stmts {
        match stmt {
            Stmt::Let { value, .. } => walk_expr_taint(value, program, deps, local),
            Stmt::Eval(e) => walk_expr_taint(e, program, deps, local),
        }
    }
    match &block.tail {
        BlockTail::Value(e) => walk_expr_taint(e, program, deps, local),
        BlockTail::Break { value, .. } => walk_expr_taint(value, program, deps, local),
        BlockTail::Continue { value, .. } => walk_expr_taint(value, program, deps, local),
        BlockTail::Return(e) => walk_expr_taint(e, program, deps, local),
        BlockTail::ReturnFromBlock { value, .. } => walk_expr_taint(value, program, deps, local),
        BlockTail::Abort { code } => walk_expr_taint(code, program, deps, local),
    }
}

fn walk_expr_taint(
    expr: &Expr,
    program: &Program,
    deps: &std::collections::HashMap<crate::ir::FunId, Vec<bool>>,
    local: &mut Vec<bool>,
) {
    match expr {
        Expr::Borrow { step, base } => {
            for __pe in step.exprs() {
                walk_expr_taint(__pe, program, deps, local);
            }
            walk_expr_taint(base, program, deps, local);
        }
        Expr::Update { step, base, value } => {
            for __pe in step.exprs() {
                walk_expr_taint(__pe, program, deps, local);
            }
            walk_expr_taint(base, program, deps, local);
            walk_expr_taint(value, program, deps, local);
        }
        Expr::Call {
            fun,
            type_args,
            args,
            ..
        } => {
            handle_call_taint(*fun, type_args, program, deps, local);
            for a in args {
                walk_expr_taint(a, program, deps, local);
            }
        }
        Expr::Tuple(es) | Expr::Pack { fields: es, .. } => {
            for x in es {
                walk_expr_taint(x, program, deps, local);
            }
        }
        Expr::Unpack { value, .. }
        | Expr::Field { base: value, .. }
        | Expr::ReadRef(value)
        | Expr::ToProp(value)
        | Expr::ToBool(value) => walk_expr_taint(value, program, deps, local),
        Expr::WriteRef { reference, value } => {
            walk_expr_taint(reference, program, deps, local);
            walk_expr_taint(value, program, deps, local);
        }
        Expr::BinOp { lhs, rhs, .. } => {
            walk_expr_taint(lhs, program, deps, local);
            walk_expr_taint(rhs, program, deps, local);
        }
        Expr::UnOp { operand, .. } => walk_expr_taint(operand, program, deps, local),
        Expr::If {
            cond,
            then_branch,
            else_branch,
        } => {
            walk_expr_taint(cond, program, deps, local);
            walk_block_taint(then_branch, program, deps, local);
            walk_block_taint(else_branch, program, deps, local);
        }
        Expr::Match {
            selector, cases, ..
        } => {
            walk_expr_taint(selector, program, deps, local);
            for c in cases {
                walk_block_taint(&c.body, program, deps, local);
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
                walk_expr_taint(init, program, deps, local);
            }
            walk_block_taint(header, program, deps, local);
            walk_expr_taint(cond, program, deps, local);
            walk_block_taint(body, program, deps, local);
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

fn handle_call_taint(
    callee_fid: crate::ir::FunId,
    type_args: &[Type],
    program: &Program,
    deps: &std::collections::HashMap<crate::ir::FunId, Vec<bool>>,
    local: &mut Vec<bool>,
) {
    if is_object_storage_call(program, callee_fid) {
        for ta in type_args {
            collect_typeparams_into(ta, local);
        }
        return;
    }
    if let Some(callee_taint) = deps.get(&callee_fid) {
        for (k, &is_tainted) in callee_taint.iter().enumerate() {
            if is_tainted {
                if let Some(ta) = type_args.get(k) {
                    collect_typeparams_into(ta, local);
                }
            }
        }
    }
}

fn collect_typeparams_into(ty: &Type, local: &mut Vec<bool>) {
    // Only the OUTERMOST `TypeParam(i)` taints i. Type params nested
    // inside struct wrappers (e.g. `Coin<T>`, `Vault<T0, T1>`) do
    // NOT need taint: the wrapping `HasObjectId` instance emitted by
    // `obj_type_universe.rs` is unconditional on its generic args
    // (`instance{T0:Type}: HasObjectId (Coin T0) where uid s := s.id`),
    // so `HasObjectId (Coin USDC)` resolves without `HasObjectId USDC`.
    // The same holds for `HasCode ObjType`: the wrapping derivation
    // only needs `[HasCode TyCode T0]`, which every user function
    // already carries unconditionally on every type param.
    //
    // Without this narrowing the over-approximation would taint
    // every wrapping use of a type param, breaking concrete-typed
    // tests like `deposit_assets<USDC, UltraUSDC, USDC>(...)` --
    // USDC is a phantom-token marker without a `HasObjectId`
    // instance, but `Coin<USDC>` has one.
    if let Type::TypeParam(i) = ty {
        let i = *i as usize;
        if i < local.len() {
            local[i] = true;
        }
    }
}

fn walk_block_obj(
    block: &Block,
    program: &Program,
    leaves: &mut HashSet<Type>,
    wrappings: &mut BTreeSet<WrappingStruct>,
) {
    for stmt in &block.stmts {
        match stmt {
            Stmt::Let { value, .. } => walk_expr_obj(value, program, leaves, wrappings),
            Stmt::Eval(e) => walk_expr_obj(e, program, leaves, wrappings),
        }
    }
    match &block.tail {
        BlockTail::Value(e) => walk_expr_obj(e, program, leaves, wrappings),
        BlockTail::Break { value, .. } => walk_expr_obj(value, program, leaves, wrappings),
        BlockTail::Continue { value, .. } => walk_expr_obj(value, program, leaves, wrappings),
        BlockTail::Return(e) => walk_expr_obj(e, program, leaves, wrappings),
        BlockTail::ReturnFromBlock { value, .. } => {
            walk_expr_obj(value, program, leaves, wrappings)
        }
        BlockTail::Abort { code } => walk_expr_obj(code, program, leaves, wrappings),
    }
}

fn walk_expr_obj(
    expr: &Expr,
    program: &Program,
    leaves: &mut HashSet<Type>,
    wrappings: &mut BTreeSet<WrappingStruct>,
) {
    match expr {
        Expr::Borrow { step, base } => {
            for __pe in step.exprs() {
                walk_expr_obj(__pe, program, leaves, wrappings);
            }
            walk_expr_obj(base, program, leaves, wrappings);
        }
        Expr::Update { step, base, value } => {
            for __pe in step.exprs() {
                walk_expr_obj(__pe, program, leaves, wrappings);
            }
            walk_expr_obj(base, program, leaves, wrappings);
            walk_expr_obj(value, program, leaves, wrappings);
        }
        Expr::Call {
            fun,
            type_args,
            args,
            ..
        } => {
            if is_object_storage_call(program, *fun) {
                for t in type_args {
                    classify(t, program, leaves, wrappings);
                }
            }
            for a in args {
                walk_expr_obj(a, program, leaves, wrappings);
            }
        }
        Expr::Tuple(es) | Expr::Pack { fields: es, .. } => {
            for x in es {
                walk_expr_obj(x, program, leaves, wrappings);
            }
        }
        Expr::Unpack { value, .. }
        | Expr::Field { base: value, .. }
        | Expr::ReadRef(value)
        | Expr::ToProp(value)
        | Expr::ToBool(value) => walk_expr_obj(value, program, leaves, wrappings),
        Expr::WriteRef { reference, value } => {
            walk_expr_obj(reference, program, leaves, wrappings);
            walk_expr_obj(value, program, leaves, wrappings);
        }
        Expr::BinOp { lhs, rhs, .. } => {
            walk_expr_obj(lhs, program, leaves, wrappings);
            walk_expr_obj(rhs, program, leaves, wrappings);
        }
        Expr::UnOp { operand, .. } => walk_expr_obj(operand, program, leaves, wrappings),
        Expr::If {
            cond,
            then_branch,
            else_branch,
        } => {
            walk_expr_obj(cond, program, leaves, wrappings);
            walk_block_obj(then_branch, program, leaves, wrappings);
            walk_block_obj(else_branch, program, leaves, wrappings);
        }
        Expr::Match {
            selector, cases, ..
        } => {
            walk_expr_obj(selector, program, leaves, wrappings);
            for c in cases {
                walk_block_obj(&c.body, program, leaves, wrappings);
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
                walk_expr_obj(init, program, leaves, wrappings);
            }
            walk_block_obj(header, program, leaves, wrappings);
            walk_expr_obj(cond, program, leaves, wrappings);
            walk_block_obj(body, program, leaves, wrappings);
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

pub fn write_obj_type_file(
    universe: &ObjTypeUniverse,
    program: &Program,
    output_dir: &Path,
) -> io::Result<()> {
    let gen_dir = output_dir.join("Generated");
    fs::create_dir_all(&gen_dir)?;
    let path = gen_dir.join("ObjType.lean");
    let mut out = String::new();
    out.push_str("-- Generated per project by the lean-pipeline renderer.\n");
    out.push_str("-- Bare inductive. Interp + Universe + HasCode in ObjTypeInterp.\n\n");
    out.push_str("import Generated.TyCode\n\n");
    out.push_str("inductive ObjType where\n");
    out.push_str("  | dummy\n");
    for leaf in &universe.leaves {
        let stem = mangle(leaf, program);
        out.push_str(&format!("  | {}\n", stem));
    }
    for w in &universe.wrappings {
        let stem = wrapping_ctor_name(w, program);
        let params: String = (0..w.arity)
            .map(|i| format!(" (a{} : _root_.TyCode)", i))
            .collect();
        out.push_str(&format!("  | {}{}\n", stem, params));
    }
    out.push_str("  deriving DecidableEq, Repr\n");
    fs::write(&path, &out)?;
    Ok(())
}

pub fn write_obj_type_interp_file(
    universe: &ObjTypeUniverse,
    context: &super::context::RenderContext<'_>,
    output_dir: &Path,
    lemma_libs: &BTreeSet<String>,
) -> io::Result<()> {
    let program = context.program;
    let gen_dir = output_dir.join("Generated");
    fs::create_dir_all(&gen_dir)?;
    let path = gen_dir.join("ObjTypeInterp.lean");
    let mut out = String::new();
    out.push_str("-- Generated per project by the lean-pipeline renderer.\n\n");
    let mut packages: HashSet<(String, String, bool)> = HashSet::new();
    for t in &universe.leaves {
        super::dyn_type_universe::collect_struct_modules(t, program, lemma_libs, &mut packages);
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
    out.push_str("import Generated.ObjType\n");
    out.push_str("import Generated.TyCodeInterp\n");
    out.push_str("import Sui.ObjectNatives\n");
    let mut import_lines: Vec<String> = packages
        .iter()
        .map(|(pkg, ns, is_lemma)| {
            if *is_lemma {
                if super::lemma_module_has_types_leaf(context, pkg, ns) {
                    format!("import {}.{}_Types\n", pkg, ns)
                } else {
                    format!("import {}.{}\n", pkg, ns)
                }
            } else {
                format!("import {}.{}_Types\n", pkg, ns)
            }
        })
        .collect();
    import_lines.sort();
    import_lines.dedup();
    for line in import_lines {
        out.push_str(&line);
    }
    out.push('\n');
    out.push_str("set_option linter.unusedVariables false\n\n");
    out.push_str("abbrev ObjType.interp : ObjType -> Type\n");
    out.push_str("  | .dummy => Unit\n");
    for leaf in &universe.leaves {
        let stem = mangle(leaf, program);
        let ty_str = super::ty::type_to_string(leaf, program, None, None);
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
            escape::escape_struct_name(&s.name)
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
    out.push_str(
        "@[reducible] def ObjType.decEqInterp : \u{2200} u : ObjType, DecidableEq (ObjType.interp u)\n",
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

    // `ObjType.typeName`: Move FQN per code (see `TyCode.typeName`).
    // Required by the `Universe` class; objects rarely flow through
    // `type_name::get`, but a total mapping must exist.
    out.push_str("def ObjType.typeName : ObjType \u{2192} String\n");
    out.push_str("  | .dummy => \"dummy\"\n");
    for leaf in &universe.leaves {
        let stem = mangle(leaf, program);
        out.push_str(&format!(
            "  | .{} => \"{}\"\n",
            stem,
            super::dyn_type_universe::lean_str(&leaf_fqn(leaf, program))
        ));
    }
    for w in &universe.wrappings {
        let stem = wrapping_ctor_name(w, program);
        let pat: String = (0..w.arity).map(|i| format!(" a{}", i)).collect();
        let base = super::dyn_type_universe::lean_str(&struct_base_fqn(w.struct_id, program));
        // ObjType wrapping args are `TyCode` codes (objects hold
        // TyCode-universe values), so recurse via `TyCode.typeName`,
        // not `ObjType.typeName`.
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

    out.push_str("instance : Universe ObjType where\n");
    out.push_str("  decEq       := inferInstance\n");
    out.push_str("  interp      := ObjType.interp\n");
    out.push_str("  decEqInterp := ObjType.decEqInterp\n");
    out.push_str("  typeName    := ObjType.typeName\n\n");
    for leaf in &universe.leaves {
        let stem = mangle(leaf, program);
        let ty_str = super::ty::type_to_string(leaf, program, None, None);
        out.push_str(&format!(
            "instance : HasCode ObjType ({}) := \u{27E8}.{}, rfl\u{27E9}\n",
            ty_str, stem
        ));
        // Emit `Object.HasObjectId` ONLY for leaves whose first field
        // is `object::UID` -- the Sui `key`-ability shape. Phantom
        // tokens like `USDC` / `UltraUSDC` appear in ObjType (because
        // they're type args at `transfer<USDC>` / `take_shared<USDC>`
        // sites via `Coin<USDC>`) but have no `id` field; emitting a
        // `HasObjectId` instance for them generates Lean code that
        // fails the lake build with `Invalid field id`.
        // Emit here only for NATIVE object structs -- non-native
        // (rendered) structs get their `HasObjectId` at the struct
        // definition (`render_struct`), regardless of ObjType-universe
        // membership, so emitting it here too would duplicate the
        // instance.
        if let Type::Struct { struct_id, .. } = leaf {
            let native = program.structs.get(struct_id).is_some_and(|s| s.is_native);
            if native && has_uid_first_field(program, struct_id) {
                out.push_str(&format!(
                    "instance : Object.HasObjectId ({}) where uid s := s.id\n",
                    ty_str
                ));
            }
        }
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
            escape::escape_struct_name(&s.name)
        );
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
            "\ninstance{cs_ty}{cs}: HasCode ObjType ({sp}{ats}) where\n  code := .{stem}{ca}\n  proof := by show {sp}{sa} = {sp}{ats}; rw [{rw}]\n",
            cs_ty = type_params_intro, cs = constraints, sp = struct_path,
            ats = applied_types, stem = stem, ca = ctor_args, sa = show_args, rw = rw_args,
        ));
        // HasObjectId for the wrapping shape -- gated on the same
        // `id : object::UID` first-field shape as the leaf case.
        // Generic Sui object wrappers (e.g. `Coin<T>`) have UID;
        // non-object generics that just happen to flow through
        // an object-storage callsite (rare but possible) do not.
        // Native wrappers (e.g. `Coin<T>`) only -- non-native generic
        // object structs get their `HasObjectId` at the struct
        // definition (`render_struct`).
        let w_native = program
            .structs
            .get(&w.struct_id)
            .is_some_and(|s| s.is_native);
        if w_native && has_uid_first_field(program, &w.struct_id) {
            out.push_str(&format!(
                "\ninstance{cs_ty}: Object.HasObjectId ({sp}{ats}) where uid s := s.id\n",
                cs_ty = type_params_intro,
                sp = struct_path,
                ats = applied_types,
            ));
        }
    }
    fs::write(&path, &out)?;
    Ok(())
}
