//! Renderer support for the typed `Mutation` prelude.
//!
//! Per-package AnyKey generation and the helpers needed to lower the
//! IR's borrow / writeback / IsParent variants to
//! `Prover.Mutation.*` calls. See
//! `plans/lean-pipeline/mutable-references.md`.
//!
//! This module is structurally complete (collector + mangler +
//! emitter) but not yet wired into every match arm in `render::expr`
//! / `render::mod`. While the wiring is in flight, the affected
//! arms keep their `UnsupportedConstruct` placeholders; tests pass
//! because no fixture currently exercises a borrow-mut shape that
//! reaches the renderer.

use std::collections::BTreeSet;

use crate::ir::{
    visit::{walk_block_default, walk_expr_default, walk_stmt_default, Visitor},
    Block, BorrowEdge, Expr, Program, Stmt, Type,
};

/// One `AnyKey` constructor entry. The set of these emitted per
/// package is computed by [`collect_any_key`].
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct AnyKeyVariant {
    /// `k_<mangled>` -- the Lean constructor name.
    pub ctor: String,
    /// The Lean type rendered for this constructor's payload
    /// (`BoundedNat (2^64)`, `Address`, `MyMod.PoolKey`, etc.).
    pub payload_lean_ty: String,
}

/// Walk `program` and collect every distinct Move key type appearing
/// in a `BorrowEdge::MapKey { key_type, .. }` (on `WriteBack` /
/// `IsParent` edges) or `Expr::BorrowMapKey { key_type, .. }`. The
/// returned set is sorted by constructor name for determinism.
pub fn collect_any_key(program: &Program) -> BTreeSet<AnyKeyVariant> {
    let deps = compute_anykey_typeparam_deps(program);
    collect_any_key_with_deps(program, &deps)
}

pub(crate) fn collect_any_key_in(
    context: &super::context::RenderContext<'_>,
) -> BTreeSet<AnyKeyVariant> {
    collect_any_key_with_deps(context.program, context.anykey_typeparam_deps())
}

fn collect_any_key_with_deps(
    program: &Program,
    deps: &std::collections::HashMap<crate::ir::FunId, Vec<bool>>,
) -> BTreeSet<AnyKeyVariant> {
    // `Type` doesn't implement `Ord`, so we collect raw types into a
    // `Vec` and dedupe by mangled constructor name (which IS totally
    // ordered). Two distinct Move types with the same mangle would
    // collide; the mangle is keyed off every structural field so
    // distinct types produce distinct mangles by construction.
    //
    // Slice 1 of item B (see plans/lean-pipeline/item-b-real-anykey-work-plan.md):
    // we now emit one real `| k_<mangled>(v : <payload>)` constructor
    // per *concrete* key type. A type is concrete iff it contains no
    // `TypeParam(n)` -- those would render to an in-scope name that
    // does not exist at the `Generated/AnyKey.lean` file scope. Filter
    // them here so the inductive stays well-formed. The placeholder
    // `| unit` constructor that `render_any_key_file` always emits
    // covers non-concrete sites; per-call monomorphisation lands in
    // a follow-up.
    let mut collector = KeyCollector {
        keys: Vec::new(),
        program,
        deps,
    };
    for func in program.functions.values() {
        collector.visit_block(&func.body);
    }
    collector
        .keys
        .into_iter()
        .filter(is_concrete_key_type)
        .map(|ty| AnyKeyVariant {
            ctor: any_key_ctor_name(&ty, program),
            payload_lean_ty: payload_lean_ty(&ty, program),
        })
        .collect()
}

/// Is `ty` safe to emit as an `AnyKey` constructor payload?
///
/// Public re-export of [`is_concrete_key_type`] so that the renderer's
/// per-call wrap helper (`render::expr::render_anykey_wrap`) can
/// check whether a given `key_type` made it into the AnyKey
/// inductive. Both `collect_any_key` and the renderer consult the
/// same predicate so the rendered wrap never references a ctor that
/// isn't in the generated file.
pub fn is_concrete_key_payload(ty: &Type) -> bool {
    is_concrete_key_type(ty)
}

/// Is `ty` safe to emit as an `AnyKey` constructor payload in slice 1?
///
/// Slice 1 scope (see plans/lean-pipeline/item-b-real-anykey-work-plan.md):
/// only primitive types and aggregates over primitives. Struct
/// payloads are deferred because the generated `Generated/AnyKey.lean`
/// file lives outside the user packages and would need new imports
/// (and DecidableEq derivations) to reference them. A later slice
/// reverses the import direction or generates one AnyKey per package.
///
/// References and mutable refs are stripped; their inner types decide.
fn is_concrete_key_type(ty: &Type) -> bool {
    match ty {
        Type::Unit | Type::Bool | Type::Prop | Type::UInt(_) | Type::Address => true,
        Type::Vector(inner) => is_concrete_key_type(inner),
        Type::Tuple(elems) => elems.iter().all(is_concrete_key_type),
        // Concrete struct payloads are now supported: `AnyKey`
        // derives `BEq` (not `DecidableEq`), so a struct key only
        // needs its own `BEq` instance (native structs and most
        // translated user structs have one) rather than a
        // recursively-derived `DecidableEq`. A generic instantiation
        // is concrete iff every type arg is concrete; `Foo<u64>` is
        // allowed, `Foo<T>` (TypeParam arg) is not.
        Type::Struct { type_args, .. } => type_args.iter().all(is_concrete_key_type),
        Type::Reference(inner) | Type::MutableRef { inner, .. } => is_concrete_key_type(inner),
        Type::TypeParam(_) => false,
    }
}

/// Render `ty` as a Lean payload type, qualifying struct references
/// via `_root_.<Pkg>.<Mod>.<Name>` so the resulting type is valid at
/// `Generated/AnyKey.lean`'s top-level scope (no `namespace` block,
/// no `open`). Falls back to the self-contained `any_key_payload_ty`
/// shape for primitives so behaviour stays predictable in the case
/// where the renderer's `ty::type_to_string` would otherwise emit
/// helper syntax (e.g. `BoundedNat (2^32)` is already what we want).
pub(crate) fn payload_lean_ty(ty: &Type, program: &Program) -> String {
    match ty {
        // Primitives stay self-contained -- matches the historical
        // shape used in tests + comments.
        Type::Unit => "Unit".to_string(),
        Type::Bool => "Bool".to_string(),
        Type::Prop => "Prop".to_string(),
        Type::UInt(_) | Type::Address => any_key_payload_ty(ty, program),
        Type::Vector(inner) => format!("List ({})", payload_lean_ty(inner, program)),
        Type::Tuple(elems) => {
            if elems.is_empty() {
                "Unit".to_string()
            } else if elems.len() == 1 {
                payload_lean_ty(&elems[0], program)
            } else {
                let inner: Vec<String> =
                    elems.iter().map(|e| payload_lean_ty(e, program)).collect();
                format!("({})", inner.join(" \u{00D7} "))
            }
        }
        // Struct payloads: use the renderer's qualified-name machinery
        // with `current_module: None` so it always emits the fully-
        // qualified `_root_.<Pkg>.<Mod>.<Name>` form (the AnyKey file
        // has no surrounding `namespace` block, so unqualified names
        // wouldn't resolve).
        Type::Struct { .. } => super::ty::type_to_string(ty, program, None, None),
        Type::Reference(inner) | Type::MutableRef { inner, .. } => payload_lean_ty(inner, program),
        // Filtered out by `is_concrete_key_type` before reaching here.
        Type::TypeParam(n) => format!("T{}", n),
    }
}

/// Emit `AnyKey.lean` source for a package's collected variants.
///
/// Per-call key payload variants can contain references to Move type
/// parameters (`TypeParam(N)` -> `tvN`) and bare struct IDs that
/// aren't in scope at the package level (same shape problem as
/// AnyEvent / AnyObject in `render::world`). Until per-function /
/// monomorphised variants land, we emit a placeholder inductive so
/// lake can typecheck; the collected variants are recorded in the
/// file's comment block.
/// Walk every variant's payload type collecting unique
/// (package, ns) pairs for non-lemma struct refs. Returns `_Types`
/// file imports for those; lemma packages get the regular module
/// import.
fn collect_anykey_imports(
    variants: &BTreeSet<AnyKeyVariant>,
    program: &Program,
    lemma_libs: &std::collections::BTreeSet<String>,
) -> Vec<String> {
    let deps = compute_anykey_typeparam_deps(program);
    collect_anykey_imports_with_deps(variants, program, lemma_libs, &deps)
}

fn collect_anykey_imports_with_deps(
    variants: &BTreeSet<AnyKeyVariant>,
    program: &Program,
    lemma_libs: &std::collections::BTreeSet<String>,
    deps: &std::collections::HashMap<crate::ir::FunId, Vec<bool>>,
) -> Vec<String> {
    use std::collections::HashSet;
    let mut packages: HashSet<(String, String, bool)> = HashSet::new();
    // Re-derive the (pkg, ns) from each variant's payload type. We
    // can recover the structural type from the mangled ctor name --
    // but easier: walk all functions, find map-keyed borrows again,
    // filter to concrete struct payloads, and collect their modules.
    // This duplicates `collect_any_key`'s walk a bit; the saving
    // grace is it runs once per render.
    // Reuse the SAME traversal as `collect_any_key` (the variant
    // collector) so every key type that becomes an AnyKey variant also
    // contributes its `_Types` import. The previous hand-rolled
    // `StructPayloadCollector` only inspected bare `Expr::BorrowMapKey`
    // and skipped `WriteBack`/`IsParent` map-key edges, so keys that
    // appear only in a write-back edge (e.g. `DFKey<EModeRateLimiter>`)
    // got a variant with no import -> unknown-identifier at lake build.
    let mut collector = KeyCollector {
        keys: Vec::new(),
        program,
        deps,
    };
    for func in program.functions.values() {
        collector.visit_block(&func.body);
    }
    for ty in &collector.keys {
        if is_concrete_key_type(ty) {
            collect_struct_packages_anykey(ty, program, lemma_libs, &mut packages);
        }
    }
    let _ = variants; // dedup already handled at variant level
    let mut imports: Vec<String> = packages
        .into_iter()
        .map(|(pkg, ns, is_lemma)| {
            if is_lemma {
                format!(
                    "import {}.{}
",
                    pkg, ns
                )
            } else {
                format!(
                    "import {}.{}_Types
",
                    pkg, ns
                )
            }
        })
        .collect();
    imports.sort();
    imports.dedup();
    imports
}

fn collect_struct_packages_anykey(
    ty: &Type,
    program: &Program,
    lemma_libs: &std::collections::BTreeSet<String>,
    packages: &mut std::collections::HashSet<(String, String, bool)>,
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
                    let ns = super::escape::module_name_to_namespace(&m.name);
                    let is_lemma = lemma_libs.contains(&pkg);
                    packages.insert((pkg, ns, is_lemma));
                }
            }
            for arg in type_args {
                collect_struct_packages_anykey(arg, program, lemma_libs, packages);
            }
        }
        Type::Vector(inner) | Type::Reference(inner) => {
            collect_struct_packages_anykey(inner, program, lemma_libs, packages);
        }
        Type::MutableRef { inner, root } => {
            collect_struct_packages_anykey(inner, program, lemma_libs, packages);
            collect_struct_packages_anykey(root, program, lemma_libs, packages);
        }
        Type::Tuple(ts) => {
            for t in ts {
                collect_struct_packages_anykey(t, program, lemma_libs, packages);
            }
        }
        _ => {}
    }
}

/// Walker that collects every concrete struct-bearing key type
/// touched by `BorrowMapKey` / `WriteBack(MapKey)` /
/// `IsParent(MapKey)`. Mirrors `KeyCollector` but keeps struct
/// payloads (Phase 4) -- they're filtered later only for TypeParam
/// contamination.
struct StructPayloadCollector {
    hits: std::collections::HashSet<Type>,
}

impl StructPayloadCollector {
    fn visit_block(&mut self, block: &crate::ir::expr::Block) {
        for stmt in &block.stmts {
            match stmt {
                crate::ir::expr::Stmt::Let { value, .. } => self.visit_expr(value),
                crate::ir::expr::Stmt::Eval(e) => self.visit_expr(e),
            }
        }
        use crate::ir::expr::BlockTail;
        match &block.tail {
            BlockTail::Value(e) => self.visit_expr(e),
            BlockTail::Break { value, .. } => self.visit_expr(value),
            BlockTail::Continue { value, .. } => self.visit_expr(value),
            BlockTail::Return(e) => self.visit_expr(e),
            BlockTail::ReturnFromBlock { value, .. } => self.visit_expr(value),
            BlockTail::Abort { code } => self.visit_expr(code),
        }
    }
    fn visit_expr(&mut self, expr: &crate::ir::expr::Expr) {
        use crate::ir::expr::Expr;
        match expr {
            Expr::Call { args, .. } => {
                for a in args {
                    self.visit_expr(a);
                }
            }
            Expr::Tuple(es) | Expr::Pack { fields: es, .. } => {
                for x in es {
                    self.visit_expr(x);
                }
            }
            Expr::Unpack { value, .. }
            | Expr::Field { base: value, .. }
            | Expr::ReadRef(value)
            | Expr::ToProp(value)
            | Expr::ToBool(value) => self.visit_expr(value),
            Expr::WriteRef { reference, value } => {
                self.visit_expr(reference);
                self.visit_expr(value);
            }
            Expr::BinOp { lhs, rhs, .. } => {
                self.visit_expr(lhs);
                self.visit_expr(rhs);
            }
            Expr::UnOp { operand, .. } => self.visit_expr(operand),
            Expr::If {
                cond,
                then_branch,
                else_branch,
            } => {
                self.visit_expr(cond);
                self.visit_block(then_branch);
                self.visit_block(else_branch);
            }
            Expr::Match {
                selector, cases, ..
            } => {
                self.visit_expr(selector);
                for c in cases {
                    self.visit_block(&c.body);
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
                    self.visit_expr(init);
                }
                self.visit_block(header);
                self.visit_expr(cond);
                self.visit_block(body);
            }
            Expr::Quantifier { domain, body, .. } => {
                use crate::ir::quant::QuantDomain;
                match domain {
                    QuantDomain::Unbounded => {}
                    QuantDomain::Range { start, end } => {
                        self.visit_expr(start);
                        self.visit_expr(end);
                    }
                    QuantDomain::Collection(c) => self.visit_expr(c),
                    QuantDomain::VecRange { vec, start, end } => {
                        self.visit_expr(vec);
                        self.visit_expr(start);
                        self.visit_expr(end);
                    }
                }
                self.visit_block(body);
            }
            _ => {}
        }
    }
}

pub fn render_any_key_file(
    variants: &BTreeSet<AnyKeyVariant>,
    program: &Program,
    lemma_libs: &std::collections::BTreeSet<String>,
) -> String {
    let deps = compute_anykey_typeparam_deps(program);
    render_any_key_file_with_deps(variants, program, lemma_libs, &deps)
}

pub(crate) fn render_any_key_file_in(
    variants: &BTreeSet<AnyKeyVariant>,
    context: &super::context::RenderContext<'_>,
    lemma_libs: &std::collections::BTreeSet<String>,
) -> String {
    render_any_key_file_with_deps(
        variants,
        context.program,
        lemma_libs,
        context.anykey_typeparam_deps(),
    )
}

fn render_any_key_file_with_deps(
    variants: &BTreeSet<AnyKeyVariant>,
    program: &Program,
    lemma_libs: &std::collections::BTreeSet<String>,
    deps: &std::collections::HashMap<crate::ir::FunId, Vec<bool>>,
) -> String {
    // Slice 1 of item B (see plans/lean-pipeline/item-b-real-anykey-work-plan.md):
    // emit a real inductive with one `| k_<mangled> (v : <payload>)`
    // constructor per *concrete* collected variant. Non-concrete
    // variants (those whose payload would mention an unresolved
    // `TypeParam(n)`) are filtered upstream by `collect_any_key`
    // and never reach this function.
    //
    // The `| unit` placeholder is *kept* alongside the real
    // constructors so existing call sites that emit `AnyKey.unit`
    // (`key_unit_val(ctx)` and friends in `render::expr`) keep
    // typechecking. Slices 2-3 of item B replace those emissions
    // with real `AnyKey.k_<mangled> <expr>` wrappers and pattern-
    // matching insert lambdas; until then `| unit` is the safety
    // net.
    let mut out = String::new();
    out.push_str(
        "-- Generated per package by the lean-pipeline renderer.
",
    );
    out.push_str(
        "-- See plans/lean-pipeline/mutable-references.md and
",
    );
    out.push_str(
        "-- plans/lean-pipeline/item-b-real-anykey-work-plan.md.
",
    );
    out.push_str(
        "--
",
    );
    out.push_str(
        "-- The per-call key variants collected from this package's
",
    );
    out.push_str(
        "-- map-keyed borrows are listed below as documentation;
",
    );
    out.push_str(
        "-- each one also gets a real `| k_<mangled>` constructor in
",
    );
    out.push_str(
        "-- the inductive below. A `| unit` constructor remains as a
",
    );
    out.push_str(
        "-- placeholder for sites that haven't been migrated to the
",
    );
    out.push_str(
        "-- real ctors yet (slices 2-3 of item B).
",
    );
    out.push_str(
        "
",
    );
    if variants.is_empty() {
        out.push_str(
            "-- (no map-keyed borrows in this package)
",
        );
    } else {
        for v in variants {
            out.push_str(&format!(
                "-- variant: {} : {}
",
                v.ctor, v.payload_lean_ty
            ));
        }
    }
    out.push_str(
        "
",
    );
    out.push_str(
        "import Prelude.Mutation
",
    );
    // Phase 4: import user `_Types` files for any struct payloads.
    // No cycle: user `_Types` files don't import `Generated.AnyKey`
    // (only user `.lean` files do, and those live further down in
    // the import DAG).
    let extra_imports = collect_anykey_imports_with_deps(variants, program, lemma_libs, deps);
    for imp in &extra_imports {
        out.push_str(imp);
    }
    out.push_str(
        "
",
    );
    out.push_str(
        "inductive AnyKey where
",
    );
    for v in variants {
        out.push_str(&format!(
            "  | {} (v : {})
",
            v.ctor, v.payload_lean_ty
        ));
    }
    out.push_str(
        "  | unit
",
    );
    out.push_str(
        "  deriving BEq
",
    );
    out.push_str(
        "
",
    );
    // `ToAnyKey`: wrap a key value into `AnyKey` via instance
    // resolution. Generic map-borrow functions (e.g.
    // `wit_table::borrow_mut`) carry `[ToAnyKey K]` and emit
    // `ToAnyKey.toAnyKey k`; at the concrete instantiation Lean picks
    // the real `k_<...>` constructor, so the borrowed value's runtime
    // key matches what `writeBackMapKey` recovers (instead of the
    // `AnyKey.unit` placeholder, which dropped the mutation).
    out.push_str(
        "class ToAnyKey (A : Type) where
  toAnyKey : A -> AnyKey

",
    );
    for v in variants {
        out.push_str(&format!(
            "instance : ToAnyKey ({}) where toAnyKey v := AnyKey.{} v
",
            v.payload_lean_ty, v.ctor
        ));
    }
    // `IntoKey AnyKey <payload>`: the 2-parameter, Key-explicit form of
    // `ToAnyKey`, consumed by LEMMA-package framework functions that
    // wrap a CONCRETE map key while staying abstract over `__MutKey`
    // (they carry `[IntoKey __MutKey <payload>]` and emit
    // `IntoKey.intoKey <key>`; see `Prelude.Mutation.IntoKey` and
    // `render::expr::util::render_anykey_wrap`). Resolved here at the
    // user-package call site where `__MutKey := AnyKey`. Maps to the
    // same `AnyKey.k_<ctor>` constructor as the `ToAnyKey` instance so
    // the key round-trips faithfully.
    for v in variants {
        out.push_str(&format!(
            "instance : IntoKey AnyKey ({}) where intoKey v := AnyKey.{} v
",
            v.payload_lean_ty, v.ctor
        ));
    }
    // No universal catch-all instance: `[ToAnyKey T]` is emitted by
    // the renderer (`function.rs`) ONLY on type params that a map-key
    // typeclass use actually reaches (`mutation::anykey_typeparam_needs_constraint`),
    // so the per-variant instances above resolve every demand. The old
    // `instance {A} : ToAnyKey A := AnyKey.unit` catch-all existed only
    // to absorb the previously-unconditional `[ToAnyKey T]` emission;
    // with precise gating it is unnecessary (and it was the last reason
    // `AnyKey.unit` had to exist as a recovered key).
    // `FromAnyKey`: the inverse of `ToAnyKey` -- recover a key value
    // back out of `AnyKey` on the writeback side. Generic map-borrow
    // functions carry `[FromAnyKey K]` (threaded next to `[ToAnyKey K]`,
    // see function.rs) and emit `FromAnyKey.fromAnyKey k`; at the
    // concrete instantiation Lean picks the faithful per-ctor instance
    // below, so the recovered key matches what `ToAnyKey` wrapped. This
    // replaces the old hardcoded `match | AnyKey.k_<mangle> v` recovery,
    // which mangled a `TypeParam` to the non-existent `AnyKey.k_T0`.
    out.push_str("class FromAnyKey (A : Type) where\n  fromAnyKey : AnyKey -> A\n\n");
    // Bridges to the prelude's `IntoKey` / `FromKey`: a lemma-package function
    // generic over a map key carries `[IntoKey AnyKey K] [FromKey AnyKey K]`
    // (framework modules cannot see `ToAnyKey` / `FromAnyKey`). A user caller
    // generic over the same key only holds the user-side pair, so derive the
    // prelude pair from it. Low priority: a concrete key still resolves to its
    // per-variant instance first.
    out.push_str(
        "instance (priority := low) {A : Type} [ToAnyKey A] : IntoKey AnyKey A where intoKey := ToAnyKey.toAnyKey\n",
    );
    out.push_str(
        "instance (priority := low) {A : Type} [FromAnyKey A] : FromKey AnyKey A where fromKey := FromAnyKey.fromAnyKey\n\n",
    );
    for v in variants {
        out.push_str(&format!(
            "instance [Inhabited ({0})] : FromAnyKey ({0}) where fromAnyKey | AnyKey.{1} v => v | _ => default\n",
            v.payload_lean_ty, v.ctor
        ));
    }
    // No universal catch-all (mirrors `ToAnyKey` above): `[FromAnyKey T]`
    // is gated to map-key type params, so every demand hits a per-variant
    // instance.
    // `LawfulAnyKey`: the round-trip law tying the two data classes
    // together -- `fromAnyKey (toAnyKey k) = k`. It is a Prop-valued class
    // parameterized by the operational `[ToAnyKey A] [FromAnyKey A]` pair
    // (the `LawfulBEq` idiom), so it adds no data path: the two classes and
    // their per-variant instances above stay byte-identical and every
    // existing elaboration is untouched. The generated writeback lowering
    // itself computes `FromAnyKey.fromAnyKey (ToAnyKey.toAnyKey k)` (see
    // `render::expr::writeback` `generic_key`), so its correctness silently
    // assumes this law; the class makes that assumption an explicit,
    // instance-discharged interface contract. Stage-12 obligation props
    // over a generic map key carry `[LawfulAnyKey T]` (gated on
    // `is_theorem` in `function.rs`) so the round-trip is derivable
    // client-side; the two data classes alone do NOT imply it (the
    // adversarial `AnyKeyGap` certificate in the cetus-stl specs exhibits a
    // law-free `FromAnyKey` that falsifies it). The class is emitted
    // unconditionally (uniform scaffold even for variant-less packages);
    // each concrete variant is lawful by `rfl` (the reducible `ToAnyKey`
    // instance wraps to `AnyKey.k_<ctor>`, the `FromAnyKey` match
    // iota-reduces on that constructor). The `[Inhabited (p)]` guard
    // mirrors the `FromAnyKey` instance head so its synthesis resolves
    // identically. These instances are also the satisfiability witnesses
    // for the new hypothesis: every concrete key the pipeline emits is
    // lawful, so conditioning obligations on lawfulness excludes no real
    // instantiation.
    out.push_str(
        "class LawfulAnyKey (A : Type) [ToAnyKey A] [FromAnyKey A] : Prop where\n  from_to : \u{2200} k : A, (FromAnyKey.fromAnyKey (ToAnyKey.toAnyKey k) : A) = k\n\n",
    );
    for v in variants {
        out.push_str(&format!(
            "instance [Inhabited ({0})] : LawfulAnyKey ({0}) where\n  from_to _ := rfl\n",
            v.payload_lean_ty
        ));
    }
    out.push_str(
        "abbrev Mutation := Prover.Mutation.Mutation AnyKey
",
    );
    out.push_str(
        "abbrev Edge     := Prover.Mutation.Edge     AnyKey
",
    );
    out
}

/// Mangle a Move `Type` into an `AnyKey` constructor suffix.
///
/// Conventions:
/// - Primitives: `k_u64`, `k_address`, `k_bool`, ...
/// - Vectors: `k_Vec_<inner>`.
/// - Tuples: `k_Tuple_<elem1>_<elem2>_...`.
/// - Datatypes: `k_S_<Package>__<module>__<Name>` -- the datatype's NAME
///   tag (see [`crate::render::struct_idx`]), never its positional
///   `StructId`. The id is handed out in module-name walk order, so a
///   `k_S<id>` constructor was renamed by any module rename anywhere in
///   the program, breaking every hand-written proof that named it.
/// - Generic instantiations: `k_<Base>_<TypeArg1>_<TypeArg2>_...`.
pub fn any_key_ctor_name(ty: &Type, program: &Program) -> String {
    let mut s = String::from("k");
    append_mangle(&mut s, ty, program);
    s
}

fn append_mangle(out: &mut String, ty: &Type, program: &Program) {
    match ty {
        Type::Unit => out.push_str("_unit"),
        Type::Bool => out.push_str("_bool"),
        Type::Prop => out.push_str("_prop"),
        Type::UInt(n) => {
            out.push_str(&format!("_u{}", n));
        }
        Type::Address => out.push_str("_address"),
        Type::Vector(inner) => {
            out.push_str("_Vec");
            append_mangle(out, inner, program);
        }
        Type::Tuple(elems) => {
            out.push_str("_Tuple");
            for e in elems {
                append_mangle(out, e, program);
            }
        }
        Type::Struct {
            struct_id,
            type_args,
        } => {
            out.push_str("_S_");
            out.push_str(&crate::render::struct_idx::struct_tag_ident(
                *struct_id, program,
            ));
            for ta in type_args {
                append_mangle(out, ta, program);
            }
        }
        Type::Reference(inner) => {
            out.push_str("_ref");
            append_mangle(out, inner, program);
        }
        Type::MutableRef { inner, .. } => {
            out.push_str("_mutref");
            append_mangle(out, inner, program);
        }
        Type::TypeParam(n) => {
            out.push_str(&format!("_T{}", n));
        }
    }
}

/// Render the Lean type of an `AnyKey` constructor payload.
///
/// Mirrors the renderer's existing `Type::*` → Lean mapping but
/// stays self-contained so the collector / emitter doesn't depend
/// on the rest of `render/`. When the full renderer wire-up lands
/// this delegates to `render::ty::render_type` instead.
pub fn any_key_payload_ty(ty: &Type, program: &Program) -> String {
    match ty {
        Type::Unit => "Unit".to_string(),
        Type::Bool => "Bool".to_string(),
        Type::Prop => "Prop".to_string(),
        // All UInt widths render to `BoundedNat (2^N)` to match the
        // renderer's `Type::UInt(N) -> BoundedNat (2^N)` mapping
        // (see `render::ty::render_type`). Using Lean's built-in
        // `UInt8` / `UInt16` / `UInt32` / `UInt64` here would create
        // a type mismatch at the wrap site: the runtime key value
        // is `BoundedNat (2^N)`, not a Lean `UInt*`.
        Type::UInt(n) => format!("BoundedNat (2^{})", n),
        Type::Address => "Address".to_string(),
        Type::Vector(inner) => format!("List ({})", any_key_payload_ty(inner, program)),
        Type::Tuple(elems) => {
            if elems.is_empty() {
                "Unit".to_string()
            } else if elems.len() == 1 {
                any_key_payload_ty(&elems[0], program)
            } else {
                let inner: Vec<String> = elems
                    .iter()
                    .map(|e| any_key_payload_ty(e, program))
                    .collect();
                format!("({})", inner.join(" × "))
            }
        }
        Type::Struct { struct_id, .. } => {
            format!(
                "Struct_{}",
                crate::render::struct_idx::struct_tag_ident(*struct_id, program)
            )
        }
        Type::Reference(inner) | Type::MutableRef { inner, .. } => {
            any_key_payload_ty(inner, program)
        }
        Type::TypeParam(n) => format!("T{}", n),
    }
}

struct KeyCollector<'a> {
    keys: Vec<Type>,
    program: &'a Program,
    deps: &'a std::collections::HashMap<crate::ir::FunId, Vec<bool>>,
}

impl KeyCollector<'_> {
    fn record(&mut self, ty: &Type) {
        if !self.keys.iter().any(|t| t == ty) {
            self.keys.push(ty.clone());
        }
    }

    fn record_edge(&mut self, edge: &BorrowEdge) {
        match edge {
            BorrowEdge::MapKey { key_type, .. } => {
                self.record(key_type);
            }
            BorrowEdge::Hyper(es) => {
                for e in es {
                    self.record_edge(e);
                }
            }
            BorrowEdge::Direct
            | BorrowEdge::StructField { .. }
            | BorrowEdge::EnumField { .. }
            | BorrowEdge::VecIndex => {}
        }
    }
}

impl Visitor for KeyCollector<'_> {
    fn visit_block(&mut self, b: &Block) {
        walk_block_default(self, b);
    }

    fn visit_stmt(&mut self, s: &Stmt) {
        walk_stmt_default(self, s);
    }

    fn visit_expr(&mut self, e: &Expr) {
        match e {
            Expr::Borrow {
                step: crate::ir::path::PathStep::MapKey { key_type, .. },
                ..
            } => {
                self.record(key_type);
            }
            Expr::WriteBack { edge, .. } | Expr::IsParent { edge, .. } => {
                self.record_edge(edge);
            }
            // A concrete type passed at a map-key-tainted callee slot IS a
            // real key -- it's used as a map key INSIDE the generic callee
            // but never appears in a `MapKey` position in any body, so it
            // would otherwise be missed. Harvest it here so it gets a
            // `k_<mangled>` variant + `ToAnyKey`/`FromAnyKey` instance.
            // Without this, deleting the universal catch-all leaves
            // `ToAnyKey <ConcreteKey>` unresolvable at the instantiation
            // site (e.g. current-lending's `assert_not_equal_and_set
            // BorrowPaused`). TypeParam args are dropped downstream by
            // `is_concrete_key_type` -- those are covered by the callee's
            // own `[ToAnyKey K]` hypothesis, not a concrete instance.
            Expr::Call { fun, type_args, .. } => {
                for (k, ta) in type_args.iter().enumerate() {
                    if self
                        .deps
                        .get(fun)
                        .and_then(|bits| bits.get(k))
                        .copied()
                        .unwrap_or(false)
                    {
                        self.record(ta);
                    }
                }
            }
            _ => {}
        }
        walk_expr_default(self, e);
    }
}

// ====================================================================
// Per-typeparam `ToAnyKey` / `FromAnyKey` taint analysis
// ====================================================================
//
// `[ToAnyKey K]` / `[FromAnyKey K]` are demanded only where the
// renderer references the typeclass for a type param: the
// `ToAnyKey.toAnyKey` wrap on a bare-`TypeParam` map key
// (`render::expr::util::render_anykey_wrap`) and the
// `FromAnyKey.fromAnyKey` recover in the `generic_key` writeback
// (`render::expr::writeback`). Both fire iff the key type is a bare
// `TypeParam` -- concrete keys emit a real `AnyKey.k_<ctor>` wrap and
// non-concrete aggregates emit the `AnyKey.unit` placeholder, neither
// of which touches the typeclass.
//
// A forward call-graph fixpoint (mirroring
// `obj_type_universe::compute_obj_typeparam_deps`) taints any function
// type param that (a) appears as a bare `TypeParam(i)` in a map-key
// borrow / write-back / is-parent edge, or (b) flows at slot k into a
// callee whose own param k is tainted. The renderer gates the
// constraint on this taint, so the universal `ToAnyKey` catch-all
// (which mapped every type to `AnyKey.unit`) is unnecessary: the
// per-variant instances cover exactly the type params that reach the
// typeclass, and `[ToAnyKey K]` is never demanded on a param
// instantiated with a non-key type.

fn taint_anykey_key_type(ty: &Type, local: &mut [bool]) {
    // Only a bare `TypeParam(i)` key reaches the typeclass; an
    // aggregate like `vector<T>` renders the `AnyKey.unit` placeholder
    // (no `ToAnyKey` use), so it must not taint -- otherwise the
    // constraint would propagate to concrete non-key instantiations
    // and fail to resolve once the catch-all is gone.
    if let Type::TypeParam(i) = ty {
        let i = *i as usize;
        if i < local.len() {
            local[i] = true;
        }
    }
}

fn taint_anykey_edge(edge: &BorrowEdge, local: &mut [bool]) {
    match edge {
        BorrowEdge::MapKey { key_type, .. } => taint_anykey_key_type(key_type, local),
        BorrowEdge::Hyper(es) => {
            for e in es {
                taint_anykey_edge(e, local);
            }
        }
        BorrowEdge::Direct
        | BorrowEdge::StructField { .. }
        | BorrowEdge::EnumField { .. }
        | BorrowEdge::VecIndex => {}
    }
}

struct AnyKeyTaint<'a> {
    deps: &'a std::collections::HashMap<crate::ir::FunId, Vec<bool>>,
    local: Vec<bool>,
}

impl Visitor for AnyKeyTaint<'_> {
    fn visit_block(&mut self, b: &Block) {
        walk_block_default(self, b);
    }

    fn visit_stmt(&mut self, s: &Stmt) {
        walk_stmt_default(self, s);
    }

    fn visit_expr(&mut self, e: &Expr) {
        match e {
            Expr::Borrow {
                step: crate::ir::path::PathStep::MapKey { key_type, .. },
                ..
            } => taint_anykey_key_type(key_type, &mut self.local),
            Expr::WriteBack { edge, .. } | Expr::IsParent { edge, .. } => {
                taint_anykey_edge(edge, &mut self.local)
            }
            Expr::Call { fun, type_args, .. } => {
                if let Some(callee) = self.deps.get(fun) {
                    for (k, &tainted) in callee.iter().enumerate() {
                        if tainted {
                            if let Some(ta) = type_args.get(k) {
                                taint_anykey_key_type(ta, &mut self.local);
                            }
                        }
                    }
                }
            }
            _ => {}
        }
        walk_expr_default(self, e);
    }
}

/// Forward fixpoint over the call graph: which of each function's type
/// params transitively reach a `ToAnyKey`/`FromAnyKey` typeclass use
/// (a bare-`TypeParam` map key). See the module-level note above.
pub fn compute_anykey_typeparam_deps(
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
            let before = deps.get(&fid).cloned().unwrap_or_default();
            // Scope the `&deps` borrow to this block so the `deps.insert`
            // below (a mutable borrow) doesn't conflict with the taint
            // walker's immutable read of the callee dependency map.
            let after = {
                let mut taint = AnyKeyTaint {
                    deps: &deps,
                    local: before.clone(),
                };
                taint.visit_block(&f.body);
                taint.local
            };
            if before != after {
                deps.insert(fid, after);
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::{Block, BlockTail, BorrowNode, Type, VarId};
    use std::rc::Rc;

    fn unit_var(name: &str) -> VarId {
        Rc::from(name)
    }

    #[test]
    fn empty_program_yields_empty_set() {
        let program = Program::default();
        let keys = collect_any_key(&program);
        assert!(keys.is_empty());
    }

    #[test]
    fn collects_borrow_map_key_with_u64_type() {
        let mut program = Program::default();
        let f = crate::ir::Function {
            module: 0,
            name: "f".to_string(),
            signature: crate::ir::Signature {
                type_params: vec![],
                params: vec![],
                return_type: Type::Unit,
            },
            body: Block {
                stmts: vec![Stmt::Eval(Expr::Borrow {
                    step: crate::ir::path::PathStep::MapKey {
                        key: Box::new(Expr::Var(unit_var("$t1"))),
                        key_type: Type::UInt(64),
                        value_type: Type::Unit,
                        df_value: None,
                    },
                    base: Box::new(Expr::Var(unit_var("$t0"))),
                })],
                tail: BlockTail::Value(Expr::Unit),
            },
            kind: crate::ir::FunctionKind::Source,
            effects: crate::ir::Effects::PURE,
            explicit_pure: false,
        };
        program.functions.insert(0, f);
        let keys = collect_any_key(&program);
        let names: Vec<&str> = keys.iter().map(|v| v.ctor.as_str()).collect();
        assert_eq!(names, vec!["k_u64"]);
    }

    #[test]
    fn collects_map_key_from_writeback_edge() {
        let mut program = Program::default();
        let f = crate::ir::Function {
            module: 0,
            name: "f".to_string(),
            signature: crate::ir::Signature {
                type_params: vec![],
                params: vec![],
                return_type: Type::Unit,
            },
            body: Block {
                stmts: vec![Stmt::Eval(Expr::WriteBack {
                    node: BorrowNode::LocalRoot(unit_var("$t0")),
                    edge: BorrowEdge::MapKey {
                        key_type: Type::Address,
                        value_type: Type::Unit,
                    },
                    child: unit_var("$t1"),
                    world: None,
                })],
                tail: BlockTail::Value(Expr::Unit),
            },
            kind: crate::ir::FunctionKind::Source,
            effects: crate::ir::Effects::PURE,
            explicit_pure: false,
        };
        program.functions.insert(0, f);
        let keys = collect_any_key(&program);
        let names: Vec<&str> = keys.iter().map(|v| v.ctor.as_str()).collect();
        assert_eq!(names, vec!["k_address"]);
    }

    #[test]
    fn collects_concrete_struct_key_type() {
        // Item C: a struct `key_type` is now concrete -- generated structs
        // provide an equality instance, so `AnyKey` can carry the concrete
        // payload rather than collapsing it to the placeholder.
        // `collect_any_key` therefore keeps it and emits a real `k_S<id>`
        // constructor instead of dropping it to the `unit` placeholder.
        let mut program = Program::default();
        let f = crate::ir::Function {
            module: 0,
            name: "f".to_string(),
            signature: crate::ir::Signature {
                type_params: vec![],
                params: vec![],
                return_type: Type::Unit,
            },
            body: Block {
                stmts: vec![Stmt::Eval(Expr::Borrow {
                    step: crate::ir::path::PathStep::MapKey {
                        key: Box::new(Expr::Var(unit_var("$t1"))),
                        key_type: Type::Struct {
                            struct_id: 7,
                            type_args: vec![],
                        },
                        value_type: Type::Unit,
                        df_value: None,
                    },
                    base: Box::new(Expr::Var(unit_var("$t0"))),
                })],
                tail: BlockTail::Value(Expr::Unit),
            },
            kind: crate::ir::FunctionKind::Source,
            effects: crate::ir::Effects::PURE,
            explicit_pure: false,
        };
        program.modules.insert(
            0,
            crate::ir::Module {
                name: "m".to_string(),
                package_name: "p".to_string(),
                address: String::new(),
                required_imports: Vec::new(),
                is_native: false,
            },
        );
        program.structs.insert(
            7,
            crate::ir::Struct {
                module_id: 0,
                name: "MyKey".to_string(),
                qualified_name: "p::m::MyKey".to_string(),
                type_params: Vec::new(),
                fields: vec![crate::ir::Field {
                    name: "id".to_string(),
                    field_type: Type::Address,
                }],
                variants: None,
                is_native: false,
            },
        );
        program.functions.insert(0, f);
        let keys = collect_any_key(&program);
        let names: Vec<&str> = keys.iter().map(|v| v.ctor.as_str()).collect();
        assert_eq!(names, vec!["k_S_p__p__m__MyKey"]);
    }

    #[test]
    fn filters_generic_struct_key_with_type_param_arg() {
        // `Foo<T>` (unresolved `TypeParam` arg) is NOT concrete -- the
        // recursive `is_concrete_key_type` check rejects it, so
        // `collect_any_key` drops it and emits no `k_S<id>` ctor.
        let mut program = Program::default();
        let f = crate::ir::Function {
            module: 0,
            name: "f".to_string(),
            signature: crate::ir::Signature {
                type_params: vec![],
                params: vec![],
                return_type: Type::Unit,
            },
            body: Block {
                stmts: vec![Stmt::Eval(Expr::Borrow {
                    step: crate::ir::path::PathStep::MapKey {
                        key: Box::new(Expr::Var(unit_var("$t1"))),
                        key_type: Type::Struct {
                            struct_id: 7,
                            type_args: vec![Type::TypeParam(0)],
                        },
                        value_type: Type::Unit,
                        df_value: None,
                    },
                    base: Box::new(Expr::Var(unit_var("$t0"))),
                })],
                tail: BlockTail::Value(Expr::Unit),
            },
            kind: crate::ir::FunctionKind::Source,
            effects: crate::ir::Effects::PURE,
            explicit_pure: false,
        };
        program.functions.insert(0, f);
        let keys = collect_any_key(&program);
        assert!(
            keys.is_empty(),
            "generic struct key with TypeParam arg must be filtered: {:?}",
            keys.iter().map(|v| v.ctor.as_str()).collect::<Vec<_>>()
        );
    }

    #[test]
    fn dedupes_repeated_key_types() {
        let mut program = Program::default();
        let f = crate::ir::Function {
            module: 0,
            name: "f".to_string(),
            signature: crate::ir::Signature {
                type_params: vec![],
                params: vec![],
                return_type: Type::Unit,
            },
            body: Block {
                stmts: vec![
                    Stmt::Eval(Expr::Borrow {
                        step: crate::ir::path::PathStep::MapKey {
                            key: Box::new(Expr::Var(unit_var("$t1"))),
                            key_type: Type::UInt(64),
                            value_type: Type::Unit,
                            df_value: None,
                        },
                        base: Box::new(Expr::Var(unit_var("$t0"))),
                    }),
                    Stmt::Eval(Expr::Borrow {
                        step: crate::ir::path::PathStep::MapKey {
                            key: Box::new(Expr::Var(unit_var("$t3"))),
                            key_type: Type::UInt(64),
                            value_type: Type::Unit,
                            df_value: None,
                        },
                        base: Box::new(Expr::Var(unit_var("$t2"))),
                    }),
                ],
                tail: BlockTail::Value(Expr::Unit),
            },
            kind: crate::ir::FunctionKind::Source,
            effects: crate::ir::Effects::PURE,
            explicit_pure: false,
        };
        program.functions.insert(0, f);
        let keys = collect_any_key(&program);
        assert_eq!(keys.len(), 1);
    }

    #[test]
    fn renders_anykey_file_with_variant_comments_and_real_ctors() {
        // Slice 1 of item B (plans/lean-pipeline/item-b-real-anykey-work-plan.md):
        // collected variants now produce real `| k_<mangled> (v : <payload>)`
        // constructors alongside the legacy `| unit` placeholder.
        // Comments in the file header still document each variant
        // (the comment lines were the only output before slice 1).
        let mut keys = BTreeSet::new();
        keys.insert(AnyKeyVariant {
            ctor: "k_u64".to_string(),
            payload_lean_ty: "UInt64".to_string(),
        });
        keys.insert(AnyKeyVariant {
            ctor: "k_address".to_string(),
            payload_lean_ty: "Address".to_string(),
        });
        let out = render_any_key_file(&keys, &Program::default(), &BTreeSet::<String>::new());
        // Both variants appear as comments (sorted: address before u64).
        assert!(
            out.contains("-- variant: k_address : Address"),
            "missing k_address variant comment: {out}"
        );
        assert!(
            out.contains("-- variant: k_u64 : UInt64"),
            "missing k_u64 variant comment: {out}"
        );
        // Real constructors in the inductive (in the same sorted order).
        assert!(
            out.contains("| k_address (v : Address)"),
            "missing k_address real ctor: {out}"
        );
        assert!(
            out.contains("| k_u64 (v : UInt64)"),
            "missing k_u64 real ctor: {out}"
        );
        // Placeholder `| unit` constructor stays for not-yet-migrated
        // call sites + Mutation abbreviation.
        assert!(out.contains("| unit"), "missing unit placeholder: {out}");
        assert!(out.contains("abbrev Mutation"), "missing abbrev: {out}");
        // Each concrete variant also gets an `IntoKey AnyKey <payload>`
        // instance (the 2-param, Key-explicit injection consumed by
        // lemma-package framework functions; see Prelude.Mutation.IntoKey).
        assert!(
            out.contains("instance : IntoKey AnyKey (UInt64) where intoKey v := AnyKey.k_u64 v"),
            "missing IntoKey instance for u64: {out}"
        );
        assert!(
            out.contains(
                "instance : IntoKey AnyKey (Address) where intoKey v := AnyKey.k_address v"
            ),
            "missing IntoKey instance for address: {out}"
        );
        // The round-trip law class is emitted (unconditionally) after the
        // FromAnyKey instances, plus one lawful `rfl` instance per variant.
        assert!(
            out.contains("class LawfulAnyKey (A : Type) [ToAnyKey A] [FromAnyKey A] : Prop where"),
            "missing LawfulAnyKey class: {out}"
        );
        assert!(
            out.contains(
                "instance [Inhabited (UInt64)] : LawfulAnyKey (UInt64) where\n  from_to _ := rfl"
            ),
            "missing LawfulAnyKey instance for u64: {out}"
        );
        assert!(
            out.contains(
                "instance [Inhabited (Address)] : LawfulAnyKey (Address) where\n  from_to _ := rfl"
            ),
            "missing LawfulAnyKey instance for address: {out}"
        );
    }

    #[test]
    fn renders_empty_anykey_with_unit_placeholder_only() {
        // No collected variants -> only `| unit` constructor.
        let keys = BTreeSet::new();
        let out = render_any_key_file(&keys, &Program::default(), &BTreeSet::<String>::new());
        assert!(out.contains("| unit"));
        // No accidental real-ctor emissions when the set is empty.
        // Constructors render as "  | k_..." (two-space indent inside
        // `inductive AnyKey where`); the comment block also mentions
        // `| k_<mangled>` so a bare `contains` would match. Check the
        // indented-constructor form instead.
        assert!(
            !out.contains("  | k_"),
            "expected no k_* ctors in empty AnyKey file: {out}"
        );
        // The `LawfulAnyKey` class scaffold is emitted even for a
        // variant-less package (uniform with the two data classes), but no
        // per-variant lawful instance is produced.
        assert!(
            out.contains("class LawfulAnyKey (A : Type) [ToAnyKey A] [FromAnyKey A] : Prop where"),
            "missing LawfulAnyKey class scaffold in empty AnyKey file: {out}"
        );
        assert!(
            !out.contains(": LawfulAnyKey ("),
            "expected no LawfulAnyKey instances in empty AnyKey file: {out}"
        );
    }

    #[test]
    fn collect_skips_type_param_keys() {
        // Slice 1 of item B: a `BorrowMapKey` whose `key_type` is
        // `TypeParam(0)` (e.g. a generic function body `f<T>(t: &mut Table<T, V>, k: T, v: V)`
        // before monomorphisation) is filtered out -- its Lean
        // payload would reference `T0` which isn't in scope at
        // `Generated/AnyKey.lean`. Per-call monomorphisation is a
        // follow-up.
        let mut program = Program::default();
        let f = crate::ir::Function {
            module: 0,
            name: "f".to_string(),
            signature: crate::ir::Signature {
                type_params: vec!["T".to_string()],
                params: vec![],
                return_type: Type::Unit,
            },
            body: Block {
                stmts: vec![Stmt::Eval(Expr::Borrow {
                    step: crate::ir::path::PathStep::MapKey {
                        key: Box::new(Expr::Var(unit_var("$t1"))),
                        key_type: Type::TypeParam(0),
                        value_type: Type::Unit,
                        df_value: None,
                    },
                    base: Box::new(Expr::Var(unit_var("$t0"))),
                })],
                tail: BlockTail::Value(Expr::Unit),
            },
            kind: crate::ir::FunctionKind::Source,
            effects: crate::ir::Effects::PURE,
            explicit_pure: false,
        };
        program.functions.insert(0, f);
        let keys = collect_any_key(&program);
        assert!(
            keys.is_empty(),
            "TypeParam-keyed BorrowMapKey leaked into AnyKey: {:?}",
            keys
        );
    }

    #[test]
    fn mangle_handles_primitives() {
        let program = Program::default();
        assert_eq!(any_key_ctor_name(&Type::UInt(64), &program), "k_u64");
        assert_eq!(any_key_ctor_name(&Type::Address, &program), "k_address");
        assert_eq!(any_key_ctor_name(&Type::Bool, &program), "k_bool");
    }

    #[test]
    fn mangle_handles_struct_with_type_args() {
        let ty = Type::Struct {
            struct_id: 7,
            type_args: vec![Type::UInt(64)],
        };
        let mut program = Program::default();
        program.modules.insert(
            0,
            crate::ir::Module {
                name: "m".to_string(),
                package_name: String::new(),
                address: String::new(),
                required_imports: Vec::new(),
                is_native: false,
            },
        );
        program.structs.insert(
            7,
            crate::ir::Struct {
                module_id: 0,
                name: "Marker".to_string(),
                qualified_name: "m::Marker".to_string(),
                type_params: vec!["T".to_string()],
                fields: Vec::new(),
                variants: None,
                is_native: false,
            },
        );
        // The datatype's NAME tag, never its positional `StructId`.
        assert_eq!(any_key_ctor_name(&ty, &program), "k_S_m__Marker_u64");
    }

    #[test]
    fn mangle_handles_tuple() {
        let ty = Type::Tuple(vec![Type::UInt(8), Type::Address]);
        assert_eq!(
            any_key_ctor_name(&ty, &Program::default()),
            "k_Tuple_u8_address"
        );
    }

    fn unit_fn(name: &str, type_params: Vec<&str>, body: Block) -> crate::ir::Function {
        crate::ir::Function {
            module: 0,
            name: name.to_string(),
            signature: crate::ir::Signature {
                type_params: type_params.into_iter().map(|s| s.to_string()).collect(),
                params: vec![],
                return_type: Type::Unit,
            },
            body,
            kind: crate::ir::FunctionKind::Source,
            effects: crate::ir::Effects::PURE,
            explicit_pure: false,
        }
    }

    #[test]
    fn anykey_taint_gates_constraint_to_map_key_typeparams() {
        // `borrow_k<K, V>` borrows a map keyed by `K` (TypeParam(0)) --
        // only param 0 reaches the `ToAnyKey`/`FromAnyKey` typeclass,
        // not `V`. `caller<U>` calls `borrow_k<U, Unit>` passing its own
        // `U` at the key slot, so taint propagates across the call edge.
        // `no_keys<T>` does no map ops and is never tainted -- it must
        // NOT carry the constraint (post-catch-all-deletion that would
        // fail to resolve at a concrete non-key instantiation).
        let mut program = Program::default();
        program.functions.insert(
            0,
            unit_fn(
                "borrow_k",
                vec!["K", "V"],
                Block {
                    stmts: vec![Stmt::Eval(Expr::Borrow {
                        step: crate::ir::path::PathStep::MapKey {
                            key: Box::new(Expr::Var(unit_var("$t1"))),
                            key_type: Type::TypeParam(0),
                            value_type: Type::Unit,
                            df_value: None,
                        },
                        base: Box::new(Expr::Var(unit_var("$t0"))),
                    })],
                    tail: BlockTail::Value(Expr::Unit),
                },
            ),
        );
        program.functions.insert(
            1,
            unit_fn(
                "no_keys",
                vec!["T"],
                Block {
                    stmts: vec![],
                    tail: BlockTail::Value(Expr::Unit),
                },
            ),
        );
        program.functions.insert(
            2,
            unit_fn(
                "caller",
                vec!["U"],
                Block {
                    stmts: vec![Stmt::Eval(Expr::Call {
                        fun: 0,
                        type_args: vec![Type::TypeParam(0), Type::Unit],
                        args: vec![],
                    })],
                    tail: BlockTail::Value(Expr::Unit),
                },
            ),
        );

        // Call `compute_*` directly (the cached predicate is keyed by
        // `Program` address, which can collide across tests via stack
        // reuse).
        let deps = compute_anykey_typeparam_deps(&program);
        assert_eq!(
            deps[&0],
            vec![true, false],
            "borrow_k: K is a map key, V is not"
        );
        assert_eq!(
            deps[&1],
            vec![false],
            "no_keys: never reaches the typeclass"
        );
        assert_eq!(
            deps[&2],
            vec![true],
            "caller: U flows into a map key via the call"
        );
    }
}
