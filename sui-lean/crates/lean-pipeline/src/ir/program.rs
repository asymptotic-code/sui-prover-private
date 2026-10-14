//! Program-level container.
//!
//! See `plans/lean-pipeline/ir.md` "Program" section. `Program` carries the
//! declarations and pipeline metadata consumed by later stages and rendering.

use std::collections::{BTreeMap, BTreeSet};

use ethnum::U256;
use num::BigUint;

use super::expr::Block;
use super::function::{Effects, Function, Signature};
use super::natives::{CalleeRef, NativeDecl, NativeRegistry};
use super::ty::Type;
use super::{AbortProvenance, FunId, GlobalId, ModId, StructId};

/// Stable association between a source global and the hidden parameter that
/// carries it through one function.
///
/// The parameter is identified by its stable signature index, not by its
/// generated name or `VarId`: later stages append World/ghost parameters and
/// SSA renames binders, but all current stages preserve parameter order.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct FunctionGlobalBinding {
    pub global: GlobalId,
    pub parameter_index: usize,
}

/// Options bundle for [`Program::insert_synthetic_native`] /
/// [`crate::ir::ProgramBuilder::insert_synthetic_native`]. Six named
/// fields rather than a six-arg signature.
#[derive(Debug, Clone)]
pub struct SyntheticNativeOpts {
    /// Module that owns the native. Typically a prelude module.
    pub module: ModId,
    /// Effects classification. Set on the new [`NativeDecl`].
    pub effects: Effects,
    /// Whether the native carries an explicit `#[ext(pure)]`-style
    /// pin. Synthetic natives that participate in the
    /// `classify_effects` fixpoint usually set this `true` to keep
    /// their pre-classified effects from being demoted.
    pub explicit_pure: bool,
    /// Optional back-reference to a "target" native (used by stage 10's
    /// `.aborts` companions to link back to their main op).
    pub spec_target: Option<FunId>,
}

impl SyntheticNativeOpts {
    pub(crate) fn into_decl(self, name: &str, signature: Signature) -> NativeDecl {
        NativeDecl {
            module: self.module,
            name: name.to_string(),
            signature,
            effects: self.effects,
            explicit_pure: self.explicit_pure,
            is_framework: true,
            spec_target: self.spec_target,
            user_native: None,
        }
    }
}

fn next_id(ids: impl Iterator<Item = usize>, exhausted: &'static str) -> usize {
    ids.max()
        .map_or(0, |id| id.checked_add(1).expect(exhausted))
}

/// The whole program. `BTreeMap`s rather than `HashMap`s -- iteration
/// order is part of the determinism contract (see
/// `plans/lean-pipeline/testing-strategy.md` "Determinism rules").
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Program {
    pub abort_provenance: AbortProvenance,
    pub modules: BTreeMap<ModId, Module>,
    pub structs: BTreeMap<StructId, Struct>,
    /// Addressable program globals, keyed by stable [`GlobalId`].
    ///
    /// Move translation leaves this table empty. C frontends populate it
    /// explicitly and refer to entries through `Expr::BorrowGlobal` and
    /// `BorrowNode::GlobalRoot`.
    pub globals: BTreeMap<GlobalId, Global>,
    /// Trusted assertion supplied by an external-memory frontend before
    /// executable global borrows are lowered.
    ///
    /// This is deliberately named as an assertion rather than a certificate:
    /// the proof/certificate remains owned by the frontend. A C frontend may
    /// set this only after checking that the global schema/identity matches
    /// this [`Program`] and that its borrow/exclusivity and root-access
    /// certificates cover every emitted `BorrowGlobal` / `GlobalRoot` node.
    /// Move programs and programs with no executable global nodes leave it
    /// `false`.
    pub external_global_borrows_certified: bool,
    /// Per-function globals threaded as hidden global parameters,
    /// in deterministic `GlobalId` order.
    ///
    /// [`crate::global_threading::thread_globals`] populates this table at
    /// the same time it appends the parameters. It is explicit metadata for
    /// boundary tooling and certificates; consumers must not recover global
    /// identity from the generated parameter names.
    pub function_globals: BTreeMap<FunId, Vec<FunctionGlobalBinding>>,
    /// Translated user Move functions. Every entry has a real,
    /// pipeline-processed body. Native declarations live in
    /// [`Self::natives`].
    pub functions: BTreeMap<FunId, Function>,
    /// Native function declarations (framework, user-declared,
    /// stage-10 synthesised). See [`NativeRegistry`].
    pub natives: NativeRegistry,
    /// Maps a `#[spec(prove)]` wrapper function to the translated or native
    /// implementation it specifies (both as IR `FunId`s). Populated in stage 2 from the
    /// Move model's `FunctionTargetsHolder::get_fun_by_spec`. Empty for
    /// functions with no spec/impl pairing. `stage_12_obligations`
    /// reads this to pair `<wrapper>.{requires,asserts,ensures}` with
    /// the impl (and its `.aborts`) when building proof obligations.
    pub spec_to_impl: BTreeMap<FunId, FunId>,
    /// `#[spec(prove)]` wrappers that declare NO `target=` -- standalone
    /// lemmas (`PackageTargets::find_target_spec` returns nothing), so they
    /// have no impl to pair with and never appear in [`Self::spec_to_impl`].
    /// They are still declared verification targets: `stage_12_obligations`
    /// emits `<spec>_correct` for each from the wrapper's OWN companions
    /// (`requires -> (asserts ->) ensures(spec args)`) -- the impl side of a
    /// paired obligation drives dispatch and the `target` metadata, never the
    /// statement, so the identical shape is well-formed with the spec itself
    /// in the target slot. Before this set existed these six (in sui-system)
    /// were dropped silently and nothing in the corpus proved them.
    pub targetless_prove_specs: BTreeSet<FunId>,
    /// Qualified name (`pkg::module::name`) of every declared
    /// `#[spec(prove)]` wrapper that got an IR `FunId`, captured while
    /// the Move model is still in scope. `write_obligations_manifest`
    /// names a spec from here when [`Self::functions`] cannot, so a
    /// wrapper that never grew a translated body is still DISCLOSED
    /// rather than skipped -- skipping was the last route by which a
    /// requested proof could leave neither an obligation nor a
    /// `[[spec_no_obligation]]` row.
    pub prove_spec_names: BTreeMap<FunId, String>,
    /// Declared `#[spec(prove)]` wrappers that reached NEITHER
    /// [`Self::spec_to_impl`] NOR [`Self::targetless_prove_specs`], as
    /// (`pkg::module::name`, reason). Two reasons, both meaning a
    /// requested proof cannot be built at all: `target_not_translated`
    /// (the `target=` impl has no IR `FunId`) and
    /// `wrapper_not_translated` (the spec itself was never lifted, so it
    /// has no `FunId` to be found by -- the reason this is a name list
    /// and not a `FunId` set). Restricted to target modules, matching
    /// the stderr report these rows supersede: a dependency's spec is
    /// not this package's obligation. Consumed only by
    /// `write_obligations_manifest`.
    pub unmapped_prove_specs: BTreeSet<(String, String)>,
    /// Spec wrappers whose `#[spec]` attribute has `ignore_abort`.
    /// Stage 12 uses this to skip abort-coverage obligations while still
    /// emitting postcondition obligations.
    pub spec_ignore_aborts: BTreeMap<FunId, bool>,
    /// Maps a TRUSTED spec wrapper to the impl (or native) function it
    /// specifies. Trusted = the Lean pipeline does not prove it:
    /// `#[spec(target=...)]` without `prove` or with `skip`
    /// (`PackageTargets::no_verify_specs`), and `ext(backend = b"boogie")` specs
    /// (`PackageTargets::boogie_backend_specs` -- proven on the Boogie
    /// side of the hybrid flow). Disjoint from [`Self::spec_to_impl`],
    /// whose consumers rely on prove-only semantics. Stage 12 emits
    /// these pairs' obligations as [`FunctionKind::Axiom`] (assumed,
    /// `axiom` in Lean) instead of [`FunctionKind::Theorem`]. Unlike
    /// `spec_to_impl`, the impl side may be a NATIVE `FunId` (e.g. a
    /// trusted spec on `std::string::utf8`). The
    /// [`TrustReason`](super::TrustReason) records WHY the pair is
    /// trusted (non-prove / skip / boogie) for `obligations.toml`.
    pub trusted_spec_to_impl: BTreeMap<FunId, (FunId, super::TrustReason)>,
    /// Spec-only ghost variables each function threads, as the `(K, V)`
    /// type pairs from `prover::ghost`. Populated in stage 2 from the
    /// upstream `SpecGlobalVariableInfo` annotation
    /// (`get_info(target.data).all_vars()`, which is transitive across
    /// callees); consumed by the stage-4 ghost-threading pass. Order
    /// follows the upstream `Type` sort so caller/callee agree on
    /// positional threading. Absent/empty for functions touching no
    /// ghost. NEVER materialised in `World`/`TyCode` -- ghost is
    /// spec-only.
    pub ghost_vars: BTreeMap<FunId, Vec<(Type, Type)>>,
    /// Per-native ghost-marker seed derived from the Move model in
    /// stage 2 (`ProgramBuilder::derive_native_ghost_seed`): each native
    /// `FunId` maps to the `(K, V)` ghost slots its target spec declares.
    /// Consumed once by the stage-4 ghost pass to seed
    /// [`Self::ghost_vars`] for natives (which carry no body/annotation of
    /// their own), from which the callee->caller fixpoint propagates to
    /// callers. Replaces the former hand-coded native registries. Empty
    /// for packages that touch no ghost-writing/reading natives.
    pub ghost_native_seed: BTreeMap<FunId, Vec<(Type, Type)>>,
    /// Opaque ghost-output symbols synthesised by the stage-4 ghost pass
    /// for ensures-published ghosts: a TRUSTED spec (see
    /// [`Self::trusted_spec_to_impl`]) whose ensures constrain a ghost
    /// `(K, V)` that the target impl's body never realises (no callee
    /// writes it). Boogie realises that value by havoc-and-assume at the
    /// opaque call; the functional mirror is an OPAQUE Lean constant
    /// `<impl>__ghost_out_<sid(K)> : <impl params> -> V` that the impl's
    /// ghost slot returns, with the trusted axiom as its defining
    /// constraint. Without this the axiom quantifies over a passthrough
    /// input and is INCONSISTENT (see
    /// plans/lean-pipeline/ghost-support.md Part 4). Keyed by the impl
    /// `FunId`; each entry names the synthesised native `FunId` and its
    /// `(K, V)` pair. The renderer emits an `opaque` declaration in the
    /// impl's module for every entry.
    pub ghost_opaque_outputs: BTreeMap<FunId, Vec<(Type, Type, FunId)>>,
}

impl Program {
    /// Resolve a [`FunId`] to either a translated function or a
    /// native declaration. Callees that don't appear in either map
    /// return `None`, which callers should treat as a bug
    /// (`UnknownFunId`) rather than silently degrade.
    pub fn lookup_callee(&self, fid: FunId) -> Option<CalleeRef<'_>> {
        if let Some(f) = self.functions.get(&fid) {
            return Some(CalleeRef::Translated(f));
        }
        self.natives.decls.get(&fid).map(CalleeRef::Native)
    }

    /// Idempotently register a pipeline-synthesised native (no
    /// upstream Move source). Stage 10's `BoundedU{N}_<op>` family
    /// and the dynamic-fields TypedMap shims are the main users.
    ///
    /// If the exact synthetic declaration is already registered, its
    /// `FunId` is returned and no new entry is inserted. A same-named
    /// declaration with different provenance, module, signature, effects,
    /// or spec target is a collision rather than the same intrinsic; it is
    /// left intact and a distinct synthetic declaration is allocated.
    /// Otherwise a fresh `FunId` is allocated (max + 1 across both
    /// `functions` and `natives.decls`) and returned.
    ///
    /// The natives created here carry `is_framework: true` because
    /// they map to prelude-defined Lean code. Callers that need a
    /// non-framework synthetic (e.g. a user-declared `native fun`
    /// stub) should insert into `natives.decls` directly.
    pub fn insert_synthetic_native(
        &mut self,
        name: &str,
        signature: Signature,
        opts: SyntheticNativeOpts,
    ) -> FunId {
        let decl = opts.into_decl(name, signature);
        if let Some((&fid, _)) = self.natives.decls.iter().find(|(_, d)| **d == decl) {
            return fid;
        }
        let fid = self.next_function_id();
        self.natives.decls.insert(fid, decl);
        fid
    }

    pub(crate) fn next_function_id(&self) -> FunId {
        next_id(
            self.functions
                .keys()
                .chain(self.natives.decls.keys())
                .copied(),
            "function ID space exhausted",
        )
    }

    pub(crate) fn next_struct_id(&self) -> StructId {
        next_id(self.structs.keys().copied(), "struct ID space exhausted")
    }

    pub(crate) fn next_global_id(&self) -> GlobalId {
        next_id(self.globals.keys().copied(), "global ID space exhausted")
    }

    pub(crate) fn next_module_id(&self) -> ModId {
        next_id(self.modules.keys().copied(), "module ID space exhausted")
    }

    /// Resolve a module by its Move package and module names.
    pub(crate) fn module_id_by_name(&self, package: &str, module: &str) -> Option<ModId> {
        self.modules
            .iter()
            .find(|(_, decl)| decl.package_name == package && decl.name == module)
            .map(|(id, _)| *id)
    }

    /// Resolve a native declaration by its Move package, module, and name.
    /// Translated functions are intentionally excluded.
    pub(crate) fn native_id_by_name(
        &self,
        package: &str,
        module: &str,
        name: &str,
    ) -> Option<FunId> {
        self.natives.decls.iter().find_map(|(fid, decl)| {
            let module_decl = self.modules.get(&decl.module)?;
            (decl.name == name && module_decl.package_name == package && module_decl.name == module)
                .then_some(*fid)
        })
    }

    /// All translated-function `FunId`s, in deterministic order.
    /// Snapshot these before a mutate-each-function pass instead of
    /// the `functions.iter().map(|(id, _)| *id).collect()` idiom.
    pub fn body_ids(&self) -> Vec<FunId> {
        self.functions.keys().copied().collect()
    }

    /// The lowest `ModId` in the program. Used as the host module for
    /// synthetic natives. Panics on an empty program -- a stage that
    /// registers a synthetic native always runs on a non-empty program
    /// (no fallback).
    pub fn first_module_id(&self) -> ModId {
        *self
            .modules
            .keys()
            .next()
            .expect("program has at least one module")
    }

    /// Run `f` over every translated function's body. Ids are
    /// snapshotted first; each body borrow is scoped to one call.
    pub fn for_each_body_mut(&mut self, mut f: impl FnMut(FunId, &mut Block)) {
        for fid in self.body_ids() {
            if let Some(func) = self.functions.get_mut(&fid) {
                f(fid, &mut func.body);
            }
        }
    }

    /// The `StructId` whose `Struct::qualified_name` equals `qname`,
    /// if any.
    pub fn struct_id_by_qualified_name(&self, qname: &str) -> Option<StructId> {
        self.structs
            .iter()
            .find(|(_, s)| s.qualified_name == qname)
            .map(|(id, _)| *id)
    }
}

/// A first-class addressable program global.
///
/// `mutable` distinguishes writable C storage from readonly globals without
/// borrowing Move's checked-UInt or resource semantics. [`GlobalDefinition`]
/// distinguishes storage whose startup value is defined by the program from a
/// value supplied by its boundary. A defined startup value is declaration
/// metadata only: ordinary functions still receive the current global value
/// through the explicit parameters introduced by global threading.
///
/// `Address` is permitted as an opaque scalar, but external-memory frontends
/// must not encode storage pointers in it (the C contract forbids
/// pointer-to-integer/address round trips).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Global {
    pub module_id: ModId,
    pub name: String,
    pub ty: Type,
    pub mutable: bool,
    pub definition: GlobalDefinition,
}

impl Global {
    /// Type of the hidden parameter introduced by global threading.
    /// Readonly globals travel through the erased immutable-reference path;
    /// writable globals use the existing mutation-return machinery.
    pub fn threaded_param_type(&self) -> Type {
        if self.mutable {
            Type::MutableRef {
                inner: Box::new(self.ty.clone()),
                root: Box::new(self.ty.clone()),
            }
        } else {
            Type::Reference(Box::new(self.ty.clone()))
        }
    }
}

/// Where a global's value comes from at the program boundary.
///
/// A mutable [`Defined`](GlobalDefinition::Defined) global is initialized once
/// at program startup. Its initializer must never be substituted for the
/// current state at an arbitrary function call. [`BoundarySupplied`] globals
/// deliberately have no value embedded in the program.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum GlobalDefinition {
    BoundarySupplied,
    Defined { startup_value: StaticValue },
}

/// A closed, effect-free value accepted as a program-global initializer.
///
/// This is intentionally separate from [`super::Const`]: expression defaults,
/// variables, calls, borrows, and pointer relocations are not representable.
/// `Repeat` is the compact form of a vector value and preserves its exact
/// length (in particular, it is not an `Inhabited.default` placeholder).
///
/// ```compile_fail
/// use lean_pipeline::ir::StaticValue;
///
/// // Pointer-bearing C initializers must remain in the frontend until the
/// // shared IR has a provenance-preserving memory model.
/// let _ = StaticValue::PointerRelocation { symbol: "other_global" };
/// ```
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum StaticValue {
    Unit,
    Bool(bool),
    UInt {
        bits: u32,
        value: U256,
    },
    Address(BigUint),
    Vector(Vec<StaticValue>),
    Repeat {
        value: Box<StaticValue>,
        count: usize,
    },
    Tuple(Vec<StaticValue>),
    Struct {
        struct_id: StructId,
        variant: Option<usize>,
        fields: Vec<StaticValue>,
    },
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Module {
    pub name: String,
    pub package_name: String,
    /// 64-char zero-padded lowercase hex of the module's numeric
    /// defining address (e.g. `0000..0002` for the Sui framework).
    /// Empty for synthetic / prelude / test modules. Used by the
    /// TyCode universe to build Move-faithful `type_name` strings
    /// (`<addr>::<module>::<type>`) so coin-ordering comparisons
    /// (`bcs::to_bytes(type_name X) < ...`) match Move byte order.
    pub address: String,
    pub required_imports: Vec<ModId>,
    /// True for modules provided by the prelude or another static source.
    /// The renderer skips emitting these.
    pub is_native: bool,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Struct {
    pub module_id: ModId,
    pub name: String,
    pub qualified_name: String,
    pub type_params: Vec<String>,
    /// Non-empty for plain structs; empty for enums (use `variants`).
    pub fields: Vec<Field>,
    /// `Some` for enums, `None` for plain structs.
    pub variants: Option<Vec<Variant>>,
    /// True iff this struct's Move body is replaced by a Lean prelude
    /// definition. Lifted via `lift_struct` with `is_native = true`
    /// (`stage_02_ir_cfg::module_lift`): the name, type-params, and (for
    /// structs) the real `fields` are still recorded so cross-module
    /// references and field accesses resolve; the renderer skips emitting
    /// a body for natives whose module has a `<Module>Natives.lean`
    /// sibling.
    pub is_native: bool,
}

impl Struct {
    pub fn variant_by_tag(&self, tag: usize) -> Option<&Variant> {
        self.variants
            .as_ref()?
            .iter()
            .find(|variant| variant.tag == tag)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Field {
    pub name: String,
    pub field_type: Type,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Variant {
    pub name: String,
    pub tag: usize,
    pub fields: Vec<Field>,
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::{BlockTail, Expr, FunctionKind};

    fn module(package: &str, name: &str) -> Module {
        Module {
            name: name.to_string(),
            package_name: package.to_string(),
            address: String::new(),
            required_imports: Vec::new(),
            is_native: false,
        }
    }

    fn signature() -> Signature {
        Signature {
            type_params: Vec::new(),
            params: Vec::new(),
            return_type: Type::Unit,
        }
    }

    #[test]
    fn qualified_name_queries_preserve_package_module_and_native_kind() {
        let mut program = Program::default();
        program.modules.insert(1, module("P", "m"));
        program.modules.insert(2, module("Q", "m"));
        program.modules.insert(3, module("P", "n"));
        program.natives.decls.insert(
            10,
            NativeDecl {
                module: 1,
                name: "f".to_string(),
                signature: signature(),
                effects: Effects::PURE,
                explicit_pure: false,
                is_framework: false,
                spec_target: None,
                user_native: None,
            },
        );
        program.functions.insert(
            11,
            Function {
                module: 1,
                name: "translated".to_string(),
                signature: signature(),
                body: Block {
                    stmts: Vec::new(),
                    tail: BlockTail::Value(Expr::Unit),
                },
                kind: FunctionKind::Source,
                effects: Effects::PURE,
                explicit_pure: false,
            },
        );

        assert_eq!(program.module_id_by_name("P", "m"), Some(1));
        assert_eq!(program.module_id_by_name("Q", "m"), Some(2));
        assert_eq!(program.module_id_by_name("P", "n"), Some(3));
        assert_eq!(program.module_id_by_name("P", "missing"), None);
        assert_eq!(program.native_id_by_name("P", "m", "f"), Some(10));
        assert_eq!(program.native_id_by_name("Q", "m", "f"), None);
        assert_eq!(program.native_id_by_name("P", "m", "translated"), None);
        assert_eq!(program.next_function_id(), 12);
    }

    #[test]
    fn native_name_query_skips_dangling_declarations() {
        let mut program = Program::default();
        program.modules.insert(1, module("P", "m"));
        for (fid, module_id) in [(5, 99), (10, 1)] {
            program.natives.decls.insert(
                fid,
                NativeDecl {
                    module: module_id,
                    name: "f".to_string(),
                    signature: signature(),
                    effects: Effects::PURE,
                    explicit_pure: false,
                    is_framework: false,
                    spec_target: None,
                    user_native: None,
                },
            );
        }

        assert_eq!(program.native_id_by_name("P", "m", "f"), Some(10));
    }

    #[test]
    #[should_panic(expected = "function ID space exhausted")]
    fn next_function_id_rejects_exhaustion() {
        let mut program = Program::default();
        program.natives.decls.insert(
            FunId::MAX,
            NativeDecl {
                module: 0,
                name: "f".to_string(),
                signature: signature(),
                effects: Effects::PURE,
                explicit_pure: false,
                is_framework: false,
                spec_target: None,
                user_native: None,
            },
        );

        program.next_function_id();
    }

    #[test]
    #[should_panic(expected = "struct ID space exhausted")]
    fn next_struct_id_rejects_exhaustion() {
        let mut program = Program::default();
        program.structs.insert(
            StructId::MAX,
            Struct {
                module_id: 0,
                name: "S".to_string(),
                qualified_name: "P::m::S".to_string(),
                type_params: Vec::new(),
                fields: Vec::new(),
                variants: None,
                is_native: false,
            },
        );

        program.next_struct_id();
    }

    #[test]
    #[should_panic(expected = "module ID space exhausted")]
    fn next_module_id_rejects_exhaustion() {
        let mut program = Program::default();
        program.modules.insert(ModId::MAX, module("P", "m"));

        program.next_module_id();
    }
}
