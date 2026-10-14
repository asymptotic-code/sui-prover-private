//! Ergonomic constructors for hand-built IR fixtures, plus the
//! stateful [`ProgramBuilder`] used by stage 2 to assemble a `Program`.
//!
//! See `plans/lean-pipeline/testing-strategy.md` "Fixture authoring"
//! section. The free constructor functions exist primarily to make
//! unit-test fixtures readable; pipeline production code may use them
//! too.
//!
//! [`ProgramBuilder`] is the canonical entry point for building a
//! `Program` from upstream Move-model identifiers. See
//! `plans/lean-pipeline/ir.md` decision-log §18.

use std::collections::{BTreeMap, BTreeSet};

use ethnum::U256;
use move_model::model::{DatatypeId, FunId as MoveFunId, ModuleId as MoveModuleId, QualifiedId};

use super::borrow::{BorrowEdge, BorrowNode};
use super::expr::{Block, BlockTail, Expr, MatchArm, Stmt};
use super::function::Function;
use super::ops::BinOp;
use super::path::PathStep;
use super::program::{Global, Module, Program, Struct};
use super::quant::{QuantDomain, QuantifierKind};
use super::ty::Const;
use super::{FunId, GlobalId, ModId, StructId, Type, VarId};

// ---------------------------------------------------------------------------
// Atoms
// ---------------------------------------------------------------------------

/// `Var(name)`. The name is interned into a `VarId`.
pub fn var(name: &str) -> Expr {
    Expr::Var(name.into())
}

/// `Const::Bool(b)`.
pub fn lit_bool(b: bool) -> Expr {
    Expr::Const(Const::Bool(b))
}

/// `Const::UInt { bits: 8, value: n }`.
pub fn lit_u8(n: u8) -> Expr {
    Expr::Const(Const::UInt {
        bits: 8,
        value: U256::from(n),
    })
}

/// `Const::UInt { bits: 64, value: n }`.
pub fn lit_u64(n: u64) -> Expr {
    Expr::Const(Const::UInt {
        bits: 64,
        value: U256::from(n),
    })
}

/// `Const::UInt { bits, value }`.
pub fn lit_uint(bits: u32, value: U256) -> Expr {
    Expr::Const(Const::UInt { bits, value })
}

/// `Expr::Unit`.
pub fn unit() -> Expr {
    Expr::Unit
}

// ---------------------------------------------------------------------------
// Compound
// ---------------------------------------------------------------------------

/// The lone element if `elems` has length 1, else `Expr::Tuple(elems)`.
/// This is the canonical "loop_state / phi tuple" shape: a 1-slot merge
/// is carried unwrapped, a multi-slot one as a Tuple. Used by stage 5
/// (and read back by stage 7).
pub fn tuple_or_single(mut elems: Vec<Expr>) -> Expr {
    if elems.len() == 1 {
        elems.pop().unwrap()
    } else {
        Expr::Tuple(elems)
    }
}

/// Inverse of [`tuple_or_single`] for one level: unwrap a 1-element
/// `Tuple`, else return `e` unchanged.
pub fn untuple_single(e: Expr) -> Expr {
    match e {
        Expr::Tuple(mut elems) if elems.len() == 1 => elems.pop().unwrap(),
        other => other,
    }
}

pub fn binop(op: BinOp, lhs: Expr, rhs: Expr) -> Expr {
    Expr::BinOp {
        op,
        lhs: Box::new(lhs),
        rhs: Box::new(rhs),
    }
}

pub fn call(fun: FunId, args: Vec<Expr>) -> Expr {
    Expr::Call {
        fun,
        type_args: Vec::new(),
        args,
    }
}

pub fn field(struct_id: StructId, field_index: usize, base: Expr) -> Expr {
    Expr::Field {
        struct_id,
        field_index,
        base: Box::new(base),
    }
}

pub fn if_expr(cond: Expr, then_branch: Block, else_branch: Block) -> Expr {
    Expr::If {
        cond: Box::new(cond),
        then_branch: Box::new(then_branch),
        else_branch: Box::new(else_branch),
    }
}

/// `Expr::While { header, cond, body }`. The header is the
/// per-iteration cond-computation prefix; pass `Block::just(unit())`
/// (or `block(vec![], tail_value(unit()))`) when the cond is a plain
/// pre-computed value.
pub fn while_expr(header: Block, cond: Expr, body: Block) -> Expr {
    Expr::While {
        header: Box::new(header),
        cond: Box::new(cond),
        body: Box::new(body),
        iter_locals: Vec::new(),
        header_exit_locals: Vec::new(),
        live_out: Vec::new(),
    }
}

// ---------------------------------------------------------------------------
// Statements
// ---------------------------------------------------------------------------

/// `let pat := value` with all-named bindings (no wildcards).
/// `pat` must be non-empty -- use [`eval`] for empty.
/// Use [`let_stmt_pat`] for patterns with wildcards.
pub fn let_stmt(pat: &[&str], value: Expr) -> Stmt {
    assert!(
        !pat.is_empty(),
        "let_stmt: empty pattern (use eval(...) for side-effect-only stmts)"
    );
    Stmt::Let {
        pattern: pat.iter().map(|s| Some((*s).into())).collect(),
        value,
    }
}

/// `let pat := value` with wildcard support. `None` entries become `_`
/// in Lean output. Pattern must contain at least one `Some`.
pub fn let_stmt_pat(pat: Vec<Option<&str>>, value: Expr) -> Stmt {
    assert!(
        pat.iter().any(|p| p.is_some()),
        "let_stmt_pat: every position is None (use eval(...) instead)"
    );
    Stmt::Let {
        pattern: pat.into_iter().map(|s| s.map(Into::into)).collect(),
        value,
    }
}

/// `Stmt::Eval(e)` -- evaluate `e` for side effect, drop the value.
pub fn eval(e: Expr) -> Stmt {
    Stmt::Eval(e)
}

// ---------------------------------------------------------------------------
// BlockTails
// ---------------------------------------------------------------------------

pub fn tail_value(e: Expr) -> BlockTail {
    BlockTail::Value(e)
}

pub fn tail_break(level: u32, value: Expr) -> BlockTail {
    BlockTail::Break {
        level,
        value: Box::new(value),
    }
}

pub fn tail_continue(level: u32, value: Expr) -> BlockTail {
    BlockTail::Continue {
        level,
        value: Box::new(value),
    }
}

pub fn tail_return(value: Expr) -> BlockTail {
    BlockTail::Return(Box::new(value))
}

pub fn tail_abort(code: Expr) -> BlockTail {
    BlockTail::Abort {
        code: Box::new(code),
    }
}

// ---------------------------------------------------------------------------
// Blocks
// ---------------------------------------------------------------------------

/// `Block { stmts: [], tail: BlockTail::Value(e) }`. The simplest block.
pub fn just(e: Expr) -> Block {
    Block {
        stmts: Vec::new(),
        tail: BlockTail::Value(e),
    }
}

/// Build a `Block` with an explicit tail.
pub fn block(stmts: Vec<Stmt>, tail: BlockTail) -> Block {
    Block { stmts, tail }
}

impl Block {
    /// Block with no statements, tail `BlockTail::Value(e)`.
    pub fn just(e: Expr) -> Self {
        just(e)
    }

    pub fn push_let<S>(&mut self, pattern: Vec<S>, value: Expr)
    where
        S: Into<VarId>,
    {
        let pat: Vec<Option<VarId>> = pattern.into_iter().map(|s| Some(s.into())).collect();
        assert!(
            !pat.is_empty(),
            "push_let: empty pattern (use push_eval for side-effect-only stmts)"
        );
        self.stmts.push(Stmt::Let {
            pattern: pat,
            value,
        });
    }

    /// Push a `Stmt::Let` with wildcard support.
    pub fn push_let_pat(&mut self, pattern: Vec<Option<VarId>>, value: Expr) {
        assert!(
            pattern.iter().any(|p| p.is_some()),
            "push_let_pat: every position is None (use push_eval instead)"
        );
        self.stmts.push(Stmt::Let { pattern, value });
    }

    pub fn push_eval(&mut self, e: Expr) {
        self.stmts.push(Stmt::Eval(e));
    }
}

// ---------------------------------------------------------------------------
// Match arms
// ---------------------------------------------------------------------------

pub fn match_arm(variant: usize, bindings: &[&str], body: Block) -> MatchArm {
    MatchArm {
        variant,
        bindings: bindings.iter().map(|s| (*s).into()).collect(),
        body: Box::new(body),
    }
}

/// `Match { struct_id, selector, cases }`.
pub fn match_expr(struct_id: StructId, selector: Expr, cases: Vec<MatchArm>) -> Expr {
    Expr::Match {
        struct_id,
        selector: Box::new(selector),
        cases,
    }
}

// ---------------------------------------------------------------------------
// References, borrows, writeback (var-slot fixtures)
// ---------------------------------------------------------------------------

/// `&loc` / `&mut loc`.
pub fn borrow_loc(name: &str) -> Expr {
    Expr::BorrowLoc(name.into())
}

/// Borrow a first-class program global by its stable ID.
///
/// This low-level constructor does not certify aliasing. An external-memory
/// frontend may use it only after its borrow/exclusivity gate succeeds and
/// must set `Program::external_global_borrows_certified` before invoking
/// global threading.
pub fn borrow_global(id: GlobalId) -> Expr {
    Expr::BorrowGlobal(id)
}

/// `ReadRef(e)`.
pub fn read_ref(e: Expr) -> Expr {
    Expr::ReadRef(Box::new(e))
}

/// `WriteRef { reference, value }`.
pub fn write_ref(reference: Expr, value: Expr) -> Expr {
    Expr::WriteRef {
        reference: Box::new(reference),
        value: Box::new(value),
    }
}

/// `WriteBack` off a `LocalRoot(node)` via the identity edge. `world`
/// is the optional dynamic-field-writeback `World` slot.
pub fn write_back(node: &str, child: &str, world: Option<&str>) -> Expr {
    Expr::WriteBack {
        node: BorrowNode::LocalRoot(node.into()),
        edge: BorrowEdge::Direct,
        child: child.into(),
        world: world.map(|w| w.into()),
    }
}

/// `IsParent` off a `LocalRoot(node)` via the identity edge.
pub fn is_parent(node: &str, child: &str) -> Expr {
    Expr::IsParent {
        node: BorrowNode::LocalRoot(node.into()),
        edge: BorrowEdge::Direct,
        child: child.into(),
    }
}

/// A dynamic-field map-key borrow off `base` (`Bool` key/value types),
/// whose value is supplied externally by the `df_value` World var.
pub fn map_key_borrow_df(base: Expr, key: Expr, df_value: &str) -> Expr {
    Expr::Borrow {
        step: PathStep::MapKey {
            key: Box::new(key),
            key_type: Type::Bool,
            value_type: Type::Bool,
            df_value: Some(df_value.into()),
        },
        base: Box::new(base),
    }
}

// ---------------------------------------------------------------------------
// Pack / unpack / coercions / labeled block
// ---------------------------------------------------------------------------

/// `Pack` of a plain struct (no variant).
pub fn pack(struct_id: StructId, fields: Vec<Expr>) -> Expr {
    Expr::Pack {
        struct_id,
        type_args: Vec::new(),
        variant: None,
        fields,
    }
}

/// `Unpack` of a plain struct (no variant).
pub fn unpack(struct_id: StructId, value: Expr) -> Expr {
    Expr::Unpack {
        struct_id,
        variant: None,
        value: Box::new(value),
    }
}

/// `ToProp(e)` -- Bool -> Prop coercion.
pub fn to_prop(e: Expr) -> Expr {
    Expr::ToProp(Box::new(e))
}

/// `ToBool(e)` -- Prop -> Bool coercion.
pub fn to_bool(e: Expr) -> Expr {
    Expr::ToBool(Box::new(e))
}

/// `LabeledBlock { body, result_ty }`.
pub fn labeled_block(body: Block, result_ty: Type) -> Expr {
    Expr::LabeledBlock {
        body: Box::new(body),
        result_ty,
    }
}

// ---------------------------------------------------------------------------
// Quantifier / while-with-iter-locals
// ---------------------------------------------------------------------------

/// `forall <binder> : Bool, <body>` over an unbounded domain. The
/// default fixture quantifier; tests needing other kinds/domains build
/// the `Expr::Quantifier` literal.
pub fn forall(binder: &str, body: Block) -> Expr {
    Expr::Quantifier {
        kind: QuantifierKind::Forall,
        binder: binder.into(),
        binder_type: Type::Bool,
        domain: QuantDomain::Unbounded,
        body: Box::new(body),
    }
}

/// `While` carrying `iter_locals` binders (the stage-5+ shape). The
/// `header` runs each iteration before `cond` / `body`.
///
/// `header_exit_locals` defaults to the iteration-entry binder names --
/// the value stage 5 records when the `header` rebinds no carried slot,
/// which is the shape every caller of this helper builds. Emitting an
/// empty vector instead would violate the stage-5 postcondition on
/// [`Expr::While`] (equal arity with `iter_locals`), so this builder
/// could not construct the shape its own doc comment claims. Callers
/// whose header DOES rebind a slot must write the `Expr::While` literal.
pub fn while_with_locals(
    iter_locals: Vec<(&str, Expr)>,
    header: Block,
    cond: Expr,
    body: Block,
) -> Expr {
    let iter_locals: Vec<(VarId, Expr)> = iter_locals
        .into_iter()
        .map(|(v, e)| (v.into(), e))
        .collect();
    let header_exit_locals: Vec<VarId> = iter_locals.iter().map(|(v, _)| v.clone()).collect();
    Expr::While {
        header: Box::new(header),
        cond: Box::new(cond),
        body: Box::new(body),
        iter_locals,
        header_exit_locals,
        live_out: Vec::new(),
    }
}

// ---------------------------------------------------------------------------
// ProgramBuilder
// ---------------------------------------------------------------------------

/// Every declared `#[spec(prove)]` verification target, sorted into the
/// bucket that decides its fate. Exhaustive by construction: a declared
/// prove-spec lands in exactly one of the first, second or fourth field,
/// so `write_obligations_manifest` can reconcile the whole roster against
/// what stage 12 emitted and no request can go unmentioned. See
/// [`ProgramBuilder::compute_spec_to_impl`].
#[derive(Debug, Default)]
pub(crate) struct ProveSpecRoster {
    /// Wrapper -> impl, both with IR `FunId`s. -> [`Program::spec_to_impl`].
    pub spec_to_impl: BTreeMap<FunId, FunId>,
    /// Standalone lemmas: no `target=`. -> [`Program::targetless_prove_specs`].
    pub targetless: BTreeSet<FunId>,
    /// `pkg::module::name` for every wrapper that got a `FunId`, whether
    /// or not it paired. Not a bucket -- a naming side table.
    /// -> [`Program::prove_spec_names`].
    pub names: BTreeMap<FunId, String>,
    /// Wrappers that resolved to neither of the two buckets above, by
    /// name with a reason. -> [`Program::unmapped_prove_specs`].
    pub unmapped: BTreeSet<(String, String)>,
}

/// Stateful assembly of a [`Program`] from upstream Move-model identifiers.
///
/// `ProgramBuilder` owns deterministic, monotonic ID allocation and a
/// `BTreeMap`-keyed mapping from Move qualified ids to our IR ids.
/// Stage 2 holds one `ProgramBuilder` for the duration of a Move
/// package translation: every per-function call reuses the same
/// builder so cross-function references (Calls, Pack/Unpack of
/// shared structs, etc.) resolve to the same allocated id.
///
/// IDs are allocated lazily on first reference. A first call to
/// [`Self::struct_id`] for a previously-unseen struct allocates a fresh
/// `StructId` and inserts a stub `Struct` with empty fields; stage 2
/// later fills in the real fields/variants via [`Self::insert_struct`].
/// Same pattern for [`Self::function_id`] / [`Self::insert_function`]
/// and [`Self::module_id`] / [`Self::insert_module`].
///
/// Determinism: monotonic counters, `BTreeMap` for qid -> id mappings.
/// Same input bytecode produces byte-identical output `Program`. See
/// `plans/lean-pipeline/testing-strategy.md` "Determinism rules".
#[derive(Debug)]
pub struct ProgramBuilder {
    program: Program,
    next_struct_id: usize,
    next_function_id: usize,
    next_module_id: usize,
    next_global_id: usize,
    /// Move qualified id -> our struct id. Lazy struct creation.
    struct_id_map: BTreeMap<QualifiedId<DatatypeId>, StructId>,
    /// Move qualified id -> our function id. Lazy function creation.
    function_id_map: BTreeMap<QualifiedId<MoveFunId>, FunId>,
    /// Move module id -> our module id. Lazy module creation.
    module_id_map: BTreeMap<MoveModuleId, ModId>,
    /// Frontend-stable global symbol -> IR global id. Unlike Move QIDs,
    /// C/LLVM global symbols already carry their linker-level identity.
    global_id_map: BTreeMap<String, GlobalId>,
    /// Side table for the three `prover::*` intrinsic function ids.
    /// Stage 2 fills these in when it first encounters a call to
    /// each; stage 7 uses them to extract `.requires` / `.ensures` /
    /// `.asserts` companion functions. `None` until first sighting.
    prover_fn_ids: ProverFnIds,
    /// Label-keyed allocation for IR items that have no upstream
    /// Move qualified id -- prelude-only types like `TypedMap` and
    /// the synthetic `Prelude` module they belong to. Pre-pass B
    /// (ghost dynamic fields) and similar passes use these to
    /// register their helpers without colliding with user-defined
    /// modules / structs / functions.
    synthetic_module_ids: BTreeMap<String, ModId>,
    synthetic_struct_ids: BTreeMap<String, StructId>,
    synthetic_function_ids: BTreeMap<String, FunId>,
    /// Per-callee precomputed list of `(K, V)` pairs (one per internal
    /// recognised borrow_mut native call site in the callee's body),
    /// keyed by the callee's upstream `(ModuleId, FunId)`. The types
    /// are in the **callee's own frame** (so `TypeParameter(i)` refers
    /// to the callee's i-th type parameter); call sites instantiate
    /// these against the call's `type_args` to get caller-frame types.
    ///
    /// Populated once at stage 2 entry by
    /// `stage_02_ir_cfg::wrapper_kv::build`. Consumed in
    /// `translate_op::translate_function_call` whose hook records the
    /// instantiated list in `borrow_mut_kv` for the call's dest temp,
    /// enabling per-step placeholder patching for wrappers that chain
    /// multiple internal borrow_mut calls (e.g. navi-lending's
    /// `storage::get_emode_asset_mut` -> dynamic_field::borrow_mut +
    /// table::borrow_mut). See
    /// `plans/lean-pipeline/native-field-collapse-loses-map-key.md`
    /// Step 3.
    user_wrapper_kvs:
        BTreeMap<(MoveModuleId, MoveFunId), Vec<(move_model::ty::Type, move_model::ty::Type)>>,
}

/// Side-table storage for the three `prover::*` intrinsic ids.
/// Stage 2 records these while lifting calls, then the pipeline passes
/// the completed table directly to stage 7 for companion extraction.
/// The ids are not embedded in the assembled [`Program`].
#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct ProverFnIds {
    pub requires: Option<FunId>,
    pub ensures: Option<FunId>,
    pub asserts: Option<FunId>,
}

/// Selector for [`ProgramBuilder::register_prover_fn`]. Distinct
/// from [`super::function::SpecKind`] (which describes companion
/// function flavours) because the `prover::asserts` intrinsic's
/// semantic is "fold into `.aborts` companion", whereas the
/// `Asserts` variant here is lexical -- it identifies the
/// `prover::asserts` call site.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum ProverFnKind {
    Requires,
    Ensures,
    Asserts,
}

impl ProgramBuilder {
    /// Construct an empty `ProgramBuilder`.
    pub fn new() -> Self {
        Self {
            program: Program::default(),
            next_struct_id: 0,
            next_function_id: 0,
            next_module_id: 0,
            next_global_id: 0,
            struct_id_map: BTreeMap::new(),
            function_id_map: BTreeMap::new(),
            module_id_map: BTreeMap::new(),
            global_id_map: BTreeMap::new(),
            prover_fn_ids: ProverFnIds::default(),
            synthetic_module_ids: BTreeMap::new(),
            synthetic_struct_ids: BTreeMap::new(),
            synthetic_function_ids: BTreeMap::new(),
            user_wrapper_kvs: BTreeMap::new(),
        }
    }

    fn alloc_struct_id(&mut self) -> StructId {
        let id = self.next_struct_id;
        self.next_struct_id = self
            .next_struct_id
            .checked_add(1)
            .expect("ProgramBuilder: StructId counter overflowed");
        id
    }

    fn alloc_function_id(&mut self) -> FunId {
        let id = self.next_function_id;
        self.next_function_id = self
            .next_function_id
            .checked_add(1)
            .expect("ProgramBuilder: FunId counter overflowed");
        id
    }

    fn alloc_module_id(&mut self) -> ModId {
        let id = self.next_module_id;
        self.next_module_id = self
            .next_module_id
            .checked_add(1)
            .expect("ProgramBuilder: ModId counter overflowed");
        id
    }

    fn alloc_global_id(&mut self) -> GlobalId {
        let id = self.next_global_id;
        self.next_global_id = self
            .next_global_id
            .checked_add(1)
            .expect("ProgramBuilder: GlobalId counter overflowed");
        id
    }

    /// Mutable accessor for the per-callee user-wrapper kv cache.
    /// Populated once at stage 2 entry by
    /// `stage_02_ir_cfg::wrapper_kv::build`.
    pub(crate) fn user_wrapper_kvs_mut(
        &mut self,
    ) -> &mut BTreeMap<(MoveModuleId, MoveFunId), Vec<(move_model::ty::Type, move_model::ty::Type)>>
    {
        &mut self.user_wrapper_kvs
    }

    /// Read accessor for the per-callee user-wrapper kv cache.
    pub(crate) fn user_wrapper_kvs(
        &self,
    ) -> &BTreeMap<(MoveModuleId, MoveFunId), Vec<(move_model::ty::Type, move_model::ty::Type)>>
    {
        &self.user_wrapper_kvs
    }

    /// Get-or-allocate a deterministic [`StructId`] for a Move struct.
    ///
    /// On first reference, allocates a fresh id and inserts a stub
    /// `Struct` with empty fields/variants. Stage 2 later overwrites
    /// the stub via [`Self::insert_struct`] when the struct is actually
    /// translated. Subsequent calls with the same `qid` return the
    /// same id without touching the stored `Struct`.
    pub fn struct_id(&mut self, qid: QualifiedId<DatatypeId>) -> StructId {
        if let Some(&id) = self.struct_id_map.get(&qid) {
            return id;
        }
        let id = self.alloc_struct_id();
        self.struct_id_map.insert(qid, id);
        let module_id = self.module_id(qid.module_id);
        // Insert a stub. Stage 2 overwrites via insert_struct when the
        // struct is actually translated; references that are never
        // resolved (e.g. opaque framework structs) keep the stub and
        // get filtered as native by the renderer.
        self.program.structs.insert(
            id,
            Struct {
                module_id,
                name: String::new(),
                qualified_name: String::new(),
                type_params: Vec::new(),
                fields: Vec::new(),
                variants: None,
                is_native: false,
            },
        );
        id
    }

    /// Get-or-allocate a deterministic [`FunId`] for a Move function.
    ///
    /// Unlike [`Self::struct_id`], no stub is inserted -- callers must
    /// follow up with [`Self::insert_function`] before the id is
    /// referenced from a `Call`, or the validator will flag
    /// `UnknownFunctionId`. Stage 2 inserts a body-less stub for
    /// natives and filtered-out functions.
    pub fn function_id(&mut self, qid: QualifiedId<MoveFunId>) -> FunId {
        if let Some(&id) = self.function_id_map.get(&qid) {
            return id;
        }
        let id = self.alloc_function_id();
        self.function_id_map.insert(qid, id);
        id
    }

    /// Build the spec-wrapper -> impl `FunId` map from the Move model's
    /// spec hierarchy. For every Move function that was lifted (has an
    /// IR `FunId`), if it is a `#[spec]` wrapper, look up the impl it
    /// targets (`FunctionTargetsHolder::get_fun_by_spec`) and record
    /// the IR-`FunId` pair. Both ends must have IR `FunId`s to be
    /// recorded. Consumed by stage 12 to pair a wrapper's spec
    /// companions with the translated or native impl (and its `.aborts`).
    /// Spec-wrapper -> impl `FunId` map for the package's verification
    /// targets. Sourced from the UNFILTERED `package_targets` (the
    /// `#[spec(target=...)]` map), NOT the holder's `function_specs`
    /// bimap: in `All` generation mode prove.rs fans out per spec module
    /// and `merge_targets_from`s the holders, which leaves that bimap
    /// merged-lossy (only the first module's spec<->impl pairs survive),
    /// so reading it here silently drops every spec module but the first.
    /// `find_target_spec` covers all `#[spec(target=...)]`; gate on
    /// `target_specs()` so only `#[spec(prove)]` wrappers (verification
    /// targets) get PROOF obligations -- non-prove `#[spec(target=...)]`
    /// specs get trusted `axiom`s via
    /// [`Self::compute_trusted_spec_to_impl`] instead. `ext(backend =
    /// b"boogie")` specs are prove-specs (so they sit in `target_specs()`) but are
    /// excluded here: they too are trusted (proven on the Boogie side),
    /// and must land in exactly one of the two maps. Unit-test callers
    /// pass `None` (no specs to pair).
    ///
    /// Returns the pair map AND the set of prove-spec wrappers that
    /// resolve to NO target at all (`find_target_spec` misses) -- see
    /// [`Program::targetless_prove_specs`]. Those are standalone lemmas,
    /// not dropped work: stage 12 builds their obligation from the
    /// wrapper's own companions. Reporting them was not enough on its
    /// own -- a stderr line inside a 25-minute gate log is not a gate.
    ///
    /// THE ROSTER IS A PARTITION, and that is the point. The loop walks
    /// the DECLARED prove targets (`pt.target_specs()` minus the Boogie
    /// ones) rather than the lifted functions, and every arm of the walk
    /// records the spec somewhere: `spec_to_impl`, `targetless`, or --
    /// when neither end resolves -- `unmapped`, by name, because the
    /// unresolved cases are exactly the ones with no `FunId` to be found
    /// by later. Walking `function_id_map` instead could not see a spec
    /// that was never lifted at all, and an `if let` with no `else`
    /// dropped the rest; the manifest then had nothing to disclose and
    /// the request vanished. `unmapped` is confined to target modules
    /// for the same reason the stderr report beside it is: a
    /// dependency's spec is not this package's obligation.
    pub(crate) fn compute_spec_to_impl(
        &self,
        env: &move_model::model::GlobalEnv,
        package_targets: Option<&move_stackless_bytecode::package_targets::PackageTargets>,
        package_name_for_module: &mut dyn FnMut(MoveModuleId) -> String,
    ) -> ProveSpecRoster {
        let mut roster = ProveSpecRoster::default();
        let Some(pt) = package_targets else {
            return roster;
        };
        let boogie_proven = pt.boogie_backend_specs();
        let qualified = |qid: &QualifiedId<MoveFunId>,
                         package_name_for_module: &mut dyn FnMut(MoveModuleId) -> String|
         -> String {
            format!(
                "{}::{}",
                package_name_for_module(qid.module_id),
                env.get_function(*qid).get_full_name_str()
            )
        };
        for spec_qid in pt.target_specs() {
            if boogie_proven.contains(spec_qid) {
                continue;
            }
            // A spec reaching here is a DECLARED `prove` verification
            // target. Every miss below therefore drops an obligation
            // that someone asked for -- unlike the trusted map, whose
            // no-target skip may legitimately be a `#[spec_only]`
            // helper. Reported AND recorded: the stderr line is for
            // whoever is watching the render, the `unmapped` row is the
            // durable record the manifest discloses, and a line inside a
            // 25-minute gate log was never the second of those.
            let Some(&spec_fid) = self.function_id_map.get(spec_qid) else {
                if env.get_function(*spec_qid).module_env.is_target() {
                    eprintln!(
                        "new-pipeline: prove spec `{}` was never lifted to IR -- \
                         NO OBLIGATION EMITTED",
                        env.get_function(*spec_qid).get_full_name_str()
                    );
                    roster.unmapped.insert((
                        qualified(spec_qid, package_name_for_module),
                        "wrapper_not_translated".to_string(),
                    ));
                }
                continue;
            };
            roster
                .names
                .insert(spec_fid, qualified(spec_qid, package_name_for_module));
            let Some(impl_qid) = pt.find_target_spec(spec_qid) else {
                // A standalone lemma: no `target=`, so no impl to pair
                // with. Recorded rather than dropped -- stage 12 emits
                // `<spec>_correct` from the wrapper's OWN companions,
                // whose statement never mentions an impl.
                roster.targetless.insert(spec_fid);
                continue;
            };
            let Some(&impl_fid) = self.function_id_map.get(&impl_qid) else {
                if env.get_function(*spec_qid).module_env.is_target() {
                    eprintln!(
                        "new-pipeline: prove spec `{}` targets `{}`, which has no IR FunId -- \
                         NO OBLIGATION EMITTED",
                        env.get_function(*spec_qid).get_full_name_str(),
                        env.get_function(impl_qid).get_full_name_str()
                    );
                    roster.unmapped.insert((
                        qualified(spec_qid, package_name_for_module),
                        "target_not_translated".to_string(),
                    ));
                }
                continue;
            };
            roster.spec_to_impl.insert(spec_fid, impl_fid);
        }
        roster
    }

    /// Trusted-spec-wrapper -> impl `FunId` map: the specs whose
    /// statements the Lean pipeline ASSUMES (stage 12 emits their
    /// obligations as `FunctionKind::Axiom` -> Lean `axiom`) instead of
    /// proving. Two sources:
    ///
    /// - `no_verify_specs()`: `#[spec(target=...)]` without `prove` or
    ///   with `skip` (also, under upstream focus mode, every non-focused
    ///   target spec -- assuming those matches Boogie's focus semantics).
    /// - `boogie_backend_specs()`: `ext(backend = b"boogie")` specs --
    ///   proven on the Boogie side, so the Lean pipeline trusts them as
    ///   axioms. Their mirror `ext(backend = b"lean")` (proven only on the
    ///   Lean side; Boogie skips it upstream) is deliberately NOT trusted
    ///   here -- it falls through as a normal `prove` obligation, as does
    ///   `b"both"` and the no-attribute default (both of which resolve to
    ///   `SpecBackend::Both`). `backend` is single-valued, so the two
    ///   partition cleanly.
    ///
    /// Unlike [`Self::compute_spec_to_impl`], the impl side may be a
    /// NATIVE (e.g. a trusted spec on `std::string::utf8`) -- natives get
    /// qid-keyed `FunId`s at module lift, so the map lookup covers them.
    /// A trusted spec whose wrapper is untranslated or whose target has
    /// no IR `FunId` is reported to stderr (by name, via `env`) rather
    /// than silently dropped.
    pub(crate) fn compute_trusted_spec_to_impl(
        &self,
        env: &move_model::model::GlobalEnv,
        package_targets: Option<&move_stackless_bytecode::package_targets::PackageTargets>,
    ) -> BTreeMap<FunId, (FunId, crate::ir::TrustReason)> {
        let mut out = BTreeMap::new();
        let Some(pt) = package_targets else {
            return out;
        };
        let boogie_proven = pt.boogie_backend_specs();
        let trusted_qids: std::collections::BTreeSet<_> = pt
            .no_verify_specs()
            .iter()
            .chain(boogie_proven.iter())
            .copied()
            .collect();
        for (spec_qid, &spec_fid) in &self.function_id_map {
            if !trusted_qids.contains(spec_qid) {
                continue;
            }
            // Classification order matters: `ext(backend = b"boogie")` specs are
            // prove-specs (never in `no_verify_specs`), and a skipped
            // spec sits in both `no_verify_specs` and `skipped_specs`.
            let reason = if boogie_proven.contains(spec_qid) {
                crate::ir::TrustReason::Boogie
            } else if pt.skipped_specs().contains_key(spec_qid) {
                crate::ir::TrustReason::Skip
            } else {
                crate::ir::TrustReason::NonProve
            };
            let Some(impl_qid) = pt.find_target_spec(spec_qid) else {
                continue; // spec-only helper with no target -- nothing to axiomatize
            };
            if !self.program.functions.contains_key(&spec_fid) {
                // Only note untranslated wrappers from TARGET modules --
                // the client can act on those (the trusted-keep prune
                // exemption translates them unless analysis rejected the
                // wrapper). Dependency wrappers (prover intrinsics like
                // `prover::drop_spec`, framework specs) stay silent: they
                // translate only when reachability pulls them in, and
                // their semantics live in the hand-written natives.
                if env.get_function(*spec_qid).module_env.is_target() {
                    eprintln!(
                        "new-pipeline: trusted spec `{}` has no translated wrapper -- no axiom emitted",
                        env.get_function(*spec_qid).get_full_name_str()
                    );
                }
                continue;
            }
            match self.function_id_map.get(&impl_qid) {
                Some(&impl_fid) => {
                    out.insert(spec_fid, (impl_fid, reason));
                }
                None => {
                    eprintln!(
                        "new-pipeline: trusted spec `{}` targets a function with no IR FunId -- no axiom emitted",
                        env.get_function(*spec_qid).get_full_name_str()
                    );
                }
            }
        }
        out
    }

    pub(crate) fn compute_spec_ignore_aborts(
        &self,
        package_targets: Option<&move_stackless_bytecode::package_targets::PackageTargets>,
    ) -> BTreeMap<FunId, bool> {
        let mut out = BTreeMap::new();
        let Some(pt) = package_targets else {
            return out;
        };
        for spec_qid in pt.ignore_aborts() {
            if let Some(&spec_fid) = self.function_id_map.get(spec_qid) {
                out.insert(spec_fid, true);
            }
        }
        out
    }

    /// Derive the spec-only ghost markers each ghost-writing native
    /// threads, from the Move model -- the replacement for stage 4g's
    /// hand-coded `NATIVE_GHOST_WRITES` / `NATIVE_GHOST_READS` registries.
    ///
    /// A native threads a ghost iff its OWN spec declares one. For each
    /// referenced native, look up the spec(s) that target it via
    /// [`PackageTargets::get_specs`] -- the unfiltered `all_specs` built
    /// from `#[spec(target=...)]`, NOT the holder's `function_specs`
    /// bimap (which is filtered by the per-module `FunctionHolderTarget`
    /// and 1:1, so it silently drops framework-native specs like
    /// `transfer_impl_spec`; that is why `get_fun_by_spec` returns nothing
    /// for them). When a native has both a client spec and the framework
    /// (`SuiSpecs`) spec -- e.g. `share_object_impl`, which a client
    /// re-specs in its own package with its own marker structs -- the
    /// client's is preferred: its markers are the structs the client
    /// actually reads.
    ///
    /// The chosen spec's bytecode is walked for
    /// `ghost::{global,set,borrow_mut}<K,V>` ops; each `(K,V)` becomes a
    /// threaded ghost slot, translated to IR exactly as
    /// [`read_ghost_vars`](super::super::stage_02_ir_cfg) does for lifted
    /// functions. Natives whose spec declares no ghost are not seeded.
    pub(crate) fn derive_native_ghost_seed(
        &mut self,
        env: &move_model::model::GlobalEnv,
        package_targets: &move_stackless_bytecode::package_targets::PackageTargets,
        package_name_for_module: &mut dyn FnMut(MoveModuleId) -> String,
    ) -> Result<BTreeMap<FunId, Vec<(super::Type, super::Type)>>, crate::stage_02_ir_cfg::Stage2Error>
    {
        use move_stackless_bytecode::stackless_bytecode::{Bytecode, Operation};
        use move_stackless_bytecode::stackless_bytecode_generator::StacklessBytecodeGenerator;

        let ghost_op_qids = [
            env.global_qid(),
            env.global_set_qid(),
            env.global_borrow_mut_qid(),
        ];

        // The native FunIds referenced in this program, with their Move
        // qids. Collected up front so the `function_id_map` borrow is
        // released before Phase 2 allocates (translate_type) on `self`.
        let native_pairs: Vec<(QualifiedId<MoveFunId>, FunId)> = self
            .function_id_map
            .iter()
            .filter(|(_, fid)| self.program().natives.decls.contains_key(fid))
            .map(|(q, f)| (*q, *f))
            .collect();

        // Phase 1: per native, walk its chosen spec's bytecode for the
        // Move `(K, V)` ghost-op type instantiations. No `self` mutation.
        // Also capture the `transfer::{transfer,transfer_impl}` native FunIds
        // for the ghost-inheritance step after Phase 2 (see below).
        let mut transfer_fid: Option<FunId> = None;
        let mut transfer_impl_fid: Option<FunId> = None;
        let mut raw: Vec<(FunId, Vec<(move_model::ty::Type, move_model::ty::Type)>)> = Vec::new();
        for (native_qid, fid) in native_pairs {
            match env.get_function(native_qid).get_full_name_str().as_str() {
                "transfer::transfer" => transfer_fid = Some(fid),
                "transfer::transfer_impl" => transfer_impl_fid = Some(fid),
                _ => {}
            }
            // A native threads a ghost iff its OWN spec declares one.
            let specs = package_targets.get_specs(&native_qid).unwrap_or_default();
            if specs.is_empty() {
                continue;
            }
            // Prefer a client (non-`SuiSpecs`) spec; fall back to framework.
            let chosen = specs
                .iter()
                .find(|s| package_name_for_module(s.module_id) != "SuiSpecs")
                .or_else(|| specs.iter().next())
                .copied();
            let Some(chosen) = chosen else {
                continue;
            };
            // Generate the spec's raw stackless bytecode fresh from the
            // model -- NOT the holder's processed/filtered target, whose
            // `code` is emptied for specs outside the per-module re-add
            // closure (and whose ghost ops may have been lowered by
            // `SpecInstrumentation`). The raw form has the
            // `ghost::global<K,V>` calls intact, for any function.
            let spec_env = env.get_function(chosen);
            let data = StacklessBytecodeGenerator::new(&spec_env).generate_function();
            let mut pairs: Vec<(move_model::ty::Type, move_model::ty::Type)> = Vec::new();
            for bc in &data.code {
                if let Bytecode::Call(_, _, Operation::Function(mid, ofid, type_inst), _, _) = bc {
                    let callee = mid.qualified(*ofid);
                    // Concrete-struct markers only: the generic ghost
                    // intrinsics (`global<$tv0,$tv1>` in `Prover::ghost`)
                    // instantiate with type params, not a marker struct.
                    // Open value types are allowed here. Stage 4's ghost
                    // fixpoint instantiates the native's `(K, V)` pair at
                    // each call site, which is required for specs like
                    // `public_receive<T>` whose ghost value is the received
                    // `T`.
                    if ghost_op_qids.contains(&callee)
                        && type_inst.len() == 2
                        && matches!(type_inst[0], move_model::ty::Type::Datatype(..))
                    {
                        let kv = (type_inst[0].clone(), type_inst[1].clone());
                        if !pairs.contains(&kv) {
                            pairs.push(kv);
                        }
                    }
                }
            }
            if !pairs.is_empty() {
                raw.push((fid, pairs));
            }
        }

        // Phase 2: translate Move `(K, V)` -> IR (allocates struct ids on
        // `self`, now that the `function_id_map` borrow is released).
        let mut seed: BTreeMap<FunId, Vec<(super::Type, super::Type)>> = BTreeMap::new();
        for (fid, pairs) in raw {
            let mut markers: Vec<(super::Type, super::Type)> = Vec::with_capacity(pairs.len());
            for (k, v) in &pairs {
                let k_ir = crate::stage_02_ir_cfg::translate_type(k, self)?;
                let v_ir = crate::stage_02_ir_cfg::translate_type(v, self)?;
                markers.push((k_ir, v_ir));
            }
            seed.insert(fid, markers);
        }

        // `transfer::transfer` is a thin Move `public fun transfer(o, r) {
        // transfer_impl(o, r) }` that the pipeline models as a NATIVE
        // (hand-written `Transfer.transfer` / `Transfer.transfer__ghost`), so
        // -- unlike the LIFTED `public_transfer`, whose body reaches the
        // ghost-writing `transfer_impl` -- its opaque native body never does.
        // SuiSpecs only carries `transfer_impl_spec` (there is no
        // `transfer_spec`), so the loop above seeds `transfer_impl` but leaves
        // plain `transfer` un-threaded, and a ghost-publishing caller that uses
        // `transfer::transfer` (e.g. `staking_pool::split_staked_sui`) would
        // get FALSE transfer-ghost ensures. `transfer`'s native performs the
        // identical `World.transfer_to`, so inherit `transfer_impl`'s ghost
        // markers onto it; the renderer then routes ghost-threaded `transfer`
        // calls to the hand-written `Transfer.transfer__ghost` variant (same
        // wiring as `transfer_impl` -> `transfer_impl__ghost`). See
        // `plans/lean-pipeline/ghost-support.md`.
        if let (Some(tf), Some(tif)) = (transfer_fid, transfer_impl_fid) {
            if let Some(markers) = seed.get(&tif).cloned() {
                seed.entry(tf).or_insert(markers);
            }
        }
        Ok(seed)
    }

    /// Get-or-allocate a deterministic [`ModId`] for a Move module.
    pub fn module_id(&mut self, mid: MoveModuleId) -> ModId {
        if let Some(&id) = self.module_id_map.get(&mid) {
            return id;
        }
        let id = self.alloc_module_id();
        self.module_id_map.insert(mid, id);
        id
    }

    /// Get or allocate the deterministic [`GlobalId`] for a frontend global
    /// symbol. The caller must complete the declaration with
    /// [`Self::insert_global`] before the ID is referenced by an expression.
    pub fn global_id(&mut self, symbol: &str) -> GlobalId {
        if let Some(&id) = self.global_id_map.get(symbol) {
            return id;
        }
        let id = self.alloc_global_id();
        self.global_id_map.insert(symbol.to_string(), id);
        id
    }

    /// True iff `qid` has been registered (id allocated).
    pub fn has_struct(&self, qid: &QualifiedId<DatatypeId>) -> bool {
        self.struct_id_map.contains_key(qid)
    }

    /// True iff `qid` has been registered (id allocated).
    pub fn has_function(&self, qid: &QualifiedId<MoveFunId>) -> bool {
        self.function_id_map.contains_key(qid)
    }

    /// True iff `mid` has been registered (id allocated).
    pub fn has_module(&self, mid: &MoveModuleId) -> bool {
        self.module_id_map.contains_key(mid)
    }

    /// Insert (or overwrite) the [`Struct`] for `id`. The id must have
    /// been previously allocated via [`Self::struct_id`].
    ///
    /// Panics if `id` was not allocated.
    pub fn insert_struct(&mut self, id: StructId, s: Struct) {
        assert!(
            id < self.next_struct_id,
            "ProgramBuilder::insert_struct: StructId {id} not allocated (next={})",
            self.next_struct_id
        );
        self.program.structs.insert(id, s);
    }

    /// Insert (or overwrite) the [`Function`] for `id`. The id must
    /// have been previously allocated via [`Self::function_id`].
    ///
    /// Panics if `id` was not allocated.
    pub fn insert_function(&mut self, id: FunId, f: Function) {
        assert!(
            id < self.next_function_id,
            "ProgramBuilder::insert_function: FunId {id} not allocated (next={})",
            self.next_function_id
        );
        self.program.functions.insert(id, f);
    }

    /// Insert (or overwrite) the [`crate::ir::NativeDecl`] for `id`.
    /// The id must have been previously allocated via
    /// [`Self::function_id`] or [`Self::synthetic_function_id`].
    ///
    /// Used by `module_lift`'s native-declaration pass and by
    /// stage-2's `dynamic_fields::register_typed_map_natives`. Stage
    /// 8 / stage 10 talk to `program.natives.decls` directly because
    /// they operate on `&mut Program`, not `&mut ProgramBuilder`.
    ///
    /// Panics if `id` was not allocated.
    pub fn insert_native(&mut self, id: FunId, d: crate::ir::NativeDecl) {
        assert!(
            id < self.next_function_id,
            "ProgramBuilder::insert_native: FunId {id} not allocated (next={})",
            self.next_function_id
        );
        self.program.natives.decls.insert(id, d);
    }

    /// Insert (or overwrite) the [`Module`] for `id`. The id must have
    /// been previously allocated via [`Self::module_id`].
    ///
    /// Panics if `id` was not allocated.
    pub fn insert_module(&mut self, id: ModId, m: Module) {
        assert!(
            id < self.next_module_id,
            "ProgramBuilder::insert_module: ModId {id} not allocated (next={})",
            self.next_module_id
        );
        self.program.modules.insert(id, m);
    }

    /// Insert or replace the global declaration for an ID previously
    /// allocated by [`Self::global_id`].
    pub fn insert_global(&mut self, id: GlobalId, global: Global) {
        assert!(
            id < self.next_global_id,
            "ProgramBuilder::insert_global: GlobalId {id} not allocated (next={})",
            self.next_global_id
        );
        self.program.globals.insert(id, global);
    }

    /// Read-only view of the partially-assembled `Program`. Useful for
    /// stage-2 sub-passes that need to inspect previously-translated
    /// structs while translating a function body.
    pub fn program(&self) -> &Program {
        &self.program
    }

    /// Mutable view of the partially-assembled `Program`. Stage 2's
    /// pre-passes (ghost dynamic-field augmentation, effects rewriting)
    /// need this; ordinary callers should use [`Self::insert_struct`]
    /// / [`Self::insert_function`] / [`Self::insert_module`] instead.
    pub fn program_mut(&mut self) -> &mut Program {
        &mut self.program
    }

    /// Get-or-allocate a synthetic [`ModId`] for a prelude-only
    /// module (e.g. `"Prelude"`). Distinct namespace from
    /// upstream Move modules: a `synthetic_module_id("Prelude")`
    /// never collides with a user-defined module called `Prelude`
    /// (which would have a Move qid).
    pub fn synthetic_module_id(&mut self, label: &str) -> ModId {
        if let Some(&id) = self.synthetic_module_ids.get(label) {
            return id;
        }
        let id = self.alloc_module_id();
        self.synthetic_module_ids.insert(label.to_string(), id);
        id
    }

    /// Get-or-allocate a synthetic [`StructId`] for a prelude-only
    /// struct (e.g. `"TypedMap"`). Inserts a stub `Struct` entry
    /// like [`Self::struct_id`] does for upstream structs; the
    /// pre-pass that allocates is expected to fill in the real
    /// definition via [`Self::insert_struct`].
    pub fn synthetic_struct_id(&mut self, label: &str) -> StructId {
        if let Some(&id) = self.synthetic_struct_ids.get(label) {
            return id;
        }
        let id = self.alloc_struct_id();
        self.synthetic_struct_ids.insert(label.to_string(), id);
        // Stub matches `struct_id`'s convention: empty fields, no
        // module set yet (caller fills via insert_struct).
        self.program.structs.insert(
            id,
            Struct {
                module_id: 0,
                name: String::new(),
                qualified_name: String::new(),
                type_params: Vec::new(),
                fields: Vec::new(),
                variants: None,
                is_native: false,
            },
        );
        id
    }

    /// Get-or-allocate a synthetic [`FunId`] for a prelude-only
    /// function (e.g. `"TypedMap.get"`). No stub is inserted (matches
    /// [`Self::function_id`]); the caller registers the function
    /// stub via [`Self::insert_function`].
    pub fn synthetic_function_id(&mut self, label: &str) -> FunId {
        if let Some(&id) = self.synthetic_function_ids.get(label) {
            return id;
        }
        let id = self.alloc_function_id();
        self.synthetic_function_ids.insert(label.to_string(), id);
        id
    }

    /// Idempotently register a pipeline-synthesised native (no
    /// upstream Move source) addressable by `label`. Mirrors
    /// [`crate::ir::Program::insert_synthetic_native`] but uses the
    /// builder's label-keyed [`Self::synthetic_function_id`] map for
    /// O(1) idempotency instead of a linear scan over
    /// `natives.decls`.
    ///
    /// On first call, allocates a fresh `FunId`, inserts a
    /// [`crate::ir::NativeDecl`] constructed from `signature` +
    /// `opts`, and returns the id. Subsequent calls with the same
    /// label short-circuit to the stored id without rebuilding the
    /// decl.
    pub fn insert_synthetic_native(
        &mut self,
        label: &str,
        signature: crate::ir::Signature,
        opts: crate::ir::SyntheticNativeOpts,
    ) -> FunId {
        let fid = self.synthetic_function_id(label);
        if !self.program.natives.decls.contains_key(&fid) {
            self.program
                .natives
                .decls
                .insert(fid, opts.into_decl(label, signature));
        }
        fid
    }

    /// Record the `FunId` of a `prover::*` intrinsic. `kind`
    /// selects which slot is set. Idempotent: calling twice with the
    /// same kind + id is a no-op; calling with the same kind but a
    /// different id panics (would mean the same intrinsic resolved
    /// to two different ids).
    pub(crate) fn register_prover_fn(&mut self, kind: ProverFnKind, fid: FunId) {
        let slot = match kind {
            ProverFnKind::Requires => &mut self.prover_fn_ids.requires,
            ProverFnKind::Ensures => &mut self.prover_fn_ids.ensures,
            ProverFnKind::Asserts => &mut self.prover_fn_ids.asserts,
        };
        match *slot {
            None => *slot = Some(fid),
            Some(existing) if existing == fid => {}
            Some(existing) => panic!(
                "ProgramBuilder::register_prover_fn: {kind:?} already registered as {existing}, \
                 cannot re-register as {fid}"
            ),
        }
    }

    /// Read-only view of the recorded `prover::*` intrinsic ids.
    pub(crate) fn prover_fn_ids(&self) -> &ProverFnIds {
        &self.prover_fn_ids
    }

    /// Consume the builder and return the assembled `Program` plus
    /// the recorded `prover::*` intrinsic ids.
    pub(crate) fn build_with_prover_ids(self) -> (Program, ProverFnIds) {
        (self.program, self.prover_fn_ids)
    }

    /// Consume the builder and return the assembled `Program`.
    pub fn build(self) -> Program {
        self.program
    }
}

impl Default for ProgramBuilder {
    fn default() -> Self {
        Self::new()
    }
}

// ---------------------------------------------------------------------------
// Builder smoke tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::GlobalDefinition;

    #[test]
    fn var_builds_var_with_interned_name() {
        match var("x") {
            Expr::Var(v) => assert_eq!(&*v, "x"),
            other => panic!("expected Var, got {other:?}"),
        }
    }

    #[test]
    fn lit_u64_has_64_bit_width() {
        match lit_u64(42) {
            Expr::Const(Const::UInt { bits: 64, value }) => {
                assert_eq!(value, U256::from(42u64));
            }
            other => panic!("expected u64 const, got {other:?}"),
        }
    }

    #[test]
    fn just_builds_empty_stmts_value_tail() {
        let b = just(unit());
        assert!(b.stmts.is_empty());
        assert_eq!(b.tail, BlockTail::Value(Expr::Unit));
    }

    #[test]
    fn global_ids_are_stable_and_declarations_are_inserted() {
        let mut builder = ProgramBuilder::new();
        let counter = builder.global_id("counter");
        assert_eq!(counter, builder.global_id("counter"));
        assert_eq!(builder.global_id("limit"), counter + 1);
        builder.insert_global(
            counter,
            Global {
                module_id: 0,
                name: "counter".into(),
                ty: Type::UInt(32),
                mutable: true,
                definition: GlobalDefinition::BoundarySupplied,
            },
        );
        let program = builder.build();
        assert_eq!(program.globals[&counter].name, "counter");
    }

    #[test]
    fn push_let_appends_let_stmt() {
        let mut b = just(unit());
        b.push_let(vec!["x"], lit_u64(1));
        assert_eq!(b.stmts.len(), 1);
        match &b.stmts[0] {
            Stmt::Let { pattern, value } => {
                assert_eq!(pattern.len(), 1);
                let v = pattern[0].as_ref().expect("expected Some binding");
                assert_eq!(&**v, "x");
                assert_eq!(value, &lit_u64(1));
            }
            other => panic!("expected Let, got {other:?}"),
        }
    }

    #[test]
    fn push_eval_appends_eval_stmt() {
        let mut b = just(unit());
        b.push_eval(lit_bool(true));
        assert_eq!(b.stmts.len(), 1);
        assert_eq!(b.stmts[0], Stmt::Eval(lit_bool(true)));
    }

    #[test]
    #[should_panic(expected = "empty pattern")]
    fn let_stmt_rejects_empty_pattern() {
        let _ = let_stmt(&[], unit());
    }

    #[test]
    #[should_panic(expected = "empty pattern")]
    fn push_let_rejects_empty_pattern() {
        let mut b = just(unit());
        b.push_let::<&str>(vec![], unit());
    }

    #[test]
    fn tails_carry_their_payloads() {
        assert_eq!(tail_value(unit()), BlockTail::Value(Expr::Unit));
        assert_eq!(
            tail_break(2, lit_u64(7)),
            BlockTail::Break {
                level: 2,
                value: Box::new(lit_u64(7))
            }
        );
        assert_eq!(
            tail_continue(0, unit()),
            BlockTail::Continue {
                level: 0,
                value: Box::new(Expr::Unit)
            }
        );
        assert_eq!(
            tail_return(lit_u64(1)),
            BlockTail::Return(Box::new(lit_u64(1)))
        );
        assert_eq!(
            tail_abort(lit_u64(7)),
            BlockTail::Abort {
                code: Box::new(lit_u64(7))
            }
        );
    }

    // ---- ProgramBuilder ------------------------------------------------

    use move_model::model::{
        DatatypeId, FunId as MoveFunId, ModuleId as MoveModuleId, QualifiedId,
    };
    use move_model::symbol::SymbolPool;

    fn pool() -> SymbolPool {
        SymbolPool::new()
    }

    fn module_id(raw: usize) -> MoveModuleId {
        MoveModuleId::new(raw)
    }

    fn struct_qid(p: &SymbolPool, m: usize, name: &str) -> QualifiedId<DatatypeId> {
        QualifiedId {
            module_id: module_id(m),
            id: DatatypeId::new(p.make(name)),
        }
    }

    fn function_qid(p: &SymbolPool, m: usize, name: &str) -> QualifiedId<MoveFunId> {
        QualifiedId {
            module_id: module_id(m),
            id: MoveFunId::new(p.make(name)),
        }
    }

    fn empty_module() -> Module {
        Module {
            name: String::new(),
            package_name: String::new(),
            address: String::new(),
            required_imports: Vec::new(),
            is_native: false,
        }
    }

    #[test]
    fn program_builder_starts_empty() {
        let pb = ProgramBuilder::new();
        assert!(pb.program().modules.is_empty());
        assert!(pb.program().structs.is_empty());
        assert!(pb.program().functions.is_empty());
    }

    #[test]
    fn program_builder_module_id_is_idempotent() {
        let mut pb = ProgramBuilder::new();
        let id1 = pb.module_id(module_id(0));
        let id2 = pb.module_id(module_id(0));
        assert_eq!(id1, id2);
        // Different Move module ids get different IR ids.
        let id3 = pb.module_id(module_id(1));
        assert_ne!(id1, id3);
    }

    #[test]
    fn program_builder_module_ids_are_monotonic_from_zero() {
        let mut pb = ProgramBuilder::new();
        assert_eq!(pb.module_id(module_id(7)), 0);
        assert_eq!(pb.module_id(module_id(2)), 1);
        assert_eq!(pb.module_id(module_id(99)), 2);
    }

    #[test]
    fn program_builder_struct_id_inserts_stub() {
        let mut pb = ProgramBuilder::new();
        let pool = pool();
        let qid = struct_qid(&pool, 0, "Pool");

        let id = pb.struct_id(qid);
        assert_eq!(id, 0);
        let stub = pb
            .program()
            .structs
            .get(&id)
            .expect("stub should be inserted");
        assert!(stub.fields.is_empty());
        assert!(stub.variants.is_none());
    }

    #[test]
    fn program_builder_function_id_does_not_insert_stub() {
        let mut pb = ProgramBuilder::new();
        let pool = pool();
        let qid = function_qid(&pool, 0, "swap");

        let id = pb.function_id(qid);
        assert_eq!(id, 0);
        // Function-id allocation does NOT auto-insert; caller must
        // insert_function before any Call references it.
        assert!(!pb.program().functions.contains_key(&id));
    }

    #[test]
    fn program_builder_function_ids_are_idempotent() {
        let mut pb = ProgramBuilder::new();
        let pool = pool();
        let qid = function_qid(&pool, 0, "swap");

        let id1 = pb.function_id(qid);
        let id2 = pb.function_id(qid);
        assert_eq!(id1, id2);
    }

    #[test]
    fn program_builder_insert_module_round_trips() {
        let mut pb = ProgramBuilder::new();
        let id = pb.module_id(module_id(0));
        pb.insert_module(
            id,
            Module {
                name: "math".to_string(),
                package_name: "MyProject".to_string(),
                address: String::new(),
                required_imports: Vec::new(),
                is_native: false,
            },
        );
        let p = pb.build();
        let m = p.modules.get(&id).expect("module should be present");
        assert_eq!(m.name, "math");
        assert_eq!(m.package_name, "MyProject");
    }

    #[test]
    #[should_panic(expected = "StructId 5 not allocated")]
    fn program_builder_insert_struct_rejects_unallocated_id() {
        let mut pb = ProgramBuilder::new();
        pb.insert_struct(
            5,
            Struct {
                module_id: 0,
                name: String::new(),
                qualified_name: String::new(),
                type_params: Vec::new(),
                fields: Vec::new(),
                variants: None,
                is_native: false,
            },
        );
    }

    #[test]
    #[should_panic(expected = "FunId 3 not allocated")]
    fn program_builder_insert_function_rejects_unallocated_id() {
        let mut pb = ProgramBuilder::new();
        pb.insert_function(
            3,
            Function {
                module: 0,
                name: String::new(),
                signature: super::super::function::Signature {
                    type_params: Vec::new(),
                    params: Vec::new(),
                    return_type: super::super::ty::Type::Unit,
                },
                body: Block {
                    stmts: Vec::new(),
                    tail: BlockTail::Value(Expr::Unit),
                },
                kind: super::super::function::FunctionKind::Source,
                effects: crate::ir::Effects::PURE,
                explicit_pure: false,
            },
        );
    }

    #[test]
    #[should_panic(expected = "ModId 1 not allocated")]
    fn program_builder_insert_module_rejects_unallocated_id() {
        let mut pb = ProgramBuilder::new();
        pb.insert_module(1, empty_module());
    }

    #[test]
    fn program_builder_has_methods() {
        let mut pb = ProgramBuilder::new();
        let pool = pool();
        let s = struct_qid(&pool, 0, "Pool");
        let f = function_qid(&pool, 0, "swap");
        let m = module_id(0);

        assert!(!pb.has_struct(&s));
        assert!(!pb.has_function(&f));
        assert!(!pb.has_module(&m));

        pb.struct_id(s);
        pb.function_id(f);
        // module_id was allocated transitively by struct_id.

        assert!(pb.has_struct(&s));
        assert!(pb.has_function(&f));
        assert!(pb.has_module(&m));
    }

    #[test]
    fn program_builder_struct_id_allocates_module_transitively() {
        // Allocating a struct id for a struct in module 7 (Move id)
        // must allocate an IR module id for that module too -- the
        // stub Struct's module field has to point somewhere valid.
        let mut pb = ProgramBuilder::new();
        let pool = pool();
        let qid = struct_qid(&pool, 7, "Pool");
        let sid = pb.struct_id(qid);
        assert!(pb.has_module(&module_id(7)));
        let mid = pb.program().structs.get(&sid).unwrap().module_id;
        assert_eq!(mid, pb.module_id(module_id(7)));
    }

    #[test]
    fn program_builder_deterministic_across_runs() {
        // Same sequence of allocations -> identical Program.
        let pool = pool();
        let qid_a = struct_qid(&pool, 0, "A");
        let qid_b = struct_qid(&pool, 1, "B");
        let qid_f = function_qid(&pool, 0, "f");

        let build_one = || {
            let mut pb = ProgramBuilder::new();
            let _ = pb.struct_id(qid_a);
            let _ = pb.struct_id(qid_b);
            let _ = pb.function_id(qid_f);
            pb.insert_module(0, empty_module());
            pb.insert_module(1, empty_module());
            pb.build()
        };
        let p1 = build_one();
        let p2 = build_one();
        assert_eq!(p1, p2);
    }

    // ---- ProverFnIds + register_prover_fn -----------------------------

    #[test]
    fn fresh_builder_has_no_prover_fn_ids() {
        let pb = ProgramBuilder::new();
        assert_eq!(pb.prover_fn_ids(), &ProverFnIds::default());
    }

    #[test]
    fn register_prover_fn_each_slot_independently() {
        let mut pb = ProgramBuilder::new();
        let pool = pool();
        let r = pb.function_id(function_qid(&pool, 0, "requires"));
        let e = pb.function_id(function_qid(&pool, 0, "ensures"));
        let a = pb.function_id(function_qid(&pool, 0, "asserts"));
        pb.register_prover_fn(ProverFnKind::Requires, r);
        pb.register_prover_fn(ProverFnKind::Ensures, e);
        pb.register_prover_fn(ProverFnKind::Asserts, a);
        let ids = pb.prover_fn_ids();
        assert_eq!(ids.requires, Some(r));
        assert_eq!(ids.ensures, Some(e));
        assert_eq!(ids.asserts, Some(a));
    }

    #[test]
    fn register_prover_fn_is_idempotent_for_same_id() {
        let mut pb = ProgramBuilder::new();
        let pool = pool();
        let r = pb.function_id(function_qid(&pool, 0, "requires"));
        pb.register_prover_fn(ProverFnKind::Requires, r);
        pb.register_prover_fn(ProverFnKind::Requires, r); // no-op
        assert_eq!(pb.prover_fn_ids().requires, Some(r));
    }

    #[test]
    #[should_panic(expected = "already registered")]
    fn register_prover_fn_rejects_conflicting_id() {
        let mut pb = ProgramBuilder::new();
        let pool = pool();
        let r1 = pb.function_id(function_qid(&pool, 0, "requires"));
        let r2 = pb.function_id(function_qid(&pool, 1, "requires"));
        pb.register_prover_fn(ProverFnKind::Requires, r1);
        pb.register_prover_fn(ProverFnKind::Requires, r2);
    }

    // ---- synthetic id allocation -----------------------------------

    #[test]
    fn synthetic_module_id_is_idempotent() {
        let mut pb = ProgramBuilder::new();
        let a = pb.synthetic_module_id("Prelude");
        let b = pb.synthetic_module_id("Prelude");
        assert_eq!(a, b);
        let c = pb.synthetic_module_id("Other");
        assert_ne!(a, c);
    }

    #[test]
    fn synthetic_struct_id_inserts_stub() {
        let mut pb = ProgramBuilder::new();
        let id = pb.synthetic_struct_id("TypedMap");
        assert!(pb.program().structs.contains_key(&id));
    }

    #[test]
    fn synthetic_function_id_does_not_insert_stub() {
        let mut pb = ProgramBuilder::new();
        let id = pb.synthetic_function_id("TypedMap.get");
        // function ids do not auto-insert; caller is expected to
        // insert_function before any Call references the id.
        assert!(!pb.program().functions.contains_key(&id));
    }

    #[test]
    fn synthetic_namespaces_share_id_counters_with_qid_path() {
        // Both synthetic and qid-keyed allocation use the same monotonic
        // counter, so ids never collide.
        let mut pb = ProgramBuilder::new();
        let pool = pool();
        let qid = struct_qid(&pool, 0, "Pool");
        let qid_id = pb.struct_id(qid);
        let synth_id = pb.synthetic_struct_id("TypedMap");
        assert_ne!(qid_id, synth_id);
    }

    #[test]
    fn build_with_prover_ids_returns_both() {
        let mut pb = ProgramBuilder::new();
        let pool = pool();
        let r = pb.function_id(function_qid(&pool, 0, "requires"));
        pb.register_prover_fn(ProverFnKind::Requires, r);
        let (program, ids) = pb.build_with_prover_ids();
        assert!(program.functions.is_empty()); // no insert_function called
        assert_eq!(ids.requires, Some(r));
        assert_eq!(ids.ensures, None);
        assert_eq!(ids.asserts, None);
    }
}
