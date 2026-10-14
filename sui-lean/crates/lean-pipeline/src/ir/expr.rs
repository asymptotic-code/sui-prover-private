//! Expressions, blocks, statements, block tails.
//!
//! See `plans/lean-pipeline/ir.md` "Block + Stmt + BlockTail" and "Expr"
//! sections. The IR follows a do-block style: `Block` is a sequence of
//! `Stmt`s ending in a `BlockTail`. Control-flow terminators
//! (`Break` / `Continue` / `Return` / `Abort`) are `BlockTail` variants
//! and **not** `Expr` variants -- the type system enforces tail-position-only.

use super::borrow::{BorrowEdge, BorrowNode};
use super::ops::{BinOp, BitOp, UnOp};
use super::quant::{QuantDomain, QuantifierKind};
use super::ty::{Const, Type};
use super::{FunId, GlobalId, StructId, VarId};

/// A do-block: a sequence of statements terminated by a `BlockTail`.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Block {
    pub stmts: Vec<Stmt>,
    pub tail: BlockTail,
}

/// A statement inside a `Block`.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Stmt {
    /// `let pat := value`. `pattern[i] == None` is the wildcard
    /// (rendered as `_` in Lean) -- the position is bound but discarded.
    /// Pattern must contain at least one `Some` (validator); a Let with
    /// every position discarded should be a `Stmt::Eval` instead.
    Let {
        pattern: Vec<Option<VarId>>,
        value: Expr,
    },
    /// Evaluate `Expr` for its side effect; drop the value.
    Eval(Expr),
}

/// The tail of a `Block`. Either a value-producing expression or one of
/// the four control-flow terminators. Stages 6 / 7 eliminate the
/// terminator variants from main bodies.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum BlockTail {
    /// The block's value is the wrapped expression.
    Value(Expr),
    /// Break out of the `level`-th enclosing loop, carrying `value`.
    /// `level = 0` is the innermost loop. Eliminated by stage 6.
    Break { level: u32, value: Box<Expr> },
    /// Continue the `level`-th enclosing loop, carrying `value` as the
    /// next iteration's induction state. Eliminated by stage 6.
    Continue { level: u32, value: Box<Expr> },
    /// Return from the enclosing function with `value`.
    /// Eliminated by stage 6.
    Return(Box<Expr>),
    /// Return from the `level`-th enclosing `Expr::LabeledBlock`,
    /// carrying `value`. `level = 0` is the innermost LabeledBlock.
    /// Independent from `Break`/`Continue` -- those count loops,
    /// this counts labeled blocks. Eliminated by stage 7's labeled-
    /// block helper extraction. See `plans/lean-pipeline/labeled-block-ir.md`.
    ReturnFromBlock { level: u32, value: Box<Expr> },
    /// Abort with the given code. In main-function bodies, lifted into
    /// the `.aborts` companion by stage 6. Survives in `.aborts`
    /// companion bodies until the renderer.
    Abort { code: Box<Expr> },
}

/// An IR expression. Value-producing only -- control-flow terminators
/// live on `BlockTail`, not here.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Expr {
    // ---- Atoms ----
    Var(VarId),
    Const(Const),
    /// `()`.
    Unit,

    // ---- Compound ----
    BinOp {
        op: BinOp,
        lhs: Box<Expr>,
        rhs: Box<Expr>,
    },
    UnOp {
        op: UnOp,
        operand: Box<Expr>,
    },
    BitOp(BitOp),
    Call {
        fun: FunId,
        type_args: Vec<Type>,
        args: Vec<Expr>,
    },
    Tuple(Vec<Expr>),

    // ---- Struct / enum ----
    Pack {
        struct_id: StructId,
        type_args: Vec<Type>,
        /// `Some(tag)` for an enum's declared variant tag; `None` for a plain struct.
        variant: Option<usize>,
        fields: Vec<Expr>,
    },
    Unpack {
        struct_id: StructId,
        /// `Some(tag)` for an enum's declared variant tag; `None` for a plain struct.
        variant: Option<usize>,
        value: Box<Expr>,
    },
    Field {
        struct_id: StructId,
        field_index: usize,
        base: Box<Expr>,
    },

    // ---- Branching (arms are Blocks) ----
    If {
        cond: Box<Expr>,
        then_branch: Box<Block>,
        else_branch: Box<Block>,
    },
    Match {
        /// The struct (enum) whose variants this match discriminates
        /// over. Used by the renderer to resolve `MatchArm::variant`
        /// tags to their declared variant names.
        struct_id: StructId,
        selector: Box<Expr>,
        cases: Vec<MatchArm>,
    },

    // ---- Loops -- eliminated by stage 7 ----
    /// Move-style `while` loop.
    ///
    /// - `header` is re-evaluated every iteration **before** `cond`
    ///   is checked. Holds the bytecodes that compute the cond
    ///   expression (Move's `while ({ pre(); cond_check() }) body`
    ///   gets a clean home here). May be empty. The validator
    ///   enforces `header.tail == BlockTail::Value(Expr::Unit)`.
    /// - `cond` is the loop predicate, unambiguously a Bool
    ///   expression -- no implicit "tail must be Value(Bool)"
    ///   invariant.
    /// - `body`'s tail is typically `BlockTail::Continue { level: 0, .. }`
    ///   (loop iteration) or `BlockTail::Break { level: 0, .. }` (early
    ///   exit). May be empty.
    ///
    /// See `plans/lean-pipeline/ir.md` decision-log §17.
    ///
    /// `iter_locals` are the iteration-local binders introduced by
    /// stage 5's SSA pass: one fresh `VarId` per `loop_state` var,
    /// paired with the **initial-value expression** evaluated once
    /// in the outer scope at loop entry. Each binder is in scope for
    /// `header`, `cond`, and `body`; each `init` expression is
    /// evaluated in the surrounding scope (before the binder is in
    /// scope). Stages 1-4 emit `iter_locals: vec![]`; stage 5
    /// populates it; stage 7 reads it to lower the `While` into a
    /// recursive `LoopBody` helper call whose arguments are the
    /// `init` expressions.
    While {
        header: Box<Block>,
        cond: Box<Expr>,
        body: Box<Block>,
        iter_locals: Vec<(VarId, Expr)>,
        /// Current SSA value of each `iter_locals` slot after the
        /// per-iteration `header` has executed, in the same positional
        /// order as `iter_locals`. Stage 5 records these names so stage 7's
        /// condition-false edge can call `LoopAfter` with the state produced
        /// by the header rather than the iteration-entry binders. Stages 1-4
        /// emit an empty vector; stage 5 requires equal arity with
        /// `iter_locals`.
        header_exit_locals: Vec<VarId>,
        /// Loop **live-out** binders: vars defined inside the loop
        /// (typically the structured loop `header`) that are NOT
        /// loop-carried (`iter_locals`) yet are referenced AFTER the
        /// loop. Each pair is `(loop_internal_ssa_name,
        /// post_loop_name)`: the first is the in-loop SSA name whose
        /// final-iteration value escapes (looked up in the body/header
        /// scope at the cond-false exit); the second is the fresh
        /// post-loop name stage 5 appends to the surrounding
        /// `Stmt::Let` pattern so post-loop references resolve under
        /// the strictly-scoped validator. Stage 5 populates this;
        /// stage 7 threads each live-out as an extra `LoopAfter` param
        /// (named by the post-loop name) plus an extra exit-call arg
        /// (the loop-internal name, in scope at the `.after` call).
        /// A carried-slot override is NOT recorded here -- that lives in
        /// `header_exit_locals` -- so every destination is a fresh
        /// post-loop name. Empty for ordinary loops whose result is fully
        /// captured by `iter_locals`. Stages 1-4 emit `live_out: vec![]`.
        live_out: Vec<(VarId, VarId)>,
    },

    // ---- Borrow operations (1:1 with upstream `Operation::*`) -----
    // Stage 2 emits these from matching bytecode operations without
    // resolving borrow chains. The active mutation-to-let and writeback
    // passes lower them in program order.
    /// `&x` / `&mut x` -- mirrors `Operation::BorrowLoc dests=[$tN] srcs=[$tM]`.
    BorrowLoc(VarId),
    /// Borrow the storage of a first-class program global.
    ///
    /// The declaration and its pointee type are resolved through
    /// `Program::globals`. A writeback to the root uses the matching
    /// [`BorrowNode::GlobalRoot`] ID. External-memory frontends may construct
    /// this node only after their schema/identity and borrow-exclusivity
    /// checks succeed, and must then set
    /// `Program::external_global_borrows_certified`; global threading rejects
    /// executable nodes without that trusted assertion.
    BorrowGlobal(GlobalId),
    /// Unified container borrow: one [`super::path::PathStep`]
    /// projection off `base` (struct field, vector index, or map key
    /// -- see `PathStep` for the per-step semantics, including the
    /// World-supplied `df_value` on MapKey df borrows). See
    /// `plans/lean-pipeline/container-df-unification.md` step 4.
    Borrow {
        step: super::path::PathStep,
        base: Box<Expr>,
    },
    /// Unified value-form container update: replace the slot named by
    /// `step` inside `base` with `value`. Step-4 replacement for
    /// `UpdateField` / `UpdateVec`, and the first value-form update
    /// for `MapKey` steps (the in-value map `set`).
    Update {
        step: super::path::PathStep,
        base: Box<Expr>,
        value: Box<Expr>,
    },
    ReadRef(Box<Expr>),
    WriteRef {
        reference: Box<Expr>,
        value: Box<Expr>,
    },
    /// Mirrors `Operation::WriteBack(BorrowNode, BorrowEdge) srcs=[child]`.
    /// `child` is the borrow temp being written back; `node` and
    /// `edge` carry the upstream-recorded path back to the parent.
    WriteBack {
        node: BorrowNode,
        edge: BorrowEdge,
        child: VarId,
        /// `Some(world_var)` marks this as a DYNAMIC-FIELD writeback that
        /// stores into `World` rather than the object value (the object is
        /// unchanged; only `World.df[_bag]_entries` changes). Set by
        /// stage-4, which threads `world` through it exactly like a
        /// world-returning call: the enclosing `let` pattern gains a
        /// trailing `world` slot and the renderer emits a
        /// `store_(bag_)set` that consumes+reproduces `world`. `None` for
        /// ordinary value writebacks (struct field / vec / in-value map).
        world: Option<VarId>,
    },
    /// Mirrors `Operation::IsParent(BorrowNode, BorrowEdge) srcs=[child]`.
    /// Returns `Bool` at the IR level; renderer emits `Mutation.isParent`.
    /// Used by upstream's conditional-borrow dispatch (`memory_instrumentation.rs`)
    /// to pick which writeback chain fires when a single borrow temp has
    /// multiple possible parents.
    IsParent {
        node: BorrowNode,
        edge: BorrowEdge,
        child: VarId,
    },

    // ---- Coercions ----
    /// Bool -> Prop. Renders as `expr = true` in Lean.
    ToProp(Box<Expr>),
    /// Prop -> Bool. Renders as `decide expr` in Lean (requires Decidable).
    ToBool(Box<Expr>),

    // ---- Labeled scope -- eliminated by stage 7 ----
    /// Labeled scope with multiple exits. `body` may contain
    /// `BlockTail::ReturnFromBlock { level: 0, value }` to return
    /// from this LabeledBlock with `value`. The block's natural-tail
    /// `Value(_)` is the fallthrough exit. Every exit (natural and
    /// labeled) must produce a value whose type matches `result_ty`.
    ///
    /// Stage 01 recovers this from a CFG pattern (multiple Jumps to a
    /// single non-loop post-dominator). Stage 02 lifts it. Stage 07
    /// extracts every LabeledBlock with a non-trivial body to a
    /// `labeled_N` helper, so the renderer never sees a surviving
    /// `Expr::LabeledBlock`.
    ///
    /// See `plans/lean-pipeline/labeled-block-ir.md`.
    LabeledBlock {
        body: Box<Block>,
        result_ty: Type,
    },

    // ---- Quantifiers (Move spec macros) ----
    Quantifier {
        kind: QuantifierKind,
        binder: VarId,
        binder_type: Type,
        domain: QuantDomain,
        /// Body must have a `BlockTail::Value` tail (validator enforces).
        body: Box<Block>,
    },
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct MatchArm {
    /// The declared tag of the enum variant matched by this arm.
    pub variant: usize,
    pub bindings: Vec<VarId>,
    pub body: Box<Block>,
}
