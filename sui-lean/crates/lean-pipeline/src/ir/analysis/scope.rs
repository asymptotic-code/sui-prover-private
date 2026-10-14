//! Scope-tracking traversal (set flavor).
//!
//! One walker that owns the IR's binding discipline -- which sites
//! introduce names, and for which sub-tree -- so the analyses that
//! need "is this var bound by an enclosing binder?" don't each
//! re-encode it. A [`ScopeObserver`] is called for every variable
//! USE with a flag saying whether it resolves to an in-scope binder;
//! the walker handles the binding sites and snapshot/restore.
//!
//! Consumers: `free_vars` (records uses that are NOT in scope),
//! and -- as they migrate -- `validate`'s unbound-variable check and
//! `stage_06`'s substitution capture-avoidance set. A new binder
//! variant or a change to scope flow updates this file alone.
//!
//! ## Binding sites (must stay in lockstep with `free_vars`)
//!
//! - `Stmt::Let { pattern, value }` -- pattern names bind from the
//!   stmt onward in the same `Block` (value is in the pre-binding
//!   scope). `None` slots bind nothing.
//! - `MatchArm::bindings` -- bind for the arm `body` only.
//! - `Quantifier::binder` -- binds for `body` only; `domain` is in
//!   the outer scope.
//! - `Expr::While::iter_locals` -- each `init` is in the OUTER scope;
//!   the binder is bound for `header`, `cond`, and `body`.
//! - `Expr::While::header` -- the header's own `Let` binders stay in
//!   scope for `cond` and `body` (the header runs each iteration before
//!   them), matching `ir::validate`.
//! - `Block` -- snapshot/restore at the boundary so binders don't
//!   leak past their block.
//!
//! ## Use sites
//!
//! Besides `Expr::Var(v)`, three expression variants reference vars
//! structurally and count as uses: `Expr::BorrowLoc(v)`,
//! `Expr::WriteBack { node, child, world }` (child, the node var, and
//! the world var), and `Expr::IsParent { node, child }` (child + node
//! var). A `PathStep::MapKey { df_value: Some(v), .. }` on a
//! `Borrow`/`Update` is also a use.

use std::collections::BTreeSet;

use crate::ir::borrow::BorrowNode;
use crate::ir::expr::{Block, BlockTail, Expr, MatchArm, Stmt};
use crate::ir::ops::BitOp;
use crate::ir::quant::QuantDomain;
use crate::ir::VarId;

/// Observes variable uses encountered during a scope-tracking walk.
pub trait ScopeObserver {
    /// Called once per variable USE. `in_scope` is `true` iff `v` is
    /// bound by some enclosing binder within the walked sub-tree.
    fn on_use(&mut self, v: &VarId, in_scope: bool);
}

/// Walk `b` (treated as its own scope), reporting every variable use
/// to `o`.
pub fn walk_block<O: ScopeObserver>(o: &mut O, b: &Block) {
    let mut w = ScopeWalker {
        o,
        bound: BTreeSet::new(),
    };
    w.walk_block(b);
}

/// Walk a single expression (no enclosing block), reporting every
/// variable use to `o`. Equivalent to treating `e` as a 1-expression
/// block tail.
pub fn walk_expr<O: ScopeObserver>(o: &mut O, e: &Expr) {
    let mut w = ScopeWalker {
        o,
        bound: BTreeSet::new(),
    };
    w.walk_expr(e);
}

struct ScopeWalker<'o, O: ScopeObserver> {
    o: &'o mut O,
    bound: BTreeSet<VarId>,
}

impl<O: ScopeObserver> ScopeWalker<'_, O> {
    fn use_var(&mut self, v: &VarId) {
        let in_scope = self.bound.contains(v);
        self.o.on_use(v, in_scope);
    }

    fn walk_block(&mut self, b: &Block) {
        let snapshot = self.bound.clone();
        self.walk_block_open(b);
        self.bound = snapshot;
    }

    /// Walk a block's stmts + tail WITHOUT snapshot/restore -- its
    /// binders persist for whatever the caller walks next. Used for a
    /// `While` header, whose binders are in scope for the loop's `cond`
    /// and `body` (the header runs each iteration before them; matches
    /// `ir::validate` and the typed walker).
    fn walk_block_open(&mut self, b: &Block) {
        for s in &b.stmts {
            self.walk_stmt(s);
        }
        self.walk_tail(&b.tail);
    }

    fn walk_stmt(&mut self, s: &Stmt) {
        match s {
            Stmt::Let { pattern, value } => {
                // Value evaluated BEFORE pattern binders come into scope.
                self.walk_expr(value);
                for slot in pattern {
                    if let Some(v) = slot {
                        self.bound.insert(v.clone());
                    }
                }
            }
            Stmt::Eval(e) => self.walk_expr(e),
        }
    }

    fn walk_tail(&mut self, t: &BlockTail) {
        match t {
            BlockTail::Value(e) => self.walk_expr(e),
            BlockTail::Break { value, .. }
            | BlockTail::Continue { value, .. }
            | BlockTail::Return(value)
            | BlockTail::ReturnFromBlock { value, .. } => self.walk_expr(value),
            BlockTail::Abort { code } => self.walk_expr(code),
        }
    }

    fn walk_expr(&mut self, e: &Expr) {
        match e {
            Expr::Var(v) => self.use_var(v),
            Expr::Const(_) | Expr::Unit | Expr::BorrowGlobal(_) => {}

            Expr::BorrowLoc(v) => self.use_var(v),

            Expr::WriteBack {
                node, child, world, ..
            } => {
                self.use_var(child);
                match node {
                    BorrowNode::LocalRoot(v) | BorrowNode::Reference(v) => self.use_var(v),
                    BorrowNode::GlobalRoot(_) | BorrowNode::SpecGlobalRoot { .. } => {}
                }
                if let Some(v) = world {
                    self.use_var(v);
                }
            }
            Expr::IsParent { node, child, .. } => {
                self.use_var(child);
                match node {
                    BorrowNode::LocalRoot(v) | BorrowNode::Reference(v) => self.use_var(v),
                    BorrowNode::GlobalRoot(_) | BorrowNode::SpecGlobalRoot { .. } => {}
                }
            }
            Expr::Borrow { step, base } => {
                for e in step.exprs() {
                    self.walk_expr(e);
                }
                if let crate::ir::path::PathStep::MapKey {
                    df_value: Some(v), ..
                } = step
                {
                    self.use_var(v);
                }
                self.walk_expr(base);
            }
            Expr::Update { step, base, value } => {
                for e in step.exprs() {
                    self.walk_expr(e);
                }
                if let crate::ir::path::PathStep::MapKey {
                    df_value: Some(v), ..
                } = step
                {
                    self.use_var(v);
                }
                self.walk_expr(base);
                self.walk_expr(value);
            }

            Expr::BinOp { lhs, rhs, .. } => {
                self.walk_expr(lhs);
                self.walk_expr(rhs);
            }
            Expr::UnOp { operand, .. } => self.walk_expr(operand),
            Expr::BitOp(op) => self.walk_bitop(op),

            Expr::Call { args, .. } => args.iter().for_each(|a| self.walk_expr(a)),
            Expr::Tuple(elems) => elems.iter().for_each(|a| self.walk_expr(a)),
            Expr::Pack { fields, .. } => fields.iter().for_each(|a| self.walk_expr(a)),
            Expr::Unpack { value, .. }
            | Expr::Field { base: value, .. }
            | Expr::ReadRef(value)
            | Expr::ToProp(value)
            | Expr::ToBool(value) => self.walk_expr(value),

            Expr::If {
                cond,
                then_branch,
                else_branch,
            } => {
                self.walk_expr(cond);
                // Each arm scoped independently -- snapshot/restore is
                // handled by walk_block.
                self.walk_block(then_branch);
                self.walk_block(else_branch);
            }
            Expr::Match {
                selector, cases, ..
            } => {
                self.walk_expr(selector);
                for arm in cases {
                    self.walk_match_arm(arm);
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
                // iter_locals: each init evaluated in OUTER scope;
                // each binder bound for header, cond, body.
                for (_, init) in iter_locals {
                    self.walk_expr(init);
                }
                let snapshot = self.bound.clone();
                for (binder, _) in iter_locals {
                    self.bound.insert(binder.clone());
                }
                // Header runs each iteration before cond + body, so its
                // binders are in scope for both -- walk it OPEN (no
                // restore) so they persist (matches `ir::validate` and
                // the typed walker).
                self.walk_block_open(header);
                self.walk_expr(cond);
                self.walk_block(body);
                self.bound = snapshot;
            }

            Expr::WriteRef { reference, value } => {
                self.walk_expr(reference);
                self.walk_expr(value);
            }

            Expr::LabeledBlock { body, .. } => self.walk_block(body),

            Expr::Quantifier {
                binder,
                domain,
                body,
                ..
            } => {
                // Domain evaluated in outer scope; binder bound only
                // for body.
                match domain {
                    QuantDomain::Unbounded => {}
                    QuantDomain::Range { start, end } => {
                        self.walk_expr(start);
                        self.walk_expr(end);
                    }
                    QuantDomain::Collection(c) => self.walk_expr(c),
                    QuantDomain::VecRange { vec, start, end } => {
                        self.walk_expr(vec);
                        self.walk_expr(start);
                        self.walk_expr(end);
                    }
                }
                let snapshot = self.bound.clone();
                self.bound.insert(binder.clone());
                self.walk_block(body);
                self.bound = snapshot;
            }
        }
    }

    fn walk_bitop(&mut self, op: &BitOp) {
        match op {
            BitOp::Extract { operand, .. }
            | BitOp::ZeroExtend { operand, .. }
            | BitOp::SignExtend { operand, .. } => self.walk_expr(operand),
            BitOp::Concat { high, low } => {
                self.walk_expr(high);
                self.walk_expr(low);
            }
        }
    }

    fn walk_match_arm(&mut self, arm: &MatchArm) {
        let snapshot = self.bound.clone();
        for v in &arm.bindings {
            self.bound.insert(v.clone());
        }
        self.walk_block(&arm.body);
        self.bound = snapshot;
    }
}

// =====================================================================
// Typed-scope walker (binder TYPES, not just names).
// =====================================================================
//
// The set-flavor walker above answers "is this name bound?"; this one
// answers "what TYPE does each binder have, for which sub-tree?" -- so
// the consumers that need `type_of` at a node (stage 10's BinOp/Cast
// lowering and the typed baseline invariants) share one encoding of the
// binding discipline instead of each re-deriving it.
//
// The binding sites and scoping are identical to the set-flavor walker;
// the only addition is computing + threading types:
//
// - `Stmt::Let` binders come from the canonical `type_of` +
//   [`bind_pattern`] (strict: a malformed multi-pattern Let is an
//   error, propagated -- no best-effort fabrication, no `Type::Unit`
//   stand-in).
// - `Expr::While::iter_locals` binders come from `type_of(init)` in the
//   OUTER scope (inits are evaluated at loop entry, before any loop
//   binder exists).
// - `Expr::While::header` bindings stay in scope for `cond` and `body`:
//   the header runs each iteration before both, so its locals are
//   visible to them (the header is walked OPEN -- no snapshot/restore).
//   This matches `ir::validate`'s scope flow; a body that reads a
//   header-defined local (e.g. a binary search keeping the probe it
//   fetched in the header) types correctly instead of seeing it free.
// - `MatchArm::bindings` resolve to the variant's declared field types.
// - `type_of` failures propagate via the visitor's `Error`; the
//   consumer decides whether that aborts its pass or just stops the
//   walk (best-effort validators ignore the `Err`).
//
// Two flavors mirror `ir/visit.rs`'s Visitor / MutVisitor split:
// [`TypedScopeVisitor`] (read-only; the hook fires PRE-order) and
// [`TypedScopeMutVisitor`] (in-place; the hook fires POST-order so a
// rewrite of `e` sees its already-rewritten children).

use std::collections::BTreeMap;

use crate::ir::analysis::type_of::{bind_pattern, substitute_type_params, type_of, TypeOfError};
use crate::ir::ty::Type;
use crate::ir::{Program, StructId};

/// A scope mapping each in-scope binder to its inferred type.
pub type TypedScope = BTreeMap<VarId, Type>;

/// Read-only typed-scope visitor. [`TypedScopeVisitor::visit_expr`]
/// fires once per expression node in **pre-order**, with the typed
/// scope in effect at that node.
pub trait TypedScopeVisitor {
    type Error: From<TypeOfError>;
    fn visit_expr(&mut self, e: &Expr, scope: &TypedScope) -> Result<(), Self::Error>;
}

/// In-place typed-scope visitor. [`TypedScopeMutVisitor::visit_expr_mut`]
/// fires once per expression node in **post-order** (after the node's
/// children are walked/rewritten).
pub trait TypedScopeMutVisitor {
    type Error: From<TypeOfError>;
    fn visit_expr_mut(&mut self, e: &mut Expr, scope: &TypedScope) -> Result<(), Self::Error>;
}

/// Walk `b` with `scope` as the initial (parameter) scope, reporting
/// every expression to `v` (read-only, pre-order).
pub fn walk_typed_block<V: TypedScopeVisitor>(
    v: &mut V,
    b: &Block,
    scope: TypedScope,
    program: &Program,
) -> Result<(), V::Error> {
    TypedWalker { v, scope, program }.walk_block(b)
}

/// In-place counterpart of [`walk_typed_block`].
pub fn walk_typed_block_mut<V: TypedScopeMutVisitor>(
    v: &mut V,
    b: &mut Block,
    scope: TypedScope,
    program: &Program,
) -> Result<(), V::Error> {
    TypedMutWalker { v, scope, program }.walk_block(b)
}

/// Extend `scope` with a match arm's binders, resolved to the variant's
/// declared field types. Unresolvable variants (struct missing, not an
/// enum, tag out of range) bind nothing -- a use of an unbound arm
/// binder then surfaces as `UnboundVar` from `type_of`, which the
/// visitor propagates.
fn bind_match_arm(
    arm: &MatchArm,
    struct_id: StructId,
    type_args: &[Type],
    program: &Program,
    scope: &mut TypedScope,
) {
    if let Some(s) = program.structs.get(&struct_id) {
        if let Some(v) = s.variant_by_tag(arm.variant) {
            for (binder, field) in arm.bindings.iter().zip(v.fields.iter()) {
                scope.insert(
                    binder.clone(),
                    substitute_type_params(&field.field_type, type_args),
                );
            }
        }
    }
}

fn struct_type_args(ty: &Type, struct_id: StructId) -> Vec<Type> {
    match ty {
        Type::Struct {
            struct_id: actual,
            type_args,
        } if *actual == struct_id => type_args.clone(),
        Type::Reference(inner) | Type::MutableRef { inner, .. } => {
            struct_type_args(inner, struct_id)
        }
        Type::Tuple(elements) if elements.len() == 1 => struct_type_args(&elements[0], struct_id),
        _ => Vec::new(),
    }
}

struct TypedWalker<'a, V: TypedScopeVisitor> {
    v: &'a mut V,
    scope: TypedScope,
    program: &'a Program,
}

impl<V: TypedScopeVisitor> TypedWalker<'_, V> {
    fn walk_block(&mut self, b: &Block) -> Result<(), V::Error> {
        let snapshot = self.scope.clone();
        self.walk_block_open(b)?;
        self.scope = snapshot;
        Ok(())
    }

    /// Walk a block's stmts + tail into the CURRENT scope WITHOUT
    /// snapshot/restore -- its bindings persist for whatever the caller
    /// walks next. Used for a `While` header, whose bindings are in
    /// scope for the loop's `cond` and `body` (the header runs each
    /// iteration before them; matches `ir::validate`'s scope flow).
    fn walk_block_open(&mut self, b: &Block) -> Result<(), V::Error> {
        for s in &b.stmts {
            self.walk_stmt(s)?;
        }
        self.walk_tail(&b.tail)
    }

    fn walk_stmt(&mut self, s: &Stmt) -> Result<(), V::Error> {
        match s {
            Stmt::Let { pattern, value } => {
                self.walk_expr(value)?;
                let ty = type_of(value, &self.scope, self.program)?;
                bind_pattern(pattern, &ty, &mut self.scope)?;
            }
            Stmt::Eval(e) => self.walk_expr(e)?,
        }
        Ok(())
    }

    fn walk_tail(&mut self, t: &BlockTail) -> Result<(), V::Error> {
        match t {
            BlockTail::Value(e) => self.walk_expr(e),
            BlockTail::Break { value, .. }
            | BlockTail::Continue { value, .. }
            | BlockTail::Return(value)
            | BlockTail::ReturnFromBlock { value, .. } => self.walk_expr(value),
            BlockTail::Abort { code } => self.walk_expr(code),
        }
    }

    fn walk_expr(&mut self, e: &Expr) -> Result<(), V::Error> {
        self.v.visit_expr(e, &self.scope)?;
        match e {
            Expr::Var(_)
            | Expr::Const(_)
            | Expr::Unit
            | Expr::BorrowGlobal(_)
            | Expr::BorrowLoc(_)
            | Expr::WriteBack { .. }
            | Expr::IsParent { .. } => Ok(()),

            Expr::BinOp { lhs, rhs, .. } => {
                self.walk_expr(lhs)?;
                self.walk_expr(rhs)
            }
            Expr::UnOp { operand, .. } => self.walk_expr(operand),
            Expr::BitOp(op) => self.walk_bitop(op),

            Expr::Call { args, .. } | Expr::Tuple(args) | Expr::Pack { fields: args, .. } => {
                for a in args {
                    self.walk_expr(a)?;
                }
                Ok(())
            }
            Expr::Unpack { value, .. }
            | Expr::Field { base: value, .. }
            | Expr::ReadRef(value)
            | Expr::ToProp(value)
            | Expr::ToBool(value) => self.walk_expr(value),

            Expr::WriteRef { reference, value } => {
                self.walk_expr(reference)?;
                self.walk_expr(value)
            }
            Expr::Borrow { step, base } => {
                for pe in step.exprs() {
                    self.walk_expr(pe)?;
                }
                self.walk_expr(base)
            }
            Expr::Update { step, base, value } => {
                for pe in step.exprs() {
                    self.walk_expr(pe)?;
                }
                self.walk_expr(base)?;
                self.walk_expr(value)
            }

            Expr::If {
                cond,
                then_branch,
                else_branch,
            } => {
                self.walk_expr(cond)?;
                self.walk_block(then_branch)?;
                self.walk_block(else_branch)
            }
            Expr::Match {
                struct_id,
                selector,
                cases,
            } => {
                self.walk_expr(selector)?;
                let selector_type = type_of(selector, &self.scope, self.program)?;
                let type_args = struct_type_args(&selector_type, *struct_id);
                for arm in cases {
                    let snapshot = self.scope.clone();
                    bind_match_arm(arm, *struct_id, &type_args, self.program, &mut self.scope);
                    self.walk_block(&arm.body)?;
                    self.scope = snapshot;
                }
                Ok(())
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
                    self.walk_expr(init)?;
                }
                let snapshot = self.scope.clone();
                let mut binder_types = Vec::with_capacity(iter_locals.len());
                for (binder, init) in iter_locals {
                    let ty = type_of(init, &self.scope, self.program)?;
                    binder_types.push((binder.clone(), ty));
                }
                for (binder, ty) in binder_types {
                    self.scope.insert(binder, ty);
                }
                // Header runs each iteration before cond + body, so its
                // bindings are in scope for both -- walk it OPEN (no
                // restore) and let them persist (matches `ir::validate`).
                self.walk_block_open(header)?;
                self.walk_expr(cond)?;
                self.walk_block(body)?;
                self.scope = snapshot;
                Ok(())
            }
            Expr::Quantifier {
                binder,
                binder_type,
                domain,
                body,
                ..
            } => {
                match domain {
                    QuantDomain::Unbounded => {}
                    QuantDomain::Range { start, end } => {
                        self.walk_expr(start)?;
                        self.walk_expr(end)?;
                    }
                    QuantDomain::Collection(c) => self.walk_expr(c)?,
                    QuantDomain::VecRange { vec, start, end } => {
                        self.walk_expr(vec)?;
                        self.walk_expr(start)?;
                        self.walk_expr(end)?;
                    }
                }
                let snapshot = self.scope.clone();
                self.scope.insert(binder.clone(), binder_type.clone());
                self.walk_block(body)?;
                self.scope = snapshot;
                Ok(())
            }
            // Pre-stage-7 a labeled block sits in eval/sequencing position
            // and its result binding ESCAPES to the enclosing scope (stage 7
            // later extracts it into a helper and rebinds `let r = helper(..)`).
            // Walk it OPEN so that binding persists -- otherwise a later use of
            // it (`ika_system::authorize_upgrade`'s `$t3`) is seen free and
            // `type_of` fails with `UnboundVar`, which made stage 10
            // (bounded-nat) skip the function and leave raw `UInt` arithmetic
            // un-lowered. Mirrors the While-header open-walk and `ir::validate`.
            Expr::LabeledBlock { body, .. } => self.walk_block_open(body),
        }
    }

    fn walk_bitop(&mut self, op: &BitOp) -> Result<(), V::Error> {
        match op {
            BitOp::Extract { operand, .. }
            | BitOp::ZeroExtend { operand, .. }
            | BitOp::SignExtend { operand, .. } => self.walk_expr(operand),
            BitOp::Concat { high, low } => {
                self.walk_expr(high)?;
                self.walk_expr(low)
            }
        }
    }
}

struct TypedMutWalker<'a, V: TypedScopeMutVisitor> {
    v: &'a mut V,
    scope: TypedScope,
    program: &'a Program,
}

impl<V: TypedScopeMutVisitor> TypedMutWalker<'_, V> {
    fn walk_block(&mut self, b: &mut Block) -> Result<(), V::Error> {
        let snapshot = self.scope.clone();
        self.walk_block_open(b)?;
        self.scope = snapshot;
        Ok(())
    }

    fn walk_block_open(&mut self, b: &mut Block) -> Result<(), V::Error> {
        for s in b.stmts.iter_mut() {
            self.walk_stmt(s)?;
        }
        self.walk_tail(&mut b.tail)
    }

    fn walk_stmt(&mut self, s: &mut Stmt) -> Result<(), V::Error> {
        match s {
            Stmt::Let { pattern, value } => {
                self.walk_expr(value)?;
                let ty = type_of(value, &self.scope, self.program)?;
                bind_pattern(pattern, &ty, &mut self.scope)?;
            }
            Stmt::Eval(e) => self.walk_expr(e)?,
        }
        Ok(())
    }

    fn walk_tail(&mut self, t: &mut BlockTail) -> Result<(), V::Error> {
        match t {
            BlockTail::Value(e) => self.walk_expr(e),
            BlockTail::Break { value, .. }
            | BlockTail::Continue { value, .. }
            | BlockTail::Return(value)
            | BlockTail::ReturnFromBlock { value, .. } => self.walk_expr(value),
            BlockTail::Abort { code } => self.walk_expr(code),
        }
    }

    fn walk_expr(&mut self, e: &mut Expr) -> Result<(), V::Error> {
        match e {
            Expr::Var(_)
            | Expr::Const(_)
            | Expr::Unit
            | Expr::BorrowGlobal(_)
            | Expr::BorrowLoc(_)
            | Expr::WriteBack { .. }
            | Expr::IsParent { .. } => {}

            Expr::BinOp { lhs, rhs, .. } => {
                self.walk_expr(lhs)?;
                self.walk_expr(rhs)?;
            }
            Expr::UnOp { operand, .. } => self.walk_expr(operand)?,
            Expr::BitOp(op) => self.walk_bitop(op)?,

            Expr::Call { args, .. } | Expr::Tuple(args) | Expr::Pack { fields: args, .. } => {
                for a in args.iter_mut() {
                    self.walk_expr(a)?;
                }
            }
            Expr::Unpack { value, .. }
            | Expr::Field { base: value, .. }
            | Expr::ReadRef(value)
            | Expr::ToProp(value)
            | Expr::ToBool(value) => self.walk_expr(value)?,

            Expr::WriteRef { reference, value } => {
                self.walk_expr(reference)?;
                self.walk_expr(value)?;
            }
            Expr::Borrow { step, base } => {
                for pe in step.exprs_mut() {
                    self.walk_expr(pe)?;
                }
                self.walk_expr(base)?;
            }
            Expr::Update { step, base, value } => {
                for pe in step.exprs_mut() {
                    self.walk_expr(pe)?;
                }
                self.walk_expr(base)?;
                self.walk_expr(value)?;
            }

            Expr::If {
                cond,
                then_branch,
                else_branch,
            } => {
                self.walk_expr(cond)?;
                self.walk_block(then_branch)?;
                self.walk_block(else_branch)?;
            }
            Expr::Match {
                struct_id,
                selector,
                cases,
            } => {
                self.walk_expr(selector)?;
                let sid = *struct_id;
                let selector_type = type_of(selector, &self.scope, self.program)?;
                let type_args = struct_type_args(&selector_type, sid);
                for arm in cases.iter_mut() {
                    let snapshot = self.scope.clone();
                    bind_match_arm(arm, sid, &type_args, self.program, &mut self.scope);
                    self.walk_block(&mut arm.body)?;
                    self.scope = snapshot;
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
                for (_, init) in iter_locals.iter_mut() {
                    self.walk_expr(init)?;
                }
                let snapshot = self.scope.clone();
                let mut binder_types = Vec::with_capacity(iter_locals.len());
                for (binder, init) in iter_locals.iter() {
                    let ty = type_of(init, &self.scope, self.program)?;
                    binder_types.push((binder.clone(), ty));
                }
                for (binder, ty) in binder_types {
                    self.scope.insert(binder, ty);
                }
                // Header runs each iteration before cond + body, so its
                // bindings are in scope for both -- walk it OPEN (no
                // restore) and let them persist (matches `ir::validate`).
                self.walk_block_open(header)?;
                self.walk_expr(cond)?;
                self.walk_block(body)?;
                self.scope = snapshot;
            }
            Expr::Quantifier {
                binder,
                binder_type,
                domain,
                body,
                ..
            } => {
                match domain {
                    QuantDomain::Unbounded => {}
                    QuantDomain::Range { start, end } => {
                        self.walk_expr(start)?;
                        self.walk_expr(end)?;
                    }
                    QuantDomain::Collection(c) => self.walk_expr(c)?,
                    QuantDomain::VecRange { vec, start, end } => {
                        self.walk_expr(vec)?;
                        self.walk_expr(start)?;
                        self.walk_expr(end)?;
                    }
                }
                let snapshot = self.scope.clone();
                self.scope.insert(binder.clone(), binder_type.clone());
                self.walk_block(body)?;
                self.scope = snapshot;
            }
            // See the read-walker's LabeledBlock arm: the result binding
            // escapes to the enclosing scope, so walk OPEN (no restore).
            Expr::LabeledBlock { body, .. } => self.walk_block_open(body)?,
        }
        self.v.visit_expr_mut(e, &self.scope)?;
        Ok(())
    }

    fn walk_bitop(&mut self, op: &mut BitOp) -> Result<(), V::Error> {
        match op {
            BitOp::Extract { operand, .. }
            | BitOp::ZeroExtend { operand, .. }
            | BitOp::SignExtend { operand, .. } => self.walk_expr(operand),
            BitOp::Concat { high, low } => {
                self.walk_expr(high)?;
                self.walk_expr(low)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::analysis::type_of::TypeOfError;
    use crate::ir::builder::{
        binop, block, eval, forall, just, let_stmt, lit_bool, lit_u64, match_arm, match_expr,
        tail_continue, tail_value, unit, var, while_with_locals,
    };
    use crate::ir::ops::BinOp;
    use crate::ir::{Field, Program, Struct, Variant};
    use std::mem::{discriminant, Discriminant};

    struct Noop;
    impl TypedScopeVisitor for Noop {
        type Error = TypeOfError;
        fn visit_expr(&mut self, _e: &Expr, _scope: &TypedScope) -> Result<(), TypeOfError> {
            Ok(())
        }
    }

    struct NoopMut;
    impl TypedScopeMutVisitor for NoopMut {
        type Error = TypeOfError;
        fn visit_expr_mut(
            &mut self,
            _e: &mut Expr,
            _scope: &TypedScope,
        ) -> Result<(), TypeOfError> {
            Ok(())
        }
    }

    /// `while [i = 0] header { let h = 0 } (true) body { let b = h; continue(i) }`
    ///
    /// `h` is defined in the header and read in the body. The header runs
    /// each iteration before the body, so `h` is in scope there -- the
    /// body's `let b = h` must type via the threaded scope, not fail with
    /// `UnboundVar`. Regression for the pre-fix walker, which restored the
    /// header scope before the body and so reported `h` free (the
    /// `oracle::binary_search` stage-10 skip on momentum / bluefin).
    fn while_with_header_local() -> Block {
        let header = block(vec![let_stmt(&["h"], lit_u64(0))], tail_value(unit()));
        let body = block(vec![let_stmt(&["b"], var("h"))], tail_continue(0, var("i")));
        just(Expr::While {
            header: Box::new(header),
            cond: Box::new(lit_bool(true)),
            body: Box::new(body),
            iter_locals: vec![("i".into(), lit_u64(0))],
            header_exit_locals: vec!["i".into()],
            live_out: vec![],
        })
    }

    #[test]
    fn while_header_binding_is_in_scope_for_body() {
        let b = while_with_header_local();
        let prog = Program::default();
        assert!(walk_typed_block(&mut Noop, &b, TypedScope::new(), &prog).is_ok());
    }

    #[test]
    fn while_header_binding_is_in_scope_for_body_mut() {
        let mut b = while_with_header_local();
        let prog = Program::default();
        assert!(walk_typed_block_mut(&mut NoopMut, &mut b, TypedScope::new(), &prog).is_ok());
    }

    /// `let a = b; eval(a); while [i=0] {let h=a} (h) {eval(h); eval(i); free};
    ///  forall q {eval(q); free}; match sel {0(m) => {eval(m); free}}`
    ///
    /// Exercises the set-flavor walker's full binding discipline: free vars
    /// (`b`, `sel`, `free`) classified out of scope; `Let` binder `a`, the
    /// `While`-header local `h` (the subtle rule), iter-local `i`,
    /// `Quantifier` binder `q`, and `Match` arm binding `m` all in scope at
    /// their uses.
    fn scope_fixture() -> Block {
        let while_e = while_with_locals(
            vec![("i", lit_u64(0))],
            block(vec![let_stmt(&["h"], var("a"))], tail_value(unit())),
            var("h"),
            block(
                vec![eval(var("h")), eval(var("i"))],
                tail_value(var("free")),
            ),
        );
        let quant = forall("q", block(vec![eval(var("q"))], tail_value(var("free"))));
        let matched = match_expr(
            0,
            var("sel"),
            vec![match_arm(
                0,
                &["m"],
                block(vec![eval(var("m"))], tail_value(var("free"))),
            )],
        );
        block(
            vec![
                let_stmt(&["a"], var("b")),
                eval(var("a")),
                eval(while_e),
                eval(quant),
                eval(matched),
            ],
            tail_value(unit()),
        )
    }

    #[test]
    fn scope_observer_classifies_uses() {
        #[derive(Default)]
        struct Obs(Vec<(String, bool)>);
        impl ScopeObserver for Obs {
            fn on_use(&mut self, v: &VarId, in_scope: bool) {
                self.0.push((v.to_string(), in_scope));
            }
        }
        let mut o = Obs::default();
        walk_block(&mut o, &scope_fixture());
        let has = |name: &str, in_scope: bool| o.0.iter().any(|(n, s)| n == name && *s == in_scope);

        // Free vars are never reported in scope.
        assert!(has("b", false) && !has("b", true), "b is free");
        assert!(has("sel", false), "match selector sel is free");
        assert!(
            has("free", false) && !has("free", true),
            "free is free at every use"
        );
        // Bound vars are always in scope at their uses.
        assert!(has("a", true) && !has("a", false), "let-bound a in scope");
        assert!(
            has("h", true) && !has("h", false),
            "While-header local h in scope for cond + body"
        );
        assert!(has("i", true), "While iter-local binder i in scope in body");
        assert!(has("q", true), "Quantifier binder q in scope in body");
        assert!(has("m", true), "Match arm binding m in scope in arm body");
    }

    /// The typed walker doesn't just keep the While-header local in scope
    /// -- it threads its inferred TYPE. A body use of the header local sees
    /// `UInt(64)`, not a fabricated default. (The existing tests only check
    /// `is_ok()`.)
    #[test]
    fn typed_walker_threads_header_local_type() {
        let prog = Program::default();
        struct CaptureH(Option<Type>);
        impl TypedScopeVisitor for CaptureH {
            type Error = TypeOfError;
            fn visit_expr(&mut self, e: &Expr, scope: &TypedScope) -> Result<(), TypeOfError> {
                if matches!(e, Expr::Var(v) if v.as_ref() == "h") {
                    self.0 = scope.get("h").cloned();
                }
                Ok(())
            }
        }
        let mut cap = CaptureH(None);
        walk_typed_block(
            &mut cap,
            &while_with_header_local(),
            TypedScope::new(),
            &prog,
        )
        .unwrap();
        assert_eq!(
            cap.0,
            Some(Type::UInt(64)),
            "header local h must thread its UInt(64) type into the body"
        );
    }

    #[test]
    fn typed_walker_substitutes_generic_match_binding_type() {
        let mut prog = Program::default();
        prog.structs.insert(
            0,
            Struct {
                module_id: 0,
                name: "Carrier".into(),
                qualified_name: "P::m::Carrier".into(),
                type_params: vec!["T".into()],
                fields: Vec::new(),
                variants: Some(vec![Variant {
                    name: "some".into(),
                    tag: 0,
                    fields: vec![Field {
                        name: "value".into(),
                        field_type: Type::TypeParam(0),
                    }],
                }]),
                is_native: false,
            },
        );
        let body = just(match_expr(
            0,
            var("carrier"),
            vec![match_arm(0, &["payload"], just(var("payload")))],
        ));
        let mut initial = TypedScope::new();
        initial.insert(
            "carrier".into(),
            Type::Struct {
                struct_id: 0,
                type_args: vec![Type::UInt(64)],
            },
        );

        struct CapturePayload(Option<Type>);
        impl TypedScopeVisitor for CapturePayload {
            type Error = TypeOfError;

            fn visit_expr(&mut self, expr: &Expr, scope: &TypedScope) -> Result<(), TypeOfError> {
                if matches!(expr, Expr::Var(var) if var.as_ref() == "payload") {
                    self.0 = scope.get("payload").cloned();
                }
                Ok(())
            }
        }

        let mut capture = CapturePayload(None);
        walk_typed_block(&mut capture, &body, initial.clone(), &prog).unwrap();
        assert_eq!(capture.0, Some(Type::UInt(64)));

        struct CapturePayloadMut(Option<Type>);
        impl TypedScopeMutVisitor for CapturePayloadMut {
            type Error = TypeOfError;

            fn visit_expr_mut(
                &mut self,
                expr: &mut Expr,
                scope: &TypedScope,
            ) -> Result<(), TypeOfError> {
                if matches!(expr, Expr::Var(var) if var.as_ref() == "payload") {
                    self.0 = scope.get("payload").cloned();
                }
                Ok(())
            }
        }

        let mut mutable_body = body;
        let mut mutable_capture = CapturePayloadMut(None);
        walk_typed_block_mut(&mut mutable_capture, &mut mutable_body, initial, &prog).unwrap();
        assert_eq!(mutable_capture.0, Some(Type::UInt(64)));
    }

    /// The read walker fires PRE-order (parent before children); the mut
    /// walker fires POST-order (children before parent) so a rewrite of a
    /// node sees its already-rewritten children. Documented on the trait
    /// defs; nothing else guarded it.
    #[test]
    fn typed_read_is_preorder_mut_is_postorder() {
        let prog = Program::default();
        let binop_disc = discriminant(&binop(BinOp::Add, lit_u64(0), lit_u64(0)));

        struct PreOrder(Vec<Discriminant<Expr>>);
        impl TypedScopeVisitor for PreOrder {
            type Error = TypeOfError;
            fn visit_expr(&mut self, e: &Expr, _s: &TypedScope) -> Result<(), TypeOfError> {
                self.0.push(discriminant(e));
                Ok(())
            }
        }
        let mut pre = PreOrder(Vec::new());
        let read_block = just(binop(BinOp::Add, lit_u64(1), lit_u64(2)));
        walk_typed_block(&mut pre, &read_block, TypedScope::new(), &prog).unwrap();
        assert_eq!(
            pre.0.first(),
            Some(&binop_disc),
            "read walker must visit BinOp before its operands"
        );

        struct PostOrder(Vec<Discriminant<Expr>>);
        impl TypedScopeMutVisitor for PostOrder {
            type Error = TypeOfError;
            fn visit_expr_mut(&mut self, e: &mut Expr, _s: &TypedScope) -> Result<(), TypeOfError> {
                self.0.push(discriminant(e));
                Ok(())
            }
        }
        let mut post = PostOrder(Vec::new());
        let mut mut_block = just(binop(BinOp::Add, lit_u64(1), lit_u64(2)));
        walk_typed_block_mut(&mut post, &mut mut_block, TypedScope::new(), &prog).unwrap();
        assert_eq!(
            post.0.last(),
            Some(&binop_disc),
            "mut walker must visit BinOp after its operands"
        );
    }
}
