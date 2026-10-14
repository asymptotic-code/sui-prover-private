//! Visitor / traversal helpers.
//!
//! See `plans/lean-pipeline/ir.md` "Visitor / traversal" section. Two-method
//! visitor (`visit_block`, `visit_expr`) plus a `visit_stmt` / `visit_tail`
//! helper for completeness. Default impls walk children; stages override
//! the methods they care about.
//!
//! [`MutVisitor`] is the in-place rewriting counterpart: `visit_expr_mut`
//! receives `&mut Expr` and may replace the node wholesale (`*e = ...`).
//! Recursion into children happens only through the `walk_*_mut_default`
//! helpers, so an override chooses pre-order (rewrite, then walk) or
//! post-order (walk, then rewrite) explicitly. Prefer these over
//! hand-rolled `fn rewrite_expr(e: &mut Expr)` families -- a new `Expr`
//! variant then needs exactly one traversal update (here), not one per
//! pass.
//!
//! Each flavor also exposes `visit_var` (`visit_var_mut`), invoked by the
//! `walk_*` helpers on **every** `VarId` in the IR -- references (`Var`,
//! `BorrowLoc`), borrow slots (`WriteBack` / `IsParent` nodes,
//! `MapKey.df_value`), and binders (`Let` patterns, `While` iter-locals,
//! `Match` arm bindings, `Quantifier` binders). A whole-program var
//! rewrite (rename / substitution) overrides just `visit_var` and lets the
//! walk reach every slot, instead of re-listing them per pass. Global
//! references similarly flow through `visit_global` / `visit_global_mut`.

use super::borrow::BorrowNode;
use super::expr::{Block, BlockTail, Expr, MatchArm, Stmt};
use super::ops::BitOp;
use super::path::PathStep;
use super::quant::QuantDomain;
use super::{GlobalId, VarId};

/// Read-only visitor. Override the methods you care about; defaults walk
/// children via [`walk_expr_default`] (and friends). To both observe and
/// recurse from an override, do your observation then call the matching
/// `walk_*_default` helper.
pub trait Visitor {
    fn visit_block(&mut self, b: &Block) {
        walk_block_default(self, b);
    }

    fn visit_stmt(&mut self, s: &Stmt) {
        walk_stmt_default(self, s);
    }

    fn visit_tail(&mut self, t: &BlockTail) {
        walk_tail_default(self, t);
    }

    fn visit_expr(&mut self, e: &Expr) {
        walk_expr_default(self, e);
    }

    /// Invoked on every `VarId` occurrence -- references, borrow slots,
    /// and binders. Default: no-op.
    fn visit_var(&mut self, _v: &VarId) {}

    /// Invoked on every first-class global reference. Default: no-op.
    fn visit_global(&mut self, _global: GlobalId) {}

    fn visit_match_arm(&mut self, arm: &MatchArm) {
        for b in &arm.bindings {
            self.visit_var(b);
        }
        self.visit_block(&arm.body);
    }

    fn visit_bitop(&mut self, op: &BitOp) {
        match op {
            BitOp::Extract { operand, .. }
            | BitOp::ZeroExtend { operand, .. }
            | BitOp::SignExtend { operand, .. } => self.visit_expr(operand),
            BitOp::Concat { high, low } => {
                self.visit_expr(high);
                self.visit_expr(low);
            }
        }
    }
}

/// Walk `b`'s stmts then its tail. Call from override impls of
/// `Visitor::visit_block` to recurse after observing.
pub fn walk_block_default<V: Visitor + ?Sized>(v: &mut V, b: &Block) {
    for s in &b.stmts {
        v.visit_stmt(s);
    }
    v.visit_tail(&b.tail);
}

/// Walk `s`'s let-pattern binders then its value expression.
pub fn walk_stmt_default<V: Visitor + ?Sized>(v: &mut V, s: &Stmt) {
    match s {
        Stmt::Let { pattern, value } => {
            for p in pattern.iter().flatten() {
                v.visit_var(p);
            }
            v.visit_expr(value);
        }
        Stmt::Eval(e) => v.visit_expr(e),
    }
}

/// Walk `t`'s carried expression (every variant carries one).
pub fn walk_tail_default<V: Visitor + ?Sized>(v: &mut V, t: &BlockTail) {
    match t {
        BlockTail::Value(e) => v.visit_expr(e),
        BlockTail::Break { value, .. }
        | BlockTail::Continue { value, .. }
        | BlockTail::Return(value)
        | BlockTail::ReturnFromBlock { value, .. } => v.visit_expr(value),
        BlockTail::Abort { code } => v.visit_expr(code),
    }
}

/// Walk `e`'s direct sub-expressions / sub-blocks. Call from
/// override impls of `Visitor::visit_expr` to recurse after observing.
pub fn walk_expr_default<V: Visitor + ?Sized>(v: &mut V, e: &Expr) {
    match e {
        Expr::Const(_) | Expr::Unit => {}
        Expr::BorrowGlobal(global) => v.visit_global(*global),
        Expr::Var(x) | Expr::BorrowLoc(x) => v.visit_var(x),
        Expr::WriteBack {
            node, child, world, ..
        } => {
            match node {
                BorrowNode::LocalRoot(x) | BorrowNode::Reference(x) => v.visit_var(x),
                BorrowNode::GlobalRoot(global) => v.visit_global(*global),
                BorrowNode::SpecGlobalRoot { .. } => {}
            }
            v.visit_var(child);
            if let Some(w) = world {
                v.visit_var(w);
            }
        }
        Expr::IsParent { node, child, .. } => {
            match node {
                BorrowNode::LocalRoot(x) | BorrowNode::Reference(x) => v.visit_var(x),
                BorrowNode::GlobalRoot(global) => v.visit_global(*global),
                BorrowNode::SpecGlobalRoot { .. } => {}
            }
            v.visit_var(child);
        }
        Expr::BinOp { lhs, rhs, .. } => {
            v.visit_expr(lhs);
            v.visit_expr(rhs);
        }
        Expr::UnOp { operand, .. } => v.visit_expr(operand),
        Expr::BitOp(op) => v.visit_bitop(op),
        Expr::Call { args, .. } | Expr::Tuple(args) | Expr::Pack { fields: args, .. } => {
            args.iter().for_each(|a| v.visit_expr(a));
        }
        Expr::Unpack { value: inner, .. }
        | Expr::Field { base: inner, .. }
        | Expr::ReadRef(inner)
        | Expr::ToProp(inner)
        | Expr::ToBool(inner) => v.visit_expr(inner),
        Expr::Borrow { step, base } => {
            step.exprs().for_each(|e| v.visit_expr(e));
            if let PathStep::MapKey {
                df_value: Some(x), ..
            } = step
            {
                v.visit_var(x);
            }
            v.visit_expr(base);
        }
        Expr::Update { step, base, value } => {
            step.exprs().for_each(|e| v.visit_expr(e));
            if let PathStep::MapKey {
                df_value: Some(x), ..
            } = step
            {
                v.visit_var(x);
            }
            v.visit_expr(base);
            v.visit_expr(value);
        }
        Expr::If {
            cond,
            then_branch,
            else_branch,
        } => {
            v.visit_expr(cond);
            v.visit_block(then_branch);
            v.visit_block(else_branch);
        }
        Expr::Match {
            selector, cases, ..
        } => {
            v.visit_expr(selector);
            cases.iter().for_each(|arm| v.visit_match_arm(arm));
        }
        Expr::While {
            header,
            cond,
            body,
            iter_locals,
            header_exit_locals: _,
            live_out: _,
        } => {
            for (binder, init) in iter_locals {
                v.visit_var(binder);
                v.visit_expr(init);
            }
            v.visit_block(header);
            v.visit_expr(cond);
            v.visit_block(body);
        }
        Expr::WriteRef { reference, value } => {
            v.visit_expr(reference);
            v.visit_expr(value);
        }
        Expr::LabeledBlock { body, .. } => v.visit_block(body),
        Expr::Quantifier {
            binder,
            domain,
            body,
            ..
        } => {
            v.visit_var(binder);
            match domain {
                QuantDomain::Unbounded => {}
                QuantDomain::Range { start, end } => {
                    v.visit_expr(start);
                    v.visit_expr(end);
                }
                QuantDomain::Collection(c) => v.visit_expr(c),
                QuantDomain::VecRange { vec, start, end } => {
                    v.visit_expr(vec);
                    v.visit_expr(start);
                    v.visit_expr(end);
                }
            }
            v.visit_block(body);
        }
    }
}

/// In-place rewriting visitor. Override the methods you care about;
/// defaults walk children via [`walk_expr_mut_default`] (and friends).
pub trait MutVisitor {
    fn visit_block_mut(&mut self, b: &mut Block) {
        walk_block_mut_default(self, b);
    }

    fn visit_stmt_mut(&mut self, s: &mut Stmt) {
        walk_stmt_mut_default(self, s);
    }

    fn visit_tail_mut(&mut self, t: &mut BlockTail) {
        walk_tail_mut_default(self, t);
    }

    fn visit_expr_mut(&mut self, e: &mut Expr) {
        walk_expr_mut_default(self, e);
    }

    /// Invoked on every `VarId` occurrence -- references, borrow slots,
    /// and binders. Default: no-op. Override for whole-program renames.
    fn visit_var_mut(&mut self, _v: &mut VarId) {}

    /// Invoked on every first-class global reference. Default: no-op.
    fn visit_global_mut(&mut self, _global: &mut GlobalId) {}

    fn visit_match_arm_mut(&mut self, arm: &mut MatchArm) {
        for b in arm.bindings.iter_mut() {
            self.visit_var_mut(b);
        }
        self.visit_block_mut(&mut arm.body);
    }

    fn visit_bitop_mut(&mut self, op: &mut BitOp) {
        match op {
            BitOp::Extract { operand, .. }
            | BitOp::ZeroExtend { operand, .. }
            | BitOp::SignExtend { operand, .. } => self.visit_expr_mut(operand),
            BitOp::Concat { high, low } => {
                self.visit_expr_mut(high);
                self.visit_expr_mut(low);
            }
        }
    }
}

/// Walk `b`'s stmts then its tail, in place.
pub fn walk_block_mut_default<V: MutVisitor + ?Sized>(v: &mut V, b: &mut Block) {
    for s in b.stmts.iter_mut() {
        v.visit_stmt_mut(s);
    }
    v.visit_tail_mut(&mut b.tail);
}

/// Walk `s`'s let-pattern binders then its value expression, in place.
pub fn walk_stmt_mut_default<V: MutVisitor + ?Sized>(v: &mut V, s: &mut Stmt) {
    match s {
        Stmt::Let { pattern, value } => {
            for p in pattern.iter_mut().flatten() {
                v.visit_var_mut(p);
            }
            v.visit_expr_mut(value);
        }
        Stmt::Eval(e) => v.visit_expr_mut(e),
    }
}

/// Walk `t`'s carried expression, in place.
pub fn walk_tail_mut_default<V: MutVisitor + ?Sized>(v: &mut V, t: &mut BlockTail) {
    match t {
        BlockTail::Value(e) => v.visit_expr_mut(e),
        BlockTail::Break { value, .. }
        | BlockTail::Continue { value, .. }
        | BlockTail::Return(value)
        | BlockTail::ReturnFromBlock { value, .. } => v.visit_expr_mut(value),
        BlockTail::Abort { code } => v.visit_expr_mut(code),
    }
}

/// Walk `e`'s direct sub-expressions / sub-blocks, in place. Call from
/// override impls of `MutVisitor::visit_expr_mut` to recurse before or
/// after rewriting.
pub fn walk_expr_mut_default<V: MutVisitor + ?Sized>(v: &mut V, e: &mut Expr) {
    match e {
        Expr::Const(_) | Expr::Unit => {}
        Expr::BorrowGlobal(global) => v.visit_global_mut(global),
        Expr::Var(x) | Expr::BorrowLoc(x) => v.visit_var_mut(x),
        Expr::WriteBack {
            node, child, world, ..
        } => {
            match node {
                BorrowNode::LocalRoot(x) | BorrowNode::Reference(x) => v.visit_var_mut(x),
                BorrowNode::GlobalRoot(global) => v.visit_global_mut(global),
                BorrowNode::SpecGlobalRoot { .. } => {}
            }
            v.visit_var_mut(child);
            if let Some(w) = world {
                v.visit_var_mut(w);
            }
        }
        Expr::IsParent { node, child, .. } => {
            match node {
                BorrowNode::LocalRoot(x) | BorrowNode::Reference(x) => v.visit_var_mut(x),
                BorrowNode::GlobalRoot(global) => v.visit_global_mut(global),
                BorrowNode::SpecGlobalRoot { .. } => {}
            }
            v.visit_var_mut(child);
        }
        Expr::BinOp { lhs, rhs, .. } => {
            v.visit_expr_mut(lhs);
            v.visit_expr_mut(rhs);
        }
        Expr::UnOp { operand, .. } => v.visit_expr_mut(operand),
        Expr::BitOp(op) => v.visit_bitop_mut(op),
        Expr::Call { args, .. } | Expr::Tuple(args) | Expr::Pack { fields: args, .. } => {
            args.iter_mut().for_each(|a| v.visit_expr_mut(a));
        }
        Expr::Unpack { value: inner, .. }
        | Expr::Field { base: inner, .. }
        | Expr::ReadRef(inner)
        | Expr::ToProp(inner)
        | Expr::ToBool(inner) => v.visit_expr_mut(inner),
        Expr::Borrow { step, base } => {
            step.exprs_mut().for_each(|e| v.visit_expr_mut(e));
            if let PathStep::MapKey {
                df_value: Some(x), ..
            } = step
            {
                v.visit_var_mut(x);
            }
            v.visit_expr_mut(base);
        }
        Expr::Update { step, base, value } => {
            step.exprs_mut().for_each(|e| v.visit_expr_mut(e));
            if let PathStep::MapKey {
                df_value: Some(x), ..
            } = step
            {
                v.visit_var_mut(x);
            }
            v.visit_expr_mut(base);
            v.visit_expr_mut(value);
        }
        Expr::If {
            cond,
            then_branch,
            else_branch,
        } => {
            v.visit_expr_mut(cond);
            v.visit_block_mut(then_branch);
            v.visit_block_mut(else_branch);
        }
        Expr::Match {
            selector, cases, ..
        } => {
            v.visit_expr_mut(selector);
            cases.iter_mut().for_each(|arm| v.visit_match_arm_mut(arm));
        }
        Expr::While {
            header,
            cond,
            body,
            iter_locals,
            header_exit_locals: _,
            live_out: _,
        } => {
            for (binder, init) in iter_locals.iter_mut() {
                v.visit_var_mut(binder);
                v.visit_expr_mut(init);
            }
            v.visit_block_mut(header);
            v.visit_expr_mut(cond);
            v.visit_block_mut(body);
        }
        Expr::WriteRef { reference, value } => {
            v.visit_expr_mut(reference);
            v.visit_expr_mut(value);
        }
        Expr::LabeledBlock { body, .. } => v.visit_block_mut(body),
        Expr::Quantifier {
            binder,
            domain,
            body,
            ..
        } => {
            v.visit_var_mut(binder);
            match domain {
                QuantDomain::Unbounded => {}
                QuantDomain::Range { start, end } => {
                    v.visit_expr_mut(start);
                    v.visit_expr_mut(end);
                }
                QuantDomain::Collection(c) => v.visit_expr_mut(c),
                QuantDomain::VecRange { vec, start, end } => {
                    v.visit_expr_mut(vec);
                    v.visit_expr_mut(start);
                    v.visit_expr_mut(end);
                }
            }
            v.visit_block_mut(body);
        }
    }
}

/// Fallible in-place rewriting visitor: the `MutVisitor` counterpart for
/// passes whose rewrite can error (e.g. a stage that returns
/// `Result<(), StageNError>`). `visit_*_mut` return `Result<(),
/// Self::Error>`; the `walk_*_mut_try` helpers thread `?` so an override
/// recurses with `walk_block_mut_try(self, b)?` and short-circuits on the
/// first error. Prefer this over a hand-rolled `fn rewrite_expr(e: &mut
/// Expr) -> Result<(), E>` family -- a new `Expr` variant then needs one
/// traversal update here, not one per pass.
pub trait TryMutVisitor {
    type Error;

    fn visit_block_mut(&mut self, b: &mut Block) -> Result<(), Self::Error> {
        walk_block_mut_try(self, b)
    }

    fn visit_stmt_mut(&mut self, s: &mut Stmt) -> Result<(), Self::Error> {
        walk_stmt_mut_try(self, s)
    }

    fn visit_tail_mut(&mut self, t: &mut BlockTail) -> Result<(), Self::Error> {
        walk_tail_mut_try(self, t)
    }

    fn visit_expr_mut(&mut self, e: &mut Expr) -> Result<(), Self::Error> {
        walk_expr_mut_try(self, e)
    }

    /// Invoked on every `VarId` occurrence -- references, borrow slots,
    /// and binders. Default: no-op.
    fn visit_var_mut(&mut self, _v: &mut VarId) -> Result<(), Self::Error> {
        Ok(())
    }

    /// Invoked on every first-class global reference. Default: no-op.
    fn visit_global_mut(&mut self, _global: &mut GlobalId) -> Result<(), Self::Error> {
        Ok(())
    }

    fn visit_match_arm_mut(&mut self, arm: &mut MatchArm) -> Result<(), Self::Error> {
        for b in arm.bindings.iter_mut() {
            self.visit_var_mut(b)?;
        }
        self.visit_block_mut(&mut arm.body)
    }

    fn visit_bitop_mut(&mut self, op: &mut BitOp) -> Result<(), Self::Error> {
        match op {
            BitOp::Extract { operand, .. }
            | BitOp::ZeroExtend { operand, .. }
            | BitOp::SignExtend { operand, .. } => self.visit_expr_mut(operand),
            BitOp::Concat { high, low } => {
                self.visit_expr_mut(high)?;
                self.visit_expr_mut(low)
            }
        }
    }
}

/// Walk `b`'s stmts then its tail, in place, short-circuiting on error.
pub fn walk_block_mut_try<V: TryMutVisitor + ?Sized>(
    v: &mut V,
    b: &mut Block,
) -> Result<(), V::Error> {
    for s in b.stmts.iter_mut() {
        v.visit_stmt_mut(s)?;
    }
    v.visit_tail_mut(&mut b.tail)
}

/// Walk `s`'s let-pattern binders then its value expression, in place,
/// short-circuiting on error.
pub fn walk_stmt_mut_try<V: TryMutVisitor + ?Sized>(
    v: &mut V,
    s: &mut Stmt,
) -> Result<(), V::Error> {
    match s {
        Stmt::Let { pattern, value } => {
            for p in pattern.iter_mut().flatten() {
                v.visit_var_mut(p)?;
            }
            v.visit_expr_mut(value)
        }
        Stmt::Eval(e) => v.visit_expr_mut(e),
    }
}

/// Walk `t`'s carried expression, in place, short-circuiting on error.
pub fn walk_tail_mut_try<V: TryMutVisitor + ?Sized>(
    v: &mut V,
    t: &mut BlockTail,
) -> Result<(), V::Error> {
    match t {
        BlockTail::Value(e) => v.visit_expr_mut(e),
        BlockTail::Break { value, .. }
        | BlockTail::Continue { value, .. }
        | BlockTail::Return(value)
        | BlockTail::ReturnFromBlock { value, .. } => v.visit_expr_mut(value),
        BlockTail::Abort { code } => v.visit_expr_mut(code),
    }
}

/// Walk `e`'s direct sub-expressions / sub-blocks, in place,
/// short-circuiting on error. Mirrors [`walk_expr_mut_default`].
pub fn walk_expr_mut_try<V: TryMutVisitor + ?Sized>(
    v: &mut V,
    e: &mut Expr,
) -> Result<(), V::Error> {
    match e {
        Expr::Const(_) | Expr::Unit => Ok(()),
        Expr::BorrowGlobal(global) => v.visit_global_mut(global),
        Expr::Var(x) | Expr::BorrowLoc(x) => v.visit_var_mut(x),
        Expr::WriteBack {
            node, child, world, ..
        } => {
            match node {
                BorrowNode::LocalRoot(x) | BorrowNode::Reference(x) => v.visit_var_mut(x)?,
                BorrowNode::GlobalRoot(global) => v.visit_global_mut(global)?,
                BorrowNode::SpecGlobalRoot { .. } => {}
            }
            v.visit_var_mut(child)?;
            if let Some(w) = world {
                v.visit_var_mut(w)?;
            }
            Ok(())
        }
        Expr::IsParent { node, child, .. } => {
            match node {
                BorrowNode::LocalRoot(x) | BorrowNode::Reference(x) => v.visit_var_mut(x)?,
                BorrowNode::GlobalRoot(global) => v.visit_global_mut(global)?,
                BorrowNode::SpecGlobalRoot { .. } => {}
            }
            v.visit_var_mut(child)
        }
        Expr::BinOp { lhs, rhs, .. } => {
            v.visit_expr_mut(lhs)?;
            v.visit_expr_mut(rhs)
        }
        Expr::UnOp { operand, .. } => v.visit_expr_mut(operand),
        Expr::BitOp(op) => v.visit_bitop_mut(op),
        Expr::Call { args, .. } | Expr::Tuple(args) | Expr::Pack { fields: args, .. } => {
            for a in args.iter_mut() {
                v.visit_expr_mut(a)?;
            }
            Ok(())
        }
        Expr::Unpack { value: inner, .. }
        | Expr::Field { base: inner, .. }
        | Expr::ReadRef(inner)
        | Expr::ToProp(inner)
        | Expr::ToBool(inner) => v.visit_expr_mut(inner),
        Expr::Borrow { step, base } => {
            for e in step.exprs_mut() {
                v.visit_expr_mut(e)?;
            }
            if let PathStep::MapKey {
                df_value: Some(x), ..
            } = step
            {
                v.visit_var_mut(x)?;
            }
            v.visit_expr_mut(base)
        }
        Expr::Update { step, base, value } => {
            for e in step.exprs_mut() {
                v.visit_expr_mut(e)?;
            }
            if let PathStep::MapKey {
                df_value: Some(x), ..
            } = step
            {
                v.visit_var_mut(x)?;
            }
            v.visit_expr_mut(base)?;
            v.visit_expr_mut(value)
        }
        Expr::If {
            cond,
            then_branch,
            else_branch,
        } => {
            v.visit_expr_mut(cond)?;
            v.visit_block_mut(then_branch)?;
            v.visit_block_mut(else_branch)
        }
        Expr::Match {
            selector, cases, ..
        } => {
            v.visit_expr_mut(selector)?;
            for arm in cases.iter_mut() {
                v.visit_match_arm_mut(arm)?;
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
            for (binder, init) in iter_locals.iter_mut() {
                v.visit_var_mut(binder)?;
                v.visit_expr_mut(init)?;
            }
            v.visit_block_mut(header)?;
            v.visit_expr_mut(cond)?;
            v.visit_block_mut(body)
        }
        Expr::WriteRef { reference, value } => {
            v.visit_expr_mut(reference)?;
            v.visit_expr_mut(value)
        }
        Expr::LabeledBlock { body, .. } => v.visit_block_mut(body),
        Expr::Quantifier {
            binder,
            domain,
            body,
            ..
        } => {
            v.visit_var_mut(binder)?;
            match domain {
                QuantDomain::Unbounded => {}
                QuantDomain::Range { start, end } => {
                    v.visit_expr_mut(start)?;
                    v.visit_expr_mut(end)?;
                }
                QuantDomain::Collection(c) => v.visit_expr_mut(c)?,
                QuantDomain::VecRange { vec, start, end } => {
                    v.visit_expr_mut(vec)?;
                    v.visit_expr_mut(start)?;
                    v.visit_expr_mut(end)?;
                }
            }
            v.visit_block_mut(body)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{
        walk_expr_default, walk_expr_mut_default, walk_expr_mut_try, MutVisitor, TryMutVisitor,
        Visitor,
    };
    use crate::ir::builder::{
        binop, block, borrow_loc, call, eval, field, forall, if_expr, is_parent, just,
        labeled_block, let_stmt, map_key_borrow_df, match_arm, match_expr, pack, read_ref,
        tail_value, to_bool, to_prop, unit, unpack, var, while_with_locals, write_back, write_ref,
    };
    use crate::ir::expr::{Block, Expr};
    use crate::ir::ops::BinOp;
    use crate::ir::{BorrowEdge, BorrowNode, GlobalId, Type, VarId};
    use std::convert::Infallible;
    use std::mem::{discriminant, Discriminant};

    /// One block touching every `VarId` slot the IR carries -- references
    /// (`Var`/`BorrowLoc`), borrow slots (`WriteBack` node/child/world,
    /// `IsParent` node/child, `MapKey.df_value`), binders (`Let`, `While`
    /// iter-local, `Quantifier`, `Match` arm) -- plus one of every compound
    /// recursion shape. Types/semantics are irrelevant; these are
    /// structural walks.
    fn rich_block() -> Block {
        block(
            vec![
                let_stmt(&["a"], var("b")),
                eval(borrow_loc("bl")),
                eval(write_back("wn", "wc", Some("ww"))),
                eval(is_parent("pn", "pc")),
                eval(map_key_borrow_df(var("mb"), var("mk"), "mv")),
                eval(read_ref(write_ref(var("wr"), var("wv")))),
                eval(binop(BinOp::Add, var("lhs"), var("rhs"))),
                eval(call(0, vec![var("ca")])),
                eval(pack(0, vec![var("pk")])),
                eval(unpack(0, var("up"))),
                eval(field(0, 0, var("fb"))),
                eval(to_prop(to_bool(var("tp")))),
                eval(labeled_block(just(var("lb")), Type::Bool)),
                eval(if_expr(var("ic"), just(var("it")), just(var("ie")))),
                eval(while_with_locals(
                    vec![("i", var("c"))],
                    just(unit()),
                    var("d"),
                    just(var("e")),
                )),
                eval(forall("q", just(var("r")))),
                eval(match_expr(
                    0,
                    var("s"),
                    vec![match_arm(0, &["f"], just(var("g")))],
                )),
            ],
            tail_value(var("t")),
        )
    }

    const ALL_SLOTS: [&str; 34] = [
        "a", "b", "bl", "wn", "wc", "ww", "pn", "pc", "mb", "mk", "mv", "wr", "wv", "lhs", "rhs",
        "ca", "pk", "up", "fb", "tp", "lb", "ic", "it", "ie", "i", "c", "d", "e", "q", "r", "s",
        "f", "g", "t",
    ];

    #[derive(Default)]
    struct VarSeq(Vec<String>);
    impl Visitor for VarSeq {
        fn visit_var(&mut self, v: &VarId) {
            self.0.push(v.to_string());
        }
    }
    #[derive(Default)]
    struct VarSeqMut(Vec<String>);
    impl MutVisitor for VarSeqMut {
        fn visit_var_mut(&mut self, v: &mut VarId) {
            self.0.push(v.to_string());
        }
    }
    #[derive(Default)]
    struct VarSeqTry(Vec<String>);
    impl TryMutVisitor for VarSeqTry {
        type Error = Infallible;
        fn visit_var_mut(&mut self, v: &mut VarId) -> Result<(), Infallible> {
            self.0.push(v.to_string());
            Ok(())
        }
    }

    #[derive(Default)]
    struct GlobalSeq(Vec<GlobalId>);
    impl Visitor for GlobalSeq {
        fn visit_global(&mut self, global: GlobalId) {
            self.0.push(global);
        }
    }

    #[test]
    fn global_visitors_reach_borrow_and_root_slots() {
        let expr = Expr::Tuple(vec![
            Expr::BorrowGlobal(2),
            Expr::WriteBack {
                node: BorrowNode::GlobalRoot(3),
                edge: BorrowEdge::Direct,
                child: "child".into(),
                world: None,
            },
        ]);
        let mut globals = GlobalSeq::default();
        globals.visit_expr(&expr);
        assert_eq!(globals.0, vec![2, 3]);

        struct Increment;
        impl MutVisitor for Increment {
            fn visit_global_mut(&mut self, global: &mut GlobalId) {
                *global += 10;
            }
        }
        let mut rewritten = expr;
        Increment.visit_expr_mut(&mut rewritten);
        let mut globals = GlobalSeq::default();
        globals.visit_expr(&rewritten);
        assert_eq!(globals.0, vec![12, 13]);
    }

    /// `visit_var` reaches every VarId slot -- guards against a new slot
    /// (or `Expr` variant) added without a `visit_var` call.
    #[test]
    fn visit_var_reaches_every_slot() {
        let mut c = VarSeq::default();
        c.visit_block(&rich_block());
        let seen: std::collections::BTreeSet<&str> = c.0.iter().map(String::as_str).collect();
        for expected in ALL_SLOTS {
            assert!(
                seen.contains(expected),
                "visit_var missed `{expected}`: {seen:?}"
            );
        }
        assert_eq!(
            seen.len(),
            ALL_SLOTS.len(),
            "unexpected extra vars: {seen:?}"
        );
    }

    /// The three visitor flavors must visit the IDENTICAL sequence of
    /// VarId slots. The `walk_expr_*` mirrors are hand-maintained; a slot
    /// added to one but not another silently breaks renames in the stages
    /// using the un-updated flavor.
    #[test]
    fn visit_var_parity_across_flavors() {
        let mut read = VarSeq::default();
        read.visit_block(&rich_block());
        let mut mutated = VarSeqMut::default();
        mutated.visit_block_mut(&mut rich_block());
        let mut tried = VarSeqTry::default();
        tried.visit_block_mut(&mut rich_block()).unwrap();
        assert_eq!(
            read.0, mutated.0,
            "Visitor vs MutVisitor visit_var divergence"
        );
        assert_eq!(
            read.0, tried.0,
            "Visitor vs TryMutVisitor visit_var divergence"
        );
    }

    #[derive(Default)]
    struct ExprSeq(Vec<Discriminant<Expr>>);
    impl Visitor for ExprSeq {
        fn visit_expr(&mut self, e: &Expr) {
            self.0.push(discriminant(e));
            walk_expr_default(self, e);
        }
    }
    #[derive(Default)]
    struct ExprSeqMut(Vec<Discriminant<Expr>>);
    impl MutVisitor for ExprSeqMut {
        fn visit_expr_mut(&mut self, e: &mut Expr) {
            self.0.push(discriminant(e));
            walk_expr_mut_default(self, e);
        }
    }
    #[derive(Default)]
    struct ExprSeqTry(Vec<Discriminant<Expr>>);
    impl TryMutVisitor for ExprSeqTry {
        type Error = Infallible;
        fn visit_expr_mut(&mut self, e: &mut Expr) -> Result<(), Infallible> {
            self.0.push(discriminant(e));
            walk_expr_mut_try(self, e)
        }
    }

    /// The three flavors must reach the IDENTICAL sequence of `Expr` nodes
    /// -- catches a recursion arm present in one `walk_expr_*` but dropped
    /// in another (a subtree a `MutVisitor` rewrite would silently skip).
    #[test]
    fn expr_traversal_parity_across_flavors() {
        let mut read = ExprSeq::default();
        read.visit_block(&rich_block());
        let mut mutated = ExprSeqMut::default();
        mutated.visit_block_mut(&mut rich_block());
        let mut tried = ExprSeqTry::default();
        tried.visit_block_mut(&mut rich_block()).unwrap();
        assert_eq!(
            read.0, mutated.0,
            "Visitor vs MutVisitor expr-traversal divergence"
        );
        assert_eq!(
            read.0, tried.0,
            "Visitor vs TryMutVisitor expr-traversal divergence"
        );
    }

    /// A no-op `MutVisitor` / `TryMutVisitor` must leave the IR untouched
    /// -- guards against an accidental `mem::replace` / `take` left in a
    /// `walk_*_mut` helper.
    #[test]
    fn noop_mut_walk_is_identity() {
        struct NoopMut;
        impl MutVisitor for NoopMut {}
        struct NoopTry;
        impl TryMutVisitor for NoopTry {
            type Error = Infallible;
        }
        let original = rich_block();

        let mut a = original.clone();
        NoopMut.visit_block_mut(&mut a);
        assert_eq!(a, original, "no-op MutVisitor mutated the IR");

        let mut b = original.clone();
        NoopTry.visit_block_mut(&mut b).unwrap();
        assert_eq!(b, original, "no-op TryMutVisitor mutated the IR");
    }

    /// `visit_var_mut` renames EVERY slot -- the hook's whole purpose is
    /// "override one method for a total whole-program rename." A missed
    /// slot leaks the old name.
    #[test]
    fn visit_var_mut_rename_is_total() {
        struct Renamer {
            from: &'static str,
            to: &'static str,
        }
        impl MutVisitor for Renamer {
            fn visit_var_mut(&mut self, v: &mut VarId) {
                if v.as_ref() == self.from {
                    *v = self.to.into();
                }
            }
        }
        // `x` planted in every var slot.
        let mut b = block(
            vec![
                let_stmt(&["x"], var("x")),
                eval(borrow_loc("x")),
                eval(write_back("x", "x", Some("x"))),
                eval(is_parent("x", "x")),
                eval(map_key_borrow_df(var("x"), var("x"), "x")),
                eval(while_with_locals(
                    vec![("x", var("x"))],
                    just(unit()),
                    var("x"),
                    just(var("x")),
                )),
                eval(forall("x", just(var("x")))),
                eval(match_expr(
                    0,
                    var("x"),
                    vec![match_arm(0, &["x"], just(var("x")))],
                )),
            ],
            tail_value(var("x")),
        );
        let before = {
            let mut c = VarSeq::default();
            c.visit_block(&b);
            c.0.len()
        };
        Renamer { from: "x", to: "y" }.visit_block_mut(&mut b);
        let mut c = VarSeq::default();
        c.visit_block(&b);
        assert!(
            c.0.iter().all(|v| v == "y"),
            "rename left stale `x`: {:?}",
            c.0
        );
        assert_eq!(c.0.len(), before, "rename changed the slot count");
    }
}
