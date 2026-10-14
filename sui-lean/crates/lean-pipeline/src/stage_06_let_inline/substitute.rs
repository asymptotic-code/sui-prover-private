//! `Var(v) -> Expr` substitution helper with capture-avoiding
//! hygiene.
//!
//! Stage 6's sub-passes 2a (`copy_inline`) and 2b (`single_use`)
//! both inline an expression at every reference to a specific
//! variable. Substitution must:
//!
//! - Replace `Expr::Var(w)` with `replacement.clone()` whenever
//!   `w == v`.
//! - **Not** enter scopes that shadow `v` (the bound name no
//!   longer references the outer var).
//! - **Not** enter scopes that shadow a free var of `replacement`
//!   (capture hazard -- the placed expression would silently bind
//!   to the inner binder).
//!
//! The free-var set of `replacement` is computed once via the shared
//! [`crate::ir::analysis::free_vars::free_vars_of_expr`], so the
//! binding discipline (every block's `Let`s, `Match` arms, `While`
//! iter-locals, `Quantifier` binders) is the single canonical one --
//! `If`/`While`/`Match`/`Let` all introduce scope the same way.
//!
//! ## Borrow positions
//!
//! `v` also occurs in `VarId`-slot (borrow) positions: `BorrowLoc(v)`,
//! `WriteBack` (`child` / `world` / `node` var), `IsParent`, and a
//! `MapKey`'s `df_value`. A borrow names a *location*, and only a
//! variable names a location -- an expression has none. So those slots
//! are substitutable **only by another variable** (a rename). The
//! substituter renames them when `replacement` is `Expr::Var(u)`; the
//! inliner guarantees (via `UseCount::has_borrow_use`) that a non-`Var`
//! replacement is never inlined for a var with a borrow use, so reaching
//! such a slot with a non-`Var` replacement is a bug -- we panic rather
//! than silently corrupt.
//!
//! In SSA form none of the shadow hazards arise (every binding is
//! fresh); the substituter is defensive.

use std::collections::BTreeSet;

use crate::ir::analysis::free_vars::free_vars_of_expr;
use crate::ir::visit::{walk_expr_mut_default, MutVisitor};
use crate::ir::{quant::QuantDomain, Block, BlockTail, Expr, Stmt, VarId};

/// Substitute every unbound `Expr::Var(v)` in `body` with
/// `replacement.clone()`.
pub fn substitute_var(body: &mut Block, v: &VarId, replacement: &Expr) {
    Substituter::new(v, replacement).visit_block_mut(body);
}

/// Substitute inside a single `Stmt`. Used by `copy_inline` to
/// avoid re-walking the entire block; same hygiene as
/// `substitute_var`.
pub fn substitute_var_in_stmt(s: &mut Stmt, v: &VarId, replacement: &Expr) {
    Substituter::new(v, replacement).visit_stmt_mut(s);
}

/// Substitute inside a `BlockTail`. Used by `copy_inline`.
pub fn substitute_var_in_tail(t: &mut BlockTail, v: &VarId, replacement: &Expr) {
    Substituter::new(v, replacement).visit_tail_mut(t);
}

struct Substituter<'a> {
    v: &'a VarId,
    repl: &'a Expr,
    /// `Some(u)` iff `repl` is `Expr::Var(u)` -- the only shape that can
    /// occupy a borrow (`VarId`) slot.
    repl_var: Option<&'a VarId>,
    free: BTreeSet<VarId>,
}

impl<'a> Substituter<'a> {
    fn new(v: &'a VarId, repl: &'a Expr) -> Self {
        let repl_var = match repl {
            Expr::Var(u) => Some(u),
            _ => None,
        };
        Substituter {
            v,
            repl,
            repl_var,
            free: free_vars_of_expr(repl),
        }
    }

    fn shadows(&self, binder: &VarId) -> bool {
        binder == self.v || self.free.contains(binder)
    }

    /// Rename a borrow-position `VarId` slot if it names `v`. Only a
    /// `Var` replacement can fill a location slot; a non-`Var`
    /// replacement reaching here means the inliner's borrow-use guard
    /// failed.
    fn rename_borrow_slot(&self, slot: &mut VarId) {
        if slot == self.v {
            match self.repl_var {
                Some(u) => *slot = u.clone(),
                None => panic!(
                    "stage 6 substitute: cannot place a non-Var replacement into a borrow \
                     position for {:?}; the inliner's has_borrow_use guard should have refused",
                    self.v
                ),
            }
        }
    }

    /// Walk a block's stmts (substituting), then its tail. A `Stmt::Let`
    /// binder that shadows `v` or captures a free var of `repl` puts the
    /// rest of the block -- subsequent stmts AND the tail -- in the
    /// shadowed scope, so we stop there. Returns `true` iff a shadow
    /// stopped the walk early; `While` uses this for header -> cond/body
    /// scope flow. This makes `Let` introduce scope exactly like the
    /// `Match`/`While`/`Quantifier` binders below -- every binder is
    /// treated uniformly.
    fn subst_block(&mut self, b: &mut Block) -> bool {
        for s in b.stmts.iter_mut() {
            // The Let value is in the pre-binding scope -- substitute it
            // first, then let the pattern shadow subsequent stmts.
            self.visit_stmt_mut(s);
            if let Stmt::Let { pattern, .. } = s {
                if pattern.iter().flatten().any(|slot| self.shadows(slot)) {
                    return true;
                }
            }
        }
        self.visit_tail_mut(&mut b.tail);
        false
    }
}

impl MutVisitor for Substituter<'_> {
    fn visit_block_mut(&mut self, b: &mut Block) {
        // `Let` binders shadow within the block exactly like the other
        // binders; `subst_block` stops at the first shadowing `Let`.
        self.subst_block(b);
    }

    /// Fires on every `VarId` slot the walk reaches. `Expr::Var` is
    /// intercepted in `visit_expr_mut` (replaced, never recursed) and
    /// binders are handled by the scope-aware arms + the value-only
    /// `visit_stmt_mut` below -- so this only ever sees a borrow-position
    /// location slot (`BorrowLoc`, `WriteBack`/`IsParent` node & child &
    /// world, `MapKey.df_value`), which `rename_borrow_slot` renames (or
    /// panics on a non-`Var` replacement).
    fn visit_var_mut(&mut self, slot: &mut VarId) {
        self.rename_borrow_slot(slot);
    }

    /// Substitute a stmt's VALUE only. The default walk fires
    /// `visit_var_mut` on `Let` pattern binders, but a binder is a fresh
    /// referent that is never renamed -- `subst_block` handles its
    /// shadowing separately.
    fn visit_stmt_mut(&mut self, s: &mut Stmt) {
        match s {
            Stmt::Let { value, .. } => self.visit_expr_mut(value),
            Stmt::Eval(e) => self.visit_expr_mut(e),
        }
    }

    fn visit_expr_mut(&mut self, e: &mut Expr) {
        match e {
            Expr::Var(w) => {
                if w == self.v {
                    *e = self.repl.clone();
                }
            }

            // Borrow-position `VarId` location slots (`BorrowLoc`,
            // `WriteBack`/`IsParent`, `MapKey.df_value`) are renamed via
            // `visit_var_mut` as the default walk reaches them.
            Expr::Match {
                selector, cases, ..
            } => {
                self.visit_expr_mut(selector);
                for arm in cases.iter_mut() {
                    // Arm-local bindings shadow if any matches `v` or
                    // any free var of `repl`; in that case, don't
                    // recurse into the body.
                    if arm.bindings.iter().any(|b| self.shadows(b)) {
                        continue;
                    }
                    self.visit_block_mut(&mut arm.body);
                }
            }
            Expr::While {
                header,
                cond,
                body,
                iter_locals,
                ..
            } => {
                // Each iter-local `init` evaluates ONCE in the OUTER
                // scope at loop entry (before its binder exists), so it
                // is always substituted regardless of the binders.
                for (_loc, init) in iter_locals.iter_mut() {
                    self.visit_expr_mut(init);
                }
                // `iter_locals` binders are in scope for `header`,
                // `cond`, and `body`. Skip substitution there if any of
                // them shadows `v` (different referent inside the loop)
                // or captures a free var of `repl` (would silently bind).
                if iter_locals.iter().any(|(loc, _init)| self.shadows(loc)) {
                    return;
                }
                // The header runs each iteration before `cond` and
                // `body`, so its bindings are in scope for both (uniform
                // with `Let` scoping in any block). A header `Let` that
                // shadows `v` / captures a free var of `repl` therefore
                // blocks substitution in `cond` and `body` too.
                if self.subst_block(header) {
                    return;
                }
                self.visit_expr_mut(cond);
                self.visit_block_mut(body);
            }
            Expr::Quantifier {
                binder,
                domain,
                body,
                ..
            } => {
                // Domain is evaluated in outer scope -- binder is not
                // in scope for the domain.
                match domain {
                    QuantDomain::Unbounded => {}
                    QuantDomain::Range { start, end } => {
                        self.visit_expr_mut(start);
                        self.visit_expr_mut(end);
                    }
                    QuantDomain::Collection(c) => self.visit_expr_mut(c),
                    QuantDomain::VecRange { vec, start, end } => {
                        self.visit_expr_mut(vec);
                        self.visit_expr_mut(start);
                        self.visit_expr_mut(end);
                    }
                }
                // Body is in the scope of `binder`. Skip if `binder`
                // shadows `v` or captures a free var of `repl`.
                if !self.shadows(binder) {
                    self.visit_block_mut(body);
                }
            }
            _ => walk_expr_mut_default(self, e),
        }
    }
}
