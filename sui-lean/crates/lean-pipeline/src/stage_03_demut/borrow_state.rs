//! Per-function borrow-state map: `VarId -> (root_var, edges)` for
//! every `&mut`-typed temp produced by a `BorrowLoc` or `BorrowField`
//! chain in the function's body.
//!
//! Stage 2 emits chains as a sequence of `Stmt::Let { pattern: [r], value: BorrowLoc(_) | BorrowField { base: Var(prev), .. } }`
//! statements (mirrors upstream's `Operation::BorrowLoc` /
//! `Operation::BorrowField` lifting). This module folds those one-step
//! bindings into resolved `(root, edges)` pairs that Phase 4's
//! WriteRef / WriteBack rebinders consume.
//!
//! Function-scoped flat map -- VarIds are unique within a function
//! (stage 2 names them `$t0`, `$t1`, ...), so nesting doesn't cause
//! key collisions. Bindings inside `If` / `While` / `Match` arms are
//! visible to the entire function's writeback pass.

use std::collections::BTreeMap;

use crate::ir::{Block, BlockTail, BorrowEdge, Expr, Function, MatchArm, Stmt, VarId};

/// A resolved borrow chain: the `VarId` of the chain's local-variable
/// root, plus the sequence of `BorrowEdge`s from root to leaf.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BorrowChain {
    pub root: VarId,
    pub edges: Vec<BorrowEdge>,
}

/// Borrow-state map for one function: every mutref temp's resolved
/// chain.
pub type BorrowState = BTreeMap<VarId, BorrowChain>;

/// Build the borrow-state map for `func`. Walks the body recursively
/// (descending into `If` / `Match` / `While` arms) and folds every
/// `Stmt::Let { value: BorrowLoc(_) | BorrowField { .. } }` into the
/// map.
pub fn build(func: &Function) -> BorrowState {
    let mut state = BorrowState::new();
    walk_block(&func.body, &mut state);
    state
}

fn walk_block(block: &Block, state: &mut BorrowState) {
    for stmt in &block.stmts {
        match stmt {
            Stmt::Let { pattern, value } => {
                // Single-binding patterns only -- multi-binding Lets
                // come from Calls / Tuples, never from BorrowLoc /
                // BorrowField (which always have a single dest).
                if pattern.len() == 1 {
                    if let Some(name) = &pattern[0] {
                        if let Some(chain) = chain_from(value, state) {
                            state.insert(name.clone(), chain);
                        }
                    }
                }
                walk_expr(value, state);
            }
            Stmt::Eval(e) => walk_expr(e, state),
        }
    }
    walk_tail(&block.tail, state);
}

fn walk_tail(tail: &BlockTail, state: &mut BorrowState) {
    match tail {
        BlockTail::Value(e) => walk_expr(e, state),
        BlockTail::Break { value, .. }
        | BlockTail::Continue { value, .. }
        | BlockTail::Return(value)
        | BlockTail::ReturnFromBlock { value, .. } => walk_expr(value, state),
        BlockTail::Abort { code } => walk_expr(code, state),
    }
}

fn walk_expr(expr: &Expr, state: &mut BorrowState) {
    match expr {
        Expr::If {
            cond: _,
            then_branch,
            else_branch,
        } => {
            walk_block(then_branch, state);
            walk_block(else_branch, state);
        }
        Expr::Match {
            selector: _, cases, ..
        } => {
            for arm in cases {
                let MatchArm { body, .. } = arm;
                walk_block(body, state);
            }
        }
        Expr::While {
            header,
            cond: _,
            body,
            ..
        } => {
            walk_block(header, state);
            walk_block(body, state);
        }
        Expr::Quantifier { body, .. } => walk_block(body, state),
        _ => {}
    }
}

/// Resolve `e` to a borrow chain if it's a `BorrowLoc` or a
/// `Borrow { step, .. }` whose chain we can trace via the existing
/// state. The step's operand-free [`BorrowEdge`] (via
/// `PathStep::to_edge`) is what the chain records.
fn chain_from(e: &Expr, state: &BorrowState) -> Option<BorrowChain> {
    match e {
        Expr::BorrowLoc(name) => Some(BorrowChain {
            root: name.clone(),
            edges: Vec::new(),
        }),
        Expr::Borrow { step, base } => extend_with_edge(base, step.to_edge(), state),
        _ => None,
    }
}

fn extend_with_edge(base: &Expr, new_edge: BorrowEdge, state: &BorrowState) -> Option<BorrowChain> {
    match base {
        Expr::Var(prev) => {
            let prev_chain = state.get(prev)?;
            let mut edges = prev_chain.edges.clone();
            edges.push(new_edge);
            Some(BorrowChain {
                root: prev_chain.root.clone(),
                edges,
            })
        }
        Expr::BorrowLoc(name) => Some(BorrowChain {
            root: name.clone(),
            edges: vec![new_edge],
        }),
        Expr::Borrow {
            step: inner_step,
            base: inner_base,
        } => {
            let prev = extend_with_edge(inner_base, inner_step.to_edge(), state)?;
            let mut edges = prev.edges;
            edges.push(new_edge);
            Some(BorrowChain {
                root: prev.root,
                edges,
            })
        }
        _ => None,
    }
}
