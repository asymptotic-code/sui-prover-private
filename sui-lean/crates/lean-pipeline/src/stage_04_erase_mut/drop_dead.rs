//! Rewrite 2 -- drop dead `Stmt::Let { value: BorrowLoc | BorrowField }`
//! bindings.
//!
//! After Rewrite 1 substitutes every `ReadRef(Var(r))` with the
//! corresponding `path_to_expr` projection, the intermediate
//! `BorrowLoc` / `BorrowField` bindings produced by stage 2 may have
//! no remaining consumers. This pass walks each function body once
//! per fixpoint iteration:
//!
//! 1. Collect every `Stmt::Let { pattern: [Some(r)], value: BorrowLoc(_) | BorrowField {..} }`
//!    binding (the **candidate** set).
//! 2. Scan every `Expr::Var(v)` in the body -- including inside
//!    other candidate bindings' values. The **live** set is every
//!    `VarId` that appears in a `Var(_)` somewhere.
//! 3. A candidate is **dead** iff its `r` is not in the live set.
//! 4. Drop every dead candidate's `Stmt::Let`. Iterate until no
//!    bindings are dropped in a pass (fixpoint).
//!
//! Pattern 4b survives **naturally**: a `BorrowField` / `BorrowLoc`
//! at the function's tail position is NOT a `Stmt::Let` binding, so
//! it's not in the candidate set. Its `base: Var(prev_temp)`
//! reference keeps the chain of intermediate temps live transitively
//! through the live-set scan.

use std::collections::BTreeSet;

use crate::ir::{Block, BlockTail, Expr, FunId, MatchArm, Program, Stmt, VarId};

/// Drop every dead `Stmt::Let { value: BorrowLoc | BorrowField }` in
/// every non-native function body in `program`.
pub fn drop_dead_borrows(program: &mut Program) {
    let funcs: Vec<FunId> = program.functions.iter().map(|(id, _)| *id).collect();
    for fid in funcs {
        let func = program.functions.get_mut(&fid).unwrap();
        drop_dead_in_function(&mut func.body);
    }
}

/// Drop dead borrow bindings in one function body. Iterates to
/// fixpoint -- typical Move bytecode has chains 1-3 deep so this
/// terminates in 1-3 iterations.
fn drop_dead_in_function(body: &mut Block) {
    loop {
        let live = collect_live_vars(body);
        let dropped = drop_dead_block(body, &live);
        if !dropped {
            break;
        }
    }
}

/// Walk the block and collect every `VarId` referenced in any
/// `Expr::Var(_)` position.
fn collect_live_vars(block: &Block) -> BTreeSet<VarId> {
    let mut live = BTreeSet::new();
    collect_block(block, &mut live);
    live
}

fn collect_block(block: &Block, live: &mut BTreeSet<VarId>) {
    for s in &block.stmts {
        collect_stmt(s, live);
    }
    collect_tail(&block.tail, live);
}

fn collect_stmt(stmt: &Stmt, live: &mut BTreeSet<VarId>) {
    match stmt {
        Stmt::Let { value, .. } => collect_expr(value, live),
        Stmt::Eval(e) => collect_expr(e, live),
    }
}

fn collect_tail(tail: &BlockTail, live: &mut BTreeSet<VarId>) {
    match tail {
        BlockTail::Value(e) => collect_expr(e, live),
        BlockTail::Break { value, .. }
        | BlockTail::Continue { value, .. }
        | BlockTail::Return(value)
        | BlockTail::ReturnFromBlock { value, .. } => collect_expr(value, live),
        BlockTail::Abort { code } => collect_expr(code, live),
    }
}

fn collect_expr(expr: &Expr, live: &mut BTreeSet<VarId>) {
    match expr {
        Expr::Borrow { step, base } => {
            for __pe in step.exprs() {
                collect_expr(__pe, live);
            }
            collect_expr(base, live);
        }
        Expr::Update { step, base, value } => {
            for __pe in step.exprs() {
                collect_expr(__pe, live);
            }
            collect_expr(base, live);
            collect_expr(value, live);
        }
        Expr::Var(v) => {
            live.insert(v.clone());
        }
        Expr::Const(_)
        | Expr::Unit
        | Expr::BorrowLoc(_)
        | Expr::BorrowGlobal(_)
        | Expr::WriteBack { .. }
        | Expr::IsParent { .. } => {}
        Expr::BinOp { lhs, rhs, .. } => {
            collect_expr(lhs, live);
            collect_expr(rhs, live);
        }
        Expr::UnOp { operand, .. } => collect_expr(operand, live),
        Expr::BitOp(op) => collect_bitop(op, live),
        Expr::Call { args, .. } | Expr::Tuple(args) | Expr::Pack { fields: args, .. } => {
            for a in args {
                collect_expr(a, live);
            }
        }
        Expr::Unpack { value: inner, .. }
        | Expr::Field { base: inner, .. }
        | Expr::ReadRef(inner)
        | Expr::ToProp(inner)
        | Expr::ToBool(inner) => collect_expr(inner, live),
        Expr::If {
            cond,
            then_branch,
            else_branch,
        } => {
            collect_expr(cond, live);
            collect_block(then_branch, live);
            collect_block(else_branch, live);
        }
        Expr::Match {
            selector, cases, ..
        } => {
            collect_expr(selector, live);
            for arm in cases {
                collect_block(&arm.body, live);
            }
        }
        Expr::While {
            header, cond, body, ..
        } => {
            collect_block(header, live);
            collect_expr(cond, live);
            collect_block(body, live);
        }
        Expr::WriteRef { reference, value } => {
            collect_expr(reference, live);
            collect_expr(value, live);
        }
        Expr::Quantifier { body, domain, .. } => {
            collect_quant_domain(domain, live);
            collect_block(body, live);
        }
        Expr::LabeledBlock { body, .. } => collect_block(body, live),
    }
}

fn collect_quant_domain(d: &crate::ir::QuantDomain, live: &mut BTreeSet<VarId>) {
    use crate::ir::QuantDomain::*;
    match d {
        Unbounded => {}
        Range { start, end } => {
            collect_expr(start, live);
            collect_expr(end, live);
        }
        Collection(c) => collect_expr(c, live),
        VecRange { vec, start, end } => {
            collect_expr(vec, live);
            collect_expr(start, live);
            collect_expr(end, live);
        }
    }
}

fn collect_bitop(op: &crate::ir::BitOp, live: &mut BTreeSet<VarId>) {
    use crate::ir::BitOp::*;
    match op {
        Extract { operand, .. } | ZeroExtend { operand, .. } | SignExtend { operand, .. } => {
            collect_expr(operand, live);
        }
        Concat { high, low } => {
            collect_expr(high, live);
            collect_expr(low, live);
        }
    }
}

// ---------------------------------------------------------------------------
// Drop pass
// ---------------------------------------------------------------------------

/// Returns true if at least one dead binding was dropped in this
/// block (recursively).
fn drop_dead_block(block: &mut Block, live: &BTreeSet<VarId>) -> bool {
    let stmts = std::mem::take(&mut block.stmts);
    let mut dropped_any = false;
    let mut kept = Vec::with_capacity(stmts.len());
    for stmt in stmts {
        match &stmt {
            Stmt::Let { pattern, value }
                if pattern.len() == 1
                    && matches!(
                        value,
                        Expr::BorrowLoc(_)
                            | Expr::Borrow {
                                step: crate::ir::path::PathStep::Field { .. },
                                ..
                            }
                    ) =>
            {
                let name = match &pattern[0] {
                    Some(n) => n,
                    None => {
                        // Single None pattern shouldn't happen (validator),
                        // but we keep it just in case.
                        kept.push(stmt);
                        continue;
                    }
                };
                if !live.contains(name) {
                    dropped_any = true;
                    // drop the binding
                } else {
                    kept.push(stmt);
                }
            }
            _ => kept.push(stmt),
        }
    }
    block.stmts = kept;

    for stmt in block.stmts.iter_mut() {
        match stmt {
            Stmt::Let { value, .. } => {
                dropped_any |= drop_dead_in_expr(value, live);
            }
            Stmt::Eval(e) => {
                dropped_any |= drop_dead_in_expr(e, live);
            }
        }
    }
    dropped_any |= drop_dead_in_tail(&mut block.tail, live);
    dropped_any
}

fn drop_dead_in_tail(tail: &mut BlockTail, live: &BTreeSet<VarId>) -> bool {
    match tail {
        BlockTail::Value(e) => drop_dead_in_expr(e, live),
        BlockTail::Break { value, .. }
        | BlockTail::Continue { value, .. }
        | BlockTail::Return(value)
        | BlockTail::ReturnFromBlock { value, .. } => drop_dead_in_expr(value, live),
        BlockTail::Abort { code } => drop_dead_in_expr(code, live),
    }
}

fn drop_dead_in_expr(expr: &mut Expr, live: &BTreeSet<VarId>) -> bool {
    let mut any = false;
    match expr {
        Expr::If {
            cond,
            then_branch,
            else_branch,
        } => {
            any |= drop_dead_in_expr(cond, live);
            any |= drop_dead_block(then_branch, live);
            any |= drop_dead_block(else_branch, live);
        }
        Expr::Match {
            selector, cases, ..
        } => {
            any |= drop_dead_in_expr(selector, live);
            for MatchArm { body, .. } in cases.iter_mut() {
                any |= drop_dead_block(body, live);
            }
        }
        Expr::While {
            header, cond, body, ..
        } => {
            any |= drop_dead_block(header, live);
            any |= drop_dead_in_expr(cond, live);
            any |= drop_dead_block(body, live);
        }
        Expr::Quantifier { body, .. } => {
            any |= drop_dead_block(body, live);
        }
        // Other variants don't contain `Block`s -- nothing to recurse into.
        _ => {}
    }
    any
}
