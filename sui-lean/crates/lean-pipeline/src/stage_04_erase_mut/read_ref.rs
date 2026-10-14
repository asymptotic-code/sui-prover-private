//! Rewrite 1 -- substitute every `Expr::ReadRef(Var(r))` with
//! `path_to_expr(root, edges)`.
//!
//! Stage 3 leaves `Expr::BorrowLoc` / `Expr::BorrowField` chains in
//! place and every `Expr::ReadRef(Var(r))` that consumes them. This
//! pass walks each function body once:
//!
//! 1. Reuses stage 3's `BorrowState` builder to produce a
//!    function-scoped `VarId -> BorrowChain` map from the
//!    `BorrowLoc` / `BorrowField` bindings.
//! 2. Walks every expression. For each `Expr::ReadRef(Var(r))` where
//!    `r` is in the borrow-state map, replaces the `ReadRef` with
//!    `path_to_expr(chain.root, &chain.edges)`.
//! 3. Leaves `Expr::ReadRef` on non-mutref locals alone -- those
//!    shouldn't reach stage 4 on well-formed input, but the
//!    postcondition validator catches them defensively.
//!
//! `BorrowLoc` / `BorrowField` bindings themselves are NOT dropped
//! here -- that's Rewrite 2's concern (Phase 2). After this pass, the
//! bindings still exist but may have no readers.

use crate::ir::{Block, BlockTail, Expr, FunId, MatchArm, Program, Stmt};

use super::path_to_expr::path_to_expr;
use crate::stage_03_demut::{build_borrow_state, BorrowChain, BorrowState};

/// Rewrite every `Expr::ReadRef(Var(r))` in every non-native function
/// body in `program` to the corresponding `path_to_expr` projection.
pub fn rewrite_read_refs(program: &mut Program) {
    let funcs: Vec<FunId> = program.functions.iter().map(|(id, _)| *id).collect();
    for fid in funcs {
        let state = build_borrow_state(&program.functions[&fid]);
        let func = program.functions.get_mut(&fid).unwrap();
        rewrite_block(&mut func.body, &state);
    }
}

fn rewrite_block(block: &mut Block, state: &BorrowState) {
    let stmts = std::mem::take(&mut block.stmts);
    block.stmts = stmts.into_iter().map(|s| rewrite_stmt(s, state)).collect();
    rewrite_tail(&mut block.tail, state);
}

fn rewrite_stmt(stmt: Stmt, state: &BorrowState) -> Stmt {
    match stmt {
        Stmt::Let { pattern, value } => Stmt::Let {
            pattern,
            value: rewrite_expr(value, state),
        },
        Stmt::Eval(e) => Stmt::Eval(rewrite_expr(e, state)),
    }
}

fn rewrite_tail(tail: &mut BlockTail, state: &BorrowState) {
    match tail {
        BlockTail::Value(e) => {
            let taken = std::mem::replace(e, Expr::Unit);
            *e = rewrite_expr(taken, state);
        }
        BlockTail::Break { value, .. }
        | BlockTail::Continue { value, .. }
        | BlockTail::Return(value)
        | BlockTail::ReturnFromBlock { value, .. } => {
            let taken = std::mem::replace(&mut **value, Expr::Unit);
            **value = rewrite_expr(taken, state);
        }
        BlockTail::Abort { code } => {
            let taken = std::mem::replace(&mut **code, Expr::Unit);
            **code = rewrite_expr(taken, state);
        }
    }
}

fn rebuild_path_step(
    step: crate::ir::path::PathStep,
    state: &BorrowState,
) -> crate::ir::path::PathStep {
    use crate::ir::path::PathStep;
    match step {
        PathStep::Field { .. } | PathStep::VariantField { .. } => step,
        PathStep::VecIndex(i) => PathStep::VecIndex(Box::new(rewrite_expr(*i, state))),
        PathStep::MapKey {
            key,
            key_type,
            value_type,
            df_value,
        } => PathStep::MapKey {
            key: Box::new(rewrite_expr(*key, state)),
            key_type,
            value_type,
            df_value,
        },
    }
}

fn rewrite_expr(expr: Expr, state: &BorrowState) -> Expr {
    match expr {
        Expr::Borrow { step, base } => Expr::Borrow {
            step: rebuild_path_step(step, state),
            base: Box::new(rewrite_expr(*base, state)),
        },
        Expr::Update { step, base, value } => Expr::Update {
            step: rebuild_path_step(step, state),
            base: Box::new(rewrite_expr(*base, state)),
            value: Box::new(rewrite_expr(*value, state)),
        },
        // ---- The substitution target ---------------------------------
        Expr::ReadRef(inner) => {
            // Recurse first so nested ReadRefs inside the inner
            // expression (rare but possible -- e.g. `ReadRef(call(...))`)
            // also get processed.
            let inner = rewrite_expr(*inner, state);
            if let Expr::Var(name) = &inner {
                if let Some(chain) = state.get(name) {
                    return path_to_expr_from_chain(chain);
                }
            }
            // Not a known mutref temp -- leave the ReadRef in place.
            // Stage 4's postcondition flags it if it survives.
            Expr::ReadRef(Box::new(inner))
        }

        // ---- Recursive descent through every sub-expression ----------
        Expr::BinOp { op, lhs, rhs } => Expr::BinOp {
            op,
            lhs: Box::new(rewrite_expr(*lhs, state)),
            rhs: Box::new(rewrite_expr(*rhs, state)),
        },
        Expr::UnOp { op, operand } => Expr::UnOp {
            op,
            operand: Box::new(rewrite_expr(*operand, state)),
        },
        Expr::BitOp(op) => Expr::BitOp(rewrite_bitop(op, state)),
        Expr::Call {
            fun,
            type_args,
            args,
        } => Expr::Call {
            fun,
            type_args,
            args: args.into_iter().map(|a| rewrite_expr(a, state)).collect(),
        },
        Expr::Tuple(items) => {
            Expr::Tuple(items.into_iter().map(|a| rewrite_expr(a, state)).collect())
        }
        Expr::Pack {
            struct_id,
            type_args,
            variant,
            fields,
        } => Expr::Pack {
            struct_id,
            type_args,
            variant,
            fields: fields.into_iter().map(|a| rewrite_expr(a, state)).collect(),
        },
        Expr::Unpack {
            struct_id,
            variant,
            value,
        } => Expr::Unpack {
            struct_id,
            variant,
            value: Box::new(rewrite_expr(*value, state)),
        },
        Expr::Field {
            struct_id,
            field_index,
            base,
        } => Expr::Field {
            struct_id,
            field_index,
            base: Box::new(rewrite_expr(*base, state)),
        },
        Expr::If {
            cond,
            mut then_branch,
            mut else_branch,
        } => {
            rewrite_block(&mut then_branch, state);
            rewrite_block(&mut else_branch, state);
            Expr::If {
                cond: Box::new(rewrite_expr(*cond, state)),
                then_branch,
                else_branch,
            }
        }
        Expr::Match {
            struct_id,
            selector,
            cases,
            ..
        } => Expr::Match {
            struct_id,
            selector: Box::new(rewrite_expr(*selector, state)),
            cases: cases
                .into_iter()
                .map(|arm| {
                    let MatchArm {
                        variant,
                        bindings,
                        mut body,
                    } = arm;
                    rewrite_block(&mut body, state);
                    MatchArm {
                        variant,
                        bindings,
                        body,
                    }
                })
                .collect(),
        },
        Expr::While {
            mut header,
            cond,
            mut body,
            iter_locals,
            header_exit_locals,
            live_out: _,
        } => {
            rewrite_block(&mut header, state);
            rewrite_block(&mut body, state);
            Expr::While {
                header,
                cond: Box::new(rewrite_expr(*cond, state)),
                body,
                iter_locals,
                header_exit_locals,
                live_out: Vec::new(),
            }
        }
        Expr::WriteRef { reference, value } => Expr::WriteRef {
            reference: Box::new(rewrite_expr(*reference, state)),
            value: Box::new(rewrite_expr(*value, state)),
        },
        Expr::ToProp(inner) => Expr::ToProp(Box::new(rewrite_expr(*inner, state))),
        Expr::ToBool(inner) => Expr::ToBool(Box::new(rewrite_expr(*inner, state))),
        Expr::Quantifier {
            kind,
            binder,
            binder_type,
            domain,
            mut body,
        } => {
            rewrite_block(&mut body, state);
            Expr::Quantifier {
                kind,
                binder,
                binder_type,
                domain,
                body,
            }
        }

        // ---- Leaf / non-descending variants --------------------------
        e @ Expr::Var(_)
        | e @ Expr::Const(_)
        | e @ Expr::Unit
        | e @ Expr::BorrowLoc(_)
        | e @ Expr::BorrowGlobal(_)
        | e @ Expr::WriteBack { .. }
        | e @ Expr::IsParent { .. } => e,
        Expr::LabeledBlock {
            mut body,
            result_ty,
        } => {
            rewrite_block(&mut body, state);
            Expr::LabeledBlock { body, result_ty }
        }
    }
}

fn rewrite_bitop(op: crate::ir::BitOp, state: &BorrowState) -> crate::ir::BitOp {
    use crate::ir::BitOp::*;
    match op {
        Extract { high, low, operand } => Extract {
            high,
            low,
            operand: Box::new(rewrite_expr(*operand, state)),
        },
        Concat { high, low } => Concat {
            high: Box::new(rewrite_expr(*high, state)),
            low: Box::new(rewrite_expr(*low, state)),
        },
        ZeroExtend { bits, operand } => ZeroExtend {
            bits,
            operand: Box::new(rewrite_expr(*operand, state)),
        },
        SignExtend { bits, operand } => SignExtend {
            bits,
            operand: Box::new(rewrite_expr(*operand, state)),
        },
    }
}

/// Build a `path_to_expr` projection from a stage-3 [`BorrowChain`].
/// Stage 3's `BorrowChain` and stage 4's local `BorrowChain` share
/// the same field shape; this helper hides the import path.
fn path_to_expr_from_chain(chain: &BorrowChain) -> Expr {
    path_to_expr(chain.root.clone(), &chain.edges)
}
