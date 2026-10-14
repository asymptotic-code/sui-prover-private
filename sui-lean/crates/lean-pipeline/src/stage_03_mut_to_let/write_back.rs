//! Transforms 2-3 -- `Stmt::Eval(WriteBack ..)` -> `Stmt::Let { pattern: [target], value: WriteBack .. }`.
//!
//! Same position-shift pattern as `WriteRef`. The rebind target is
//! extracted from the `BorrowNode`:
//!
//! - `BorrowNode::LocalRoot(x)` -> target = `x`.
//! - `BorrowNode::Reference(parent_mut)` -> target = `parent_mut`.
//! - `BorrowNode::SpecGlobalRoot { .. }` -> no rebind target; the
//!   statement is left as `Stmt::Eval(WriteBack { SpecGlobalRoot, .. })`
//!   so the renderer's ghost-state path
//!   (`render_writeback` -> `Prover.Mutation.writeBackSpecGlobal`) sees
//!   the Unit-typed expression inside an `let _ := ...` discard.
//!
//! `GlobalRoot` is a frontend-only C-global node and is unreachable here:
//! `thread_globals` rewrites it to `Reference(hidden_param)`, while `run`
//! fails closed if the lifecycle boundary was skipped.

use crate::ir::{Block, BlockTail, BorrowNode, Expr, FunId, MatchArm, Program, Stmt};

use super::Stage3Error;

/// Rewrite every `Stmt::Eval(WriteBack ..)` in every function body
/// in `program` to a `Stmt::Let` rebind of the target.
///
/// `program.functions` is body-only after step 5 of
/// `no-stubs-templated-natives.md` -- there are no native entries to
/// skip; the natives registry (`program.natives.decls`) doesn't
/// carry bodies.
pub fn rewrite_write_backs(program: &mut Program) -> Result<(), Stage3Error> {
    let funcs: Vec<FunId> = program.functions.iter().map(|(id, _)| *id).collect();
    for fid in funcs {
        let func = program.functions.get_mut(&fid).unwrap();
        rewrite_block(&mut func.body, fid)?;
    }
    Ok(())
}

fn rewrite_block(block: &mut Block, fid: FunId) -> Result<(), Stage3Error> {
    let stmts = std::mem::take(&mut block.stmts);
    let mut rewritten = Vec::with_capacity(stmts.len());
    for stmt in stmts {
        rewritten.push(rewrite_stmt(stmt, fid)?);
    }
    block.stmts = rewritten;
    rewrite_tail(&mut block.tail, fid)
}

fn rewrite_stmt(stmt: Stmt, fid: FunId) -> Result<Stmt, Stage3Error> {
    match stmt {
        Stmt::Eval(Expr::WriteBack {
            node,
            edge,
            child,
            world,
        }) => match target_var(&node) {
            Some(target) => {
                // Position-shift: same WriteBack expression moves into
                // Stmt::Let::value, rebinding the target.
                Ok(Stmt::Let {
                    pattern: vec![Some(target)],
                    value: Expr::WriteBack {
                        node,
                        edge,
                        child,
                        world,
                    },
                })
            }
            None => {
                // SpecGlobalRoot writeback: no local to rebind. Leave the
                // statement as-is; the renderer maps it to a Unit-typed
                // `Prover.Mutation.writeBackSpecGlobal (...)` call inside
                // `let _ := ...` (see `render::expr::render_writeback` and
                // `render_stmt`'s `Stmt::Eval` arm).
                Ok(Stmt::Eval(Expr::WriteBack {
                    node,
                    edge,
                    child,
                    world,
                }))
            }
        },
        Stmt::Eval(other) => Ok(Stmt::Eval(rewrite_subblocks(other, fid)?)),
        Stmt::Let { pattern, value } => Ok(Stmt::Let {
            pattern,
            value: rewrite_subblocks(value, fid)?,
        }),
    }
}

/// Extract the rebind target from a `BorrowNode`. `LocalRoot` and
/// `Reference` both carry a `VarId`; `SpecGlobalRoot` has no local
/// binding to rebind (ghost-state writebacks are handled by the
/// renderer's `writeBackSpecGlobal` stub), so we return `None` and
/// `rewrite_stmt` keeps the original `Stmt::Eval(WriteBack ..)`.
fn target_var(node: &BorrowNode) -> Option<crate::ir::VarId> {
    match node {
        BorrowNode::LocalRoot(v) | BorrowNode::Reference(v) => Some(v.clone()),
        BorrowNode::GlobalRoot(global) => {
            unreachable!("GlobalRoot({global}) passed stage 3's thread_globals precondition")
        }
        BorrowNode::SpecGlobalRoot { .. } => None,
    }
}

fn rewrite_tail(tail: &mut BlockTail, fid: FunId) -> Result<(), Stage3Error> {
    match tail {
        BlockTail::Value(e) => {
            let taken = std::mem::replace(e, Expr::Unit);
            *e = rewrite_subblocks(taken, fid)?;
        }
        BlockTail::Break { value, .. }
        | BlockTail::Continue { value, .. }
        | BlockTail::Return(value)
        | BlockTail::ReturnFromBlock { value, .. } => {
            let taken = std::mem::replace(&mut **value, Expr::Unit);
            **value = rewrite_subblocks(taken, fid)?;
        }
        BlockTail::Abort { code } => {
            let taken = std::mem::replace(&mut **code, Expr::Unit);
            **code = rewrite_subblocks(taken, fid)?;
        }
    }
    Ok(())
}

fn rewrite_subblocks(expr: Expr, fid: FunId) -> Result<Expr, Stage3Error> {
    match expr {
        Expr::If {
            cond,
            mut then_branch,
            mut else_branch,
        } => {
            rewrite_block(&mut then_branch, fid)?;
            rewrite_block(&mut else_branch, fid)?;
            Ok(Expr::If {
                cond,
                then_branch,
                else_branch,
            })
        }
        Expr::Match {
            struct_id,
            selector,
            cases,
            ..
        } => {
            let mut new_cases = Vec::with_capacity(cases.len());
            for arm in cases {
                let MatchArm {
                    variant,
                    bindings,
                    mut body,
                } = arm;
                rewrite_block(&mut body, fid)?;
                new_cases.push(MatchArm {
                    variant,
                    bindings,
                    body,
                });
            }
            Ok(Expr::Match {
                struct_id,
                selector,
                cases: new_cases,
            })
        }
        Expr::While {
            mut header,
            cond,
            mut body,
            iter_locals,
            header_exit_locals,
            live_out: _,
        } => {
            rewrite_block(&mut header, fid)?;
            rewrite_block(&mut body, fid)?;
            Ok(Expr::While {
                header,
                cond,
                body,
                iter_locals,
                header_exit_locals,
                live_out: Vec::new(),
            })
        }
        Expr::Quantifier {
            kind,
            binder,
            binder_type,
            domain,
            mut body,
        } => {
            rewrite_block(&mut body, fid)?;
            Ok(Expr::Quantifier {
                kind,
                binder,
                binder_type,
                domain,
                body,
            })
        }
        Expr::LabeledBlock {
            mut body,
            result_ty,
        } => {
            rewrite_block(&mut body, fid)?;
            Ok(Expr::LabeledBlock { body, result_ty })
        }
        other => Ok(other),
    }
}
