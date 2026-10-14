//! Transform 1 -- `Stmt::Eval(WriteRef ..)` -> `Stmt::Let { pattern: [r], value: WriteRef .. }`.
//!
//! Position-shift only. Same `Expr::WriteRef` value moves from
//! statement-position (side-effecting interpretation) to value-position
//! inside a `Stmt::Let` binding (value-form interpretation). The
//! renderer is responsible for mapping `Expr::WriteRef` in value
//! position to `Mutation.updateValue` in the Lean output.

use crate::ir::{Block, BlockTail, Expr, FunId, MatchArm, Program, Stmt};

use super::Stage3Error;

/// Rewrite every `Stmt::Eval(WriteRef ..)` in every function body
/// in `program` to a `Stmt::Let` rebind of the reference.
pub fn rewrite_write_refs(program: &mut Program) -> Result<(), Stage3Error> {
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
        Stmt::Eval(Expr::WriteRef { reference, value }) => {
            let r = match *reference {
                Expr::Var(name) => name,
                _other => return Err(Stage3Error::WriteRefNonVar { function: fid }),
            };
            // Position-shift: the same WriteRef expression moves into
            // Stmt::Let::value, rebinding `r` to the updated Mutation.
            Ok(Stmt::Let {
                pattern: vec![Some(r.clone())],
                value: Expr::WriteRef {
                    reference: Box::new(Expr::Var(r)),
                    value,
                },
            })
        }
        Stmt::Eval(other) => Ok(Stmt::Eval(rewrite_subblocks(other, fid)?)),
        Stmt::Let { pattern, value } => Ok(Stmt::Let {
            pattern,
            value: rewrite_subblocks(value, fid)?,
        }),
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

/// Walk into compound expressions whose sub-trees can contain blocks
/// (If / Match / While / Quantifier). Leaf-and-non-block expressions
/// are returned untouched.
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
