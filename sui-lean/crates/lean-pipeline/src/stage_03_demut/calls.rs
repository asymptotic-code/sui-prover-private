//! Call-site rewriting: destructure augmented returns from demoted
//! callees.
//!
//! Phase 3 scope -- standard demotion only:
//!
//! For every `Expr::Call(g, args)` where `g` is in the demotion set
//! AND `g`'s pattern is `DemotionPattern::Standard`, rewrite the
//! enclosing statement so the augmented-return tuple is destructured
//! and each `&mut`-typed arg's caller temp is rebound from its slot.
//!
//! Pattern 4a (self-return) and pattern 4b (sub-field-return) call
//! sites are left structurally unchanged in Phase 3 -- their demoted
//! returns naturally match the consumer's expectations once stage 4
//! lowers the surviving `MutBorrow` / `ReadRef` ops and strips
//! body-local `Type::MutableRef`.
//!
//! Calls live in two stmt positions per stage 2's emission
//! (`translate_op::translate_function_call`):
//!
//! - `Stmt::Eval(Expr::Call(...))` for unit-returning calls
//!   (`dests.len() == 0`).
//! - `Stmt::Let { pattern, value: Expr::Call(...) }` for
//!   value-returning calls (`dests.len() >= 1`).
//!
//! For both positions the rewrite yields a `Stmt::Let { pattern, value: Call }`
//! whose pattern is `<original_pattern> ++ <mut_arg_var_ids>`. Sub-pass
//! C in `plans/lean-pipeline/stage-03-demut.md`.

use crate::ir::{Block, BlockTail, Expr, MatchArm, Program, Stmt, VarId};

use super::demotion_set::DemotionMap;
use super::signatures::DemotionPattern;

/// Rewrite call sites in every non-native function body in `program`.
pub fn rewrite_calls(program: &mut Program, demotion_map: &DemotionMap) {
    for func in program.functions.values_mut() {
        rewrite_block(&mut func.body, demotion_map);
    }
}

fn rewrite_block(block: &mut Block, demotion_map: &DemotionMap) {
    let stmts = std::mem::take(&mut block.stmts);
    block.stmts = stmts
        .into_iter()
        .map(|s| rewrite_stmt(s, demotion_map))
        .collect();
    rewrite_tail(&mut block.tail, demotion_map);
}

fn rewrite_stmt(stmt: Stmt, demotion_map: &DemotionMap) -> Stmt {
    match stmt {
        Stmt::Eval(expr) => match expr {
            Expr::Call {
                fun,
                type_args,
                args,
            } if is_standard_demoted(demotion_map, fun) => {
                let info = demotion_map.info(fun).unwrap();
                build_destructure(fun, type_args, args, Vec::new(), info)
            }
            other => Stmt::Eval(rewrite_expr_subblocks(other, demotion_map)),
        },
        Stmt::Let { pattern, value } => match value {
            Expr::Call {
                fun,
                type_args,
                args,
            } if is_standard_demoted(demotion_map, fun) => {
                let info = demotion_map.info(fun).unwrap();
                build_destructure(fun, type_args, args, pattern, info)
            }
            other => Stmt::Let {
                pattern,
                value: rewrite_expr_subblocks(other, demotion_map),
            },
        },
    }
}

fn rewrite_tail(tail: &mut BlockTail, demotion_map: &DemotionMap) {
    match tail {
        BlockTail::Value(e) => {
            *e = rewrite_expr_subblocks(std::mem::replace(e, Expr::Unit), demotion_map)
        }
        BlockTail::Break { value, .. }
        | BlockTail::Continue { value, .. }
        | BlockTail::Return(value)
        | BlockTail::ReturnFromBlock { value, .. } => {
            **value =
                rewrite_expr_subblocks(std::mem::replace(&mut **value, Expr::Unit), demotion_map);
        }
        BlockTail::Abort { code } => {
            **code =
                rewrite_expr_subblocks(std::mem::replace(&mut **code, Expr::Unit), demotion_map);
        }
    }
}

/// Recurse into any nested `Block`s carried by `expr` (If, Match,
/// While, Quantifier). For Calls in non-stmt positions (e.g. nested
/// inside a BinOp), we leave them alone -- stage 2 emits Calls only
/// at Stmt level, so this is defensive.
fn rewrite_expr_subblocks(expr: Expr, demotion_map: &DemotionMap) -> Expr {
    match expr {
        Expr::If {
            cond,
            mut then_branch,
            mut else_branch,
        } => {
            rewrite_block(&mut then_branch, demotion_map);
            rewrite_block(&mut else_branch, demotion_map);
            Expr::If {
                cond,
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
            selector,
            cases: cases
                .into_iter()
                .map(|arm| {
                    let MatchArm {
                        variant,
                        bindings,
                        mut body,
                    } = arm;
                    rewrite_block(&mut body, demotion_map);
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
            ..
        } => {
            rewrite_block(&mut header, demotion_map);
            rewrite_block(&mut body, demotion_map);
            Expr::While {
                header,
                cond,
                body,
                iter_locals: Vec::new(),
                header_exit_locals: Vec::new(),
                live_out: Vec::new(),
            }
        }
        Expr::Quantifier {
            kind,
            binder,
            binder_type,
            domain,
            mut body,
        } => {
            rewrite_block(&mut body, demotion_map);
            Expr::Quantifier {
                kind,
                binder,
                binder_type,
                domain,
                body,
            }
        }
        other => other,
    }
}

fn is_standard_demoted(demotion_map: &DemotionMap, fid: crate::ir::FunId) -> bool {
    demotion_map
        .info(fid)
        .map(|i| i.pattern == DemotionPattern::Standard)
        .unwrap_or(false)
}

/// Build the augmented-destructure `Stmt::Let`. The new pattern is
/// `original_pattern ++ <mut_arg_var_ids>`. Each mut-arg slot must
/// be a plain `Expr::Var(name)` (per stage 2's emission); other
/// shapes panic.
fn build_destructure(
    fun: crate::ir::FunId,
    type_args: Vec<crate::ir::Type>,
    args: Vec<Expr>,
    orig_pattern: Vec<Option<VarId>>,
    info: &super::demotion_set::FunDemotion,
) -> Stmt {
    let mut pattern = orig_pattern;
    for &idx in &info.mut_param_indices {
        let var_id = match args.get(idx) {
            Some(Expr::Var(v)) => v.clone(),
            Some(other) => {
                panic!(
                    "stage 3 call-site rewrite: arg at &mut position {idx} of fun {fun} is not Expr::Var (got {:?})",
                    other
                );
            }
            None => {
                panic!(
                    "stage 3 call-site rewrite: fun {fun} has &mut param index {idx} but only {} args supplied",
                    args.len()
                );
            }
        };
        pattern.push(Some(var_id));
    }
    Stmt::Let {
        pattern,
        value: Expr::Call {
            fun,
            type_args,
            args,
        },
    }
}
