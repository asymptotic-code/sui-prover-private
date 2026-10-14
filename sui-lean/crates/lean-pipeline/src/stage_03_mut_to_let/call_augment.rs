//! Transform 6: at every call site to a function with `&mut` params,
//! augment the destructure pattern to include the `&mut` arg vars
//! (or convert `Stmt::Eval` to `Stmt::Let`).
//!
//! Pre-pass: collect the `&mut`-param index list for each function.
//! Per-pass: walk each non-native function body and rewrite Calls.

use std::collections::BTreeMap;

use crate::ir::visit::{walk_expr_default, Visitor};
use crate::ir::{Block, BlockTail, Expr, FunId, MatchArm, Program, Stmt, Type, VarId};

use super::Stage3Error;

/// Validate the v1 call-shape contract before stage 3 mutates any body or
/// signature. A call whose callee takes `&mut` may occur only as the complete
/// value of `Stmt::Eval` or `Stmt::Let`; tails and compound/nested expression
/// positions cannot carry the destructuring needed for returned mutations.
pub(super) fn validate_mutating_call_shapes(program: &Program) -> Result<(), Stage3Error> {
    let mut_args = build_mut_arg_map(program);
    for (&fid, function) in &program.functions {
        let mut checker = MutatingCallShapeChecker {
            mut_args: &mut_args,
            invalid: false,
        };
        checker.visit_block(&function.body);
        if checker.invalid {
            return Err(Stage3Error::CallInExpressionPosition { function: fid });
        }
    }
    Ok(())
}

struct MutatingCallShapeChecker<'a> {
    mut_args: &'a BTreeMap<FunId, Vec<usize>>,
    invalid: bool,
}

impl MutatingCallShapeChecker<'_> {
    fn callee_mutates(&self, callee: FunId) -> bool {
        self.mut_args
            .get(&callee)
            .is_some_and(|indices| !indices.is_empty())
    }

    fn visit_statement_value(&mut self, value: &Expr) {
        if let Expr::Call { fun, args, .. } = value {
            if self.callee_mutates(*fun) {
                // The root call is in the one supported position. Its
                // arguments remain expression positions and must not hide a
                // second mutating call.
                for arg in args {
                    self.visit_expr(arg);
                }
                return;
            }
        }
        self.visit_expr(value);
    }
}

impl Visitor for MutatingCallShapeChecker<'_> {
    fn visit_block(&mut self, block: &Block) {
        if self.invalid {
            return;
        }
        for statement in &block.stmts {
            match statement {
                Stmt::Eval(value) | Stmt::Let { value, .. } => {
                    self.visit_statement_value(value);
                }
            }
            if self.invalid {
                return;
            }
        }
        // Every tail payload is an expression position, including a direct
        // `Value(Call(..))`.
        match &block.tail {
            BlockTail::Value(value) => self.visit_expr(value),
            BlockTail::Break { value, .. }
            | BlockTail::Continue { value, .. }
            | BlockTail::Return(value)
            | BlockTail::ReturnFromBlock { value, .. } => self.visit_expr(value),
            BlockTail::Abort { code } => self.visit_expr(code),
        }
    }

    fn visit_expr(&mut self, expression: &Expr) {
        if self.invalid {
            return;
        }
        if let Expr::Call { fun, .. } = expression {
            if self.callee_mutates(*fun) {
                self.invalid = true;
                return;
            }
        }
        walk_expr_default(self, expression);
    }
}

/// Augment call-site destructures for every call to a function with
/// `&mut` params.
pub fn augment_call_sites(program: &mut Program) -> Result<(), Stage3Error> {
    let mut_arg_indices = build_mut_arg_map(program);
    let augmented_arities = build_augmented_arities(program);

    let fids: Vec<FunId> = program.functions.iter().map(|(id, _)| *id).collect();
    for fid in fids {
        let func = program.functions.get_mut(&fid).unwrap();
        rewrite_block(&mut func.body, &mut_arg_indices, &augmented_arities, fid)?;
    }
    Ok(())
}

/// `FunId -> ordered list of `&mut`-param indices`.
/// Built from the param types, which are stable across all stage-3
/// transforms (signatures.rs only touches the return type, not params).
fn build_mut_arg_map(program: &Program) -> BTreeMap<FunId, Vec<usize>> {
    fn mut_param_indices(sig: &crate::ir::Signature) -> Vec<usize> {
        sig.params
            .iter()
            .enumerate()
            .filter_map(|(i, p)| match p.ty {
                Type::MutableRef { .. } => Some(i),
                _ => None,
            })
            .collect()
    }
    let translated = program
        .functions
        .iter()
        .map(|(fid, f)| (*fid, mut_param_indices(&f.signature)));
    let natives = program
        .natives
        .decls
        .iter()
        .map(|(fid, d)| (*fid, mut_param_indices(&d.signature)));
    translated.chain(natives).collect()
}

/// `FunId -> augmented return arity`.
///
/// Used by call-site augmentation to compute `head_count`: how many
/// leading `None` slots to insert before the `&mut`-arg slots in a
/// `Stmt::Eval(Call) -> Stmt::Let` conversion.
///
/// After Transform 4 (`augment_signatures`), every function (native
/// or not) that has `&mut` params has its return_type rewritten to
/// the augmented Tuple shape. So the arity is just the shape of
/// `signature.return_type` -- no native special case.
fn build_augmented_arities(program: &Program) -> BTreeMap<FunId, usize> {
    fn arity_of(rt: &Type) -> usize {
        match rt {
            Type::Tuple(items) => items.len(),
            Type::Unit => 0,
            _ => 1,
        }
    }
    let translated = program
        .functions
        .iter()
        .map(|(fid, f)| (*fid, arity_of(&f.signature.return_type)));
    let natives = program
        .natives
        .decls
        .iter()
        .map(|(fid, d)| (*fid, arity_of(&d.signature.return_type)));
    translated.chain(natives).collect()
}

fn rewrite_block(
    block: &mut Block,
    mut_args: &BTreeMap<FunId, Vec<usize>>,
    arities: &BTreeMap<FunId, usize>,
    fid: FunId,
) -> Result<(), Stage3Error> {
    let stmts = std::mem::take(&mut block.stmts);
    let mut rewritten = Vec::with_capacity(stmts.len());
    for stmt in stmts {
        rewritten.push(rewrite_stmt(stmt, mut_args, arities, fid)?);
    }
    block.stmts = rewritten;
    rewrite_tail(&mut block.tail, mut_args, arities, fid)
}

fn rewrite_stmt(
    stmt: Stmt,
    mut_args: &BTreeMap<FunId, Vec<usize>>,
    arities: &BTreeMap<FunId, usize>,
    fid: FunId,
) -> Result<Stmt, Stage3Error> {
    match stmt {
        Stmt::Eval(Expr::Call {
            fun,
            type_args,
            args,
        }) => {
            let muts = mut_args.get(&fun).map(|v| v.as_slice()).unwrap_or(&[]);
            if muts.is_empty() {
                return Ok(Stmt::Eval(Expr::Call {
                    fun,
                    type_args,
                    args,
                }));
            }
            // The augmented return arity = augmented_arities[fun].
            // head_count = augmented_arity - muts.len() (the number of
            // original return slots that the caller is discarding).
            // Pattern: [None x head_count, Some(mut_arg) x muts.len()].
            let augmented_arity = arities
                .get(&fun)
                .copied()
                .expect("mutating callee has an augmented arity (built for every fn + native)");
            let head_count = augmented_arity.saturating_sub(muts.len());
            let mut new_pattern: Vec<Option<VarId>> = (0..head_count).map(|_| None).collect();
            new_pattern.extend(build_mut_pattern(muts, &args, fid)?);
            Ok(Stmt::Let {
                pattern: new_pattern,
                value: Expr::Call {
                    fun,
                    type_args,
                    args,
                },
            })
        }
        Stmt::Let {
            pattern,
            value:
                Expr::Call {
                    fun,
                    type_args,
                    args,
                },
        } => {
            let muts = mut_args.get(&fun).map(|v| v.as_slice()).unwrap_or(&[]);
            if muts.is_empty() {
                return Ok(Stmt::Let {
                    pattern,
                    value: Expr::Call {
                        fun,
                        type_args,
                        args,
                    },
                });
            }
            if pattern_already_augmented(&pattern, muts, &args) {
                return Ok(Stmt::Let {
                    pattern,
                    value: Expr::Call {
                        fun,
                        type_args,
                        args,
                    },
                });
            }
            let mut new_pattern = pattern;
            let mut_pattern = build_mut_pattern(muts, &args, fid)?;
            new_pattern.extend(mut_pattern);
            Ok(Stmt::Let {
                pattern: new_pattern,
                value: Expr::Call {
                    fun,
                    type_args,
                    args,
                },
            })
        }
        Stmt::Eval(other) => Ok(Stmt::Eval(rewrite_subblocks(
            other, mut_args, arities, fid,
        )?)),
        Stmt::Let { pattern, value } => Ok(Stmt::Let {
            pattern,
            value: rewrite_subblocks(value, mut_args, arities, fid)?,
        }),
    }
}

/// Detect whether a `Stmt::Let { pattern, value: Call(f, args) }` is
/// already in augmented form: the trailing `muts.len()` pattern slots
/// match the arg vars at the corresponding `&mut` param indices.
fn pattern_already_augmented(pattern: &[Option<VarId>], muts: &[usize], args: &[Expr]) -> bool {
    if pattern.len() < muts.len() {
        return false;
    }
    let head_count = pattern.len() - muts.len();
    for (pat_idx, &mut_idx) in (head_count..pattern.len()).zip(muts.iter()) {
        let arg = match args.get(mut_idx) {
            Some(a) => a,
            None => return false,
        };
        let expected_var = match arg {
            Expr::Var(v) => v,
            _ => return false,
        };
        match &pattern[pat_idx] {
            Some(actual_var) if actual_var == expected_var => {}
            _ => return false,
        }
    }
    true
}

fn build_mut_pattern(
    muts: &[usize],
    args: &[Expr],
    fid: FunId,
) -> Result<Vec<Option<VarId>>, Stage3Error> {
    let mut pat: Vec<Option<VarId>> = Vec::with_capacity(muts.len());
    for &mut_idx in muts {
        let arg = args
            .get(mut_idx)
            .ok_or(Stage3Error::CallMutArgOutOfRange { function: fid })?;
        match arg {
            Expr::Var(name) => pat.push(Some(name.clone())),
            _ => return Err(Stage3Error::CallMutArgNonVar { function: fid }),
        }
    }
    Ok(pat)
}

fn rewrite_tail(
    tail: &mut BlockTail,
    mut_args: &BTreeMap<FunId, Vec<usize>>,
    arities: &BTreeMap<FunId, usize>,
    fid: FunId,
) -> Result<(), Stage3Error> {
    match tail {
        BlockTail::Value(e) => {
            let taken = std::mem::replace(e, Expr::Unit);
            *e = rewrite_subblocks(taken, mut_args, arities, fid)?;
        }
        BlockTail::Break { value, .. }
        | BlockTail::Continue { value, .. }
        | BlockTail::Return(value)
        | BlockTail::ReturnFromBlock { value, .. } => {
            let taken = std::mem::replace(&mut **value, Expr::Unit);
            **value = rewrite_subblocks(taken, mut_args, arities, fid)?;
        }
        BlockTail::Abort { code } => {
            let taken = std::mem::replace(&mut **code, Expr::Unit);
            **code = rewrite_subblocks(taken, mut_args, arities, fid)?;
        }
    }
    Ok(())
}

fn rewrite_subblocks(
    expr: Expr,
    mut_args: &BTreeMap<FunId, Vec<usize>>,
    arities: &BTreeMap<FunId, usize>,
    fid: FunId,
) -> Result<Expr, Stage3Error> {
    match expr {
        Expr::If {
            cond,
            mut then_branch,
            mut else_branch,
        } => {
            rewrite_block(&mut then_branch, mut_args, arities, fid)?;
            rewrite_block(&mut else_branch, mut_args, arities, fid)?;
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
                rewrite_block(&mut body, mut_args, arities, fid)?;
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
            rewrite_block(&mut header, mut_args, arities, fid)?;
            rewrite_block(&mut body, mut_args, arities, fid)?;
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
            rewrite_block(&mut body, mut_args, arities, fid)?;
            Ok(Expr::Quantifier {
                kind,
                binder,
                binder_type,
                domain,
                body,
            })
        }
        Expr::Call {
            fun,
            type_args,
            args,
        } => {
            if mut_args.get(&fun).map(|v| !v.is_empty()).unwrap_or(false) {
                return Err(Stage3Error::CallInExpressionPosition { function: fid });
            }
            Ok(Expr::Call {
                fun,
                type_args,
                args,
            })
        }
        Expr::LabeledBlock {
            mut body,
            result_ty,
        } => {
            rewrite_block(&mut body, mut_args, arities, fid)?;
            Ok(Expr::LabeledBlock { body, result_ty })
        }
        other => Ok(other),
    }
}
