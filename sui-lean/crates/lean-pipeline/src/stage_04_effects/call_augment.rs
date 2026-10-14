//! Transforms C + D: thread `world` into every Call to a world-needing
//! function and extend the surrounding destructure pattern.
//!
//! Algorithm (per-function walk over each non-native body):
//!
//! 1. **Pre-pass**: build `BTreeMap<FunId, usize>` from each
//!    world-callee's post-Transform-B IR return signature. Native and
//!    translated declarations use the same augmented representation.
//!
//! 2. **Per-stmt rewrite**: for each `Stmt::Eval(Call(f, args))` or
//!    `Stmt::Let { value: Call(f, args) }` where `f` needs World:
//!    - Append `Var(world)` to `args`.
//!    - Adjust the destructure pattern (Stmt::Eval -> Stmt::Let with
//!      `[None x head_count, Some(world)]`; existing Stmt::Let
//!      patterns extended with `Some(world)`).

use std::collections::BTreeMap;

use crate::ir::{Block, BlockTail, Expr, FunId, MatchArm, Program, Stmt, Type, VarId};

use std::collections::BTreeSet;

use super::common::{is_world_callee, world_varid, WORLD_VAR};
use super::Stage4Error;

/// Augment all Calls to world-needing callees inside the bodies of
/// every non-native function in `needs_world`.
pub fn augment_call_sites(
    program: &mut Program,
    needs_world: &BTreeSet<FunId>,
) -> Result<(), Stage4Error> {
    let augmented_arities = build_augmented_arities(program, needs_world);

    // Only rewrite bodies of callers in `needs_world`. Functions
    // outside `needs_world` either are native (no body to rewrite)
    // or have no transitively-GlobalMut callees -- their bodies
    // are already world-free and don't need threading. Critically,
    // this includes `#[ext(pure)]` user helpers whose explicit_pure
    // annotation locked their `Function::effects` at `Effects::PURE`
    // AND which happen to have no GlobalMut descendants -- those
    // stay un-augmented. The complementary case (`#[ext(pure)]`
    // helpers that DO call globally-mutating code) IS in
    // `needs_world` because the call-graph fixpoint sees the
    // GlobalMut descendant; their signature was just augmented, so
    // their body must thread world.
    let fids: Vec<FunId> = needs_world.iter().copied().collect();
    for fid in fids {
        if std::env::var_os("FOXY_DEBUG_PIPELINE_TRACE").is_some() {
            let name = program
                .functions
                .get(&fid)
                .map(|f| f.name.as_str())
                .unwrap_or("<native>");
            eprintln!("[stage-04-effects] augment_call_sites {name}");
        }
        if let Some(func) = program.functions.get_mut(&fid) {
            rewrite_block(&mut func.body, &augmented_arities, fid)?;
        }
    }
    Ok(())
}

/// `FunId -> post-stage-4 augmented return arity for world callees`.
///
/// Non-world callees aren't in the map (caller treats them as
/// "no augmentation needed" via `.get(&fid).copied()`).
///
/// After Transform B (`augment_signatures`), every world-callee
/// (native or not) has its `signature.return_type` rewritten to
/// include the trailing `World` slot. So the arity is just the
/// shape of `signature.return_type` -- no native special case.
fn build_augmented_arities(
    program: &Program,
    needs_world: &BTreeSet<FunId>,
) -> BTreeMap<FunId, usize> {
    let translated = program.functions.iter().filter_map(|(fid, f)| {
        let cref = crate::ir::CalleeRef::Translated(f);
        if !is_world_callee(cref, *fid, needs_world) {
            return None;
        }
        let arity = match &f.signature.return_type {
            Type::Tuple(items) => items.len(),
            Type::Unit => 0,
            _ => 1,
        };
        Some((*fid, arity))
    });
    let natives = program.natives.decls.iter().filter_map(|(fid, d)| {
        let cref = crate::ir::CalleeRef::Native(d);
        if !is_world_callee(cref, *fid, needs_world) {
            return None;
        }
        let arity = match &d.signature.return_type {
            Type::Tuple(items) => items.len(),
            Type::Unit => 0,
            _ => 1,
        };
        Some((*fid, arity))
    });
    translated.chain(natives).collect()
}

fn rewrite_block(
    block: &mut Block,
    arities: &BTreeMap<FunId, usize>,
    fid: FunId,
) -> Result<(), Stage4Error> {
    let stmts = std::mem::take(&mut block.stmts);
    let mut rewritten = Vec::with_capacity(stmts.len());
    for stmt in stmts {
        rewritten.push(rewrite_stmt(stmt, arities, fid)?);
    }
    block.stmts = rewritten;
    rewrite_tail(&mut block.tail, arities, fid)
}

fn rewrite_stmt(
    stmt: Stmt,
    arities: &BTreeMap<FunId, usize>,
    fid: FunId,
) -> Result<Stmt, Stage4Error> {
    match stmt {
        Stmt::Eval(Expr::Call {
            fun,
            type_args,
            args,
        }) => {
            let arity = match arities.get(&fun).copied() {
                Some(a) => a,
                None => {
                    return Ok(Stmt::Eval(Expr::Call {
                        fun,
                        type_args,
                        args,
                    }));
                }
            };
            // Append Var(world) to args.
            let mut new_args = args;
            if !args_already_threaded(&new_args) {
                new_args.push(Expr::Var(world_varid()));
            }
            // Build the destructure pattern: head_count = arity - 1 (the
            // pre-world slots), then Some(world).
            let head_count = arity.saturating_sub(1);
            let mut pattern: Vec<Option<VarId>> = (0..head_count).map(|_| None).collect();
            pattern.push(Some(world_varid()));
            Ok(Stmt::Let {
                pattern,
                value: Expr::Call {
                    fun,
                    type_args,
                    args: new_args,
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
            let arity = match arities.get(&fun).copied() {
                Some(a) => a,
                None => {
                    return Ok(Stmt::Let {
                        pattern,
                        value: Expr::Call {
                            fun,
                            type_args,
                            args,
                        },
                    });
                }
            };
            if pattern_already_world_augmented(&pattern) && args_already_threaded(&args) {
                return Ok(Stmt::Let {
                    pattern,
                    value: Expr::Call {
                        fun,
                        type_args,
                        args,
                    },
                });
            }
            let mut new_args = args;
            if !args_already_threaded(&new_args) {
                new_args.push(Expr::Var(world_varid()));
            }
            // Caller's existing pattern may be shorter than the
            // augmented arity (e.g., caller was Stmt::Let with
            // pattern [Some(ret)] from stage-2 lift, before stage-3
            // mut augmentation; or caller wrote `let _ = f()` so
            // pattern is [None] of length 1). Pad with None entries
            // to match `arity - 1`, then append Some(world).
            let mut new_pattern = pattern;
            let head_count = arity.saturating_sub(1);
            while new_pattern.len() < head_count {
                new_pattern.push(None);
            }
            new_pattern.push(Some(world_varid()));
            // Suppress unused warning -- consumed by callers that
            // mutate `pattern` to extend it.
            let _ = fid;
            Ok(Stmt::Let {
                pattern: new_pattern,
                value: Expr::Call {
                    fun,
                    type_args,
                    args: new_args,
                },
            })
        }
        // DF writeback marked world-threaded by route_df_to_world:
        // thread `world` exactly like a world-returning call -- append a
        // trailing `world` slot to the destructure pattern. The
        // WriteBack already carries `world: Some(world_varid())` as its
        // world input; the renderer emits the World store producing
        // `(object_unchanged, world)`. stage-5 SSA then versions both
        // slots like any other multi-slot let.
        Stmt::Let { mut pattern, value }
            if matches!(&value, Expr::WriteBack { world: Some(_), .. }) =>
        {
            if !pattern_already_world_augmented(&pattern) {
                pattern.push(Some(world_varid()));
            }
            Ok(Stmt::Let { pattern, value })
        }
        Stmt::Eval(other) => Ok(Stmt::Eval(rewrite_subblocks(other, arities, fid)?)),
        Stmt::Let { pattern, value } => Ok(Stmt::Let {
            pattern,
            value: rewrite_subblocks(value, arities, fid)?,
        }),
    }
}

fn args_already_threaded(args: &[Expr]) -> bool {
    args.last()
        .map(|a| matches!(a, Expr::Var(v) if v.as_ref() == WORLD_VAR))
        .unwrap_or(false)
}

fn pattern_already_world_augmented(pattern: &[Option<VarId>]) -> bool {
    pattern
        .last()
        .map(|p| matches!(p, Some(v) if v.as_ref() == WORLD_VAR))
        .unwrap_or(false)
}

fn rewrite_tail(
    tail: &mut BlockTail,
    arities: &BTreeMap<FunId, usize>,
    fid: FunId,
) -> Result<(), Stage4Error> {
    match tail {
        BlockTail::Value(e) => {
            let taken = std::mem::replace(e, Expr::Unit);
            *e = rewrite_subblocks(taken, arities, fid)?;
        }
        BlockTail::Break { value, .. }
        | BlockTail::Continue { value, .. }
        | BlockTail::Return(value)
        | BlockTail::ReturnFromBlock { value, .. } => {
            let taken = std::mem::replace(&mut **value, Expr::Unit);
            **value = rewrite_subblocks(taken, arities, fid)?;
        }
        BlockTail::Abort { code } => {
            let taken = std::mem::replace(&mut **code, Expr::Unit);
            **code = rewrite_subblocks(taken, arities, fid)?;
        }
    }
    Ok(())
}

fn rewrite_subblocks(
    expr: Expr,
    arities: &BTreeMap<FunId, usize>,
    fid: FunId,
) -> Result<Expr, Stage4Error> {
    match expr {
        Expr::If {
            cond,
            mut then_branch,
            mut else_branch,
        } => {
            rewrite_block(&mut then_branch, arities, fid)?;
            rewrite_block(&mut else_branch, arities, fid)?;
            Ok(Expr::If {
                cond: Box::new(rewrite_subblocks(*cond, arities, fid)?),
                then_branch,
                else_branch,
            })
        }
        Expr::Match {
            struct_id,
            selector,
            cases,
        } => {
            let mut new_cases = Vec::with_capacity(cases.len());
            for arm in cases {
                let MatchArm {
                    variant,
                    bindings,
                    mut body,
                } = arm;
                rewrite_block(&mut body, arities, fid)?;
                new_cases.push(MatchArm {
                    variant,
                    bindings,
                    body,
                });
            }
            Ok(Expr::Match {
                struct_id,
                selector: Box::new(rewrite_subblocks(*selector, arities, fid)?),
                cases: new_cases,
            })
        }
        Expr::While {
            mut header,
            cond,
            mut body,
            iter_locals,
            header_exit_locals,
            live_out,
        } => {
            rewrite_block(&mut header, arities, fid)?;
            rewrite_block(&mut body, arities, fid)?;
            let iter_locals = iter_locals
                .into_iter()
                .map(|(var, initial)| Ok((var, rewrite_subblocks(initial, arities, fid)?)))
                .collect::<Result<Vec<_>, Stage4Error>>()?;
            Ok(Expr::While {
                header,
                cond: Box::new(rewrite_subblocks(*cond, arities, fid)?),
                body,
                iter_locals,
                header_exit_locals,
                live_out,
            })
        }
        Expr::Quantifier {
            kind,
            binder,
            binder_type,
            domain,
            mut body,
        } => {
            // Quantifier bodies are pure LOGICAL predicates, but a
            // predicate can call a world-threaded function -- e.g.
            // `forall addr, acl_permission_unchanged(addr, ..)` where the
            // predicate reads a `LinkedTable` (df-backed -> world). The
            // world inside a quantifier is FIXED and read-only (a
            // quantifier does not sequence world mutations), so each such
            // call applies the enclosing world and projects the value,
            // discarding the returned world. We hoist the call into a
            // `let (v, _) := f(.. , world)` inside the body and use `v`
            // (the IR has no tuple-projection expr, so a destructure is
            // the only way to drop the world slot). collect_let_stmts is
            // taught not to lift these body-local lets into the companion
            // prelude. `world_varid()` is the fixed pre-SSA world var;
            // stage-5 SSA resolves it to the world live at the
            // quantifier's position.
            thread_world_in_quantifier_body(&mut body, &binder, arities)?;
            Ok(Expr::Quantifier {
                kind,
                binder,
                binder_type,
                domain: rewrite_quant_domain(domain, arities, fid)?,
                body,
            })
        }
        Expr::Call {
            fun,
            type_args,
            args,
        } => {
            // A Call to a world-needing callee in a compound expression
            // position can't be augmented locally -- the surrounding
            // expression context doesn't have a Stmt to attach a
            // destructure pattern to. Stage 2's bytecode lift should
            // hoist these into named temps; if one slips through,
            // reject.
            if arities.contains_key(&fun) {
                return Err(Stage4Error::CallInExpressionPosition { function: fid });
            }
            // Recurse into args to detect world-needing Calls buried deeper.
            let mut new_args = Vec::with_capacity(args.len());
            for a in args {
                new_args.push(rewrite_subblocks(a, arities, fid)?);
            }
            Ok(Expr::Call {
                fun,
                type_args,
                args: new_args,
            })
        }
        Expr::Tuple(items) => {
            let mut out = Vec::with_capacity(items.len());
            for item in items {
                out.push(rewrite_subblocks(item, arities, fid)?);
            }
            Ok(Expr::Tuple(out))
        }
        Expr::Pack {
            struct_id,
            type_args,
            variant,
            fields,
        } => {
            let mut out = Vec::with_capacity(fields.len());
            for f in fields {
                out.push(rewrite_subblocks(f, arities, fid)?);
            }
            Ok(Expr::Pack {
                struct_id,
                type_args,
                variant,
                fields: out,
            })
        }
        Expr::BinOp { op, lhs, rhs } => Ok(Expr::BinOp {
            op,
            lhs: Box::new(rewrite_subblocks(*lhs, arities, fid)?),
            rhs: Box::new(rewrite_subblocks(*rhs, arities, fid)?),
        }),
        Expr::UnOp { op, operand } => Ok(Expr::UnOp {
            op,
            operand: Box::new(rewrite_subblocks(*operand, arities, fid)?),
        }),
        Expr::BitOp(op) => Ok(Expr::BitOp(match op {
            crate::ir::BitOp::Extract { operand, high, low } => crate::ir::BitOp::Extract {
                operand: Box::new(rewrite_subblocks(*operand, arities, fid)?),
                high,
                low,
            },
            crate::ir::BitOp::ZeroExtend { operand, bits } => crate::ir::BitOp::ZeroExtend {
                operand: Box::new(rewrite_subblocks(*operand, arities, fid)?),
                bits,
            },
            crate::ir::BitOp::SignExtend { operand, bits } => crate::ir::BitOp::SignExtend {
                operand: Box::new(rewrite_subblocks(*operand, arities, fid)?),
                bits,
            },
            crate::ir::BitOp::Concat { high, low } => crate::ir::BitOp::Concat {
                high: Box::new(rewrite_subblocks(*high, arities, fid)?),
                low: Box::new(rewrite_subblocks(*low, arities, fid)?),
            },
        })),
        Expr::Field {
            struct_id,
            field_index,
            base,
        } => Ok(Expr::Field {
            struct_id,
            field_index,
            base: Box::new(rewrite_subblocks(*base, arities, fid)?),
        }),
        Expr::Borrow { mut step, base } => {
            for op in step.exprs_mut() {
                let owned = std::mem::replace(op, Expr::Unit);
                *op = rewrite_subblocks(owned, arities, fid)?;
            }
            Ok(Expr::Borrow {
                step,
                base: Box::new(rewrite_subblocks(*base, arities, fid)?),
            })
        }
        Expr::Update {
            mut step,
            base,
            value,
        } => {
            for op in step.exprs_mut() {
                let owned = std::mem::replace(op, Expr::Unit);
                *op = rewrite_subblocks(owned, arities, fid)?;
            }
            Ok(Expr::Update {
                step,
                base: Box::new(rewrite_subblocks(*base, arities, fid)?),
                value: Box::new(rewrite_subblocks(*value, arities, fid)?),
            })
        }
        Expr::Unpack {
            struct_id,
            variant,
            value,
        } => Ok(Expr::Unpack {
            struct_id,
            variant,
            value: Box::new(rewrite_subblocks(*value, arities, fid)?),
        }),
        Expr::ReadRef(inner) => Ok(Expr::ReadRef(Box::new(rewrite_subblocks(
            *inner, arities, fid,
        )?))),
        Expr::WriteRef { reference, value } => Ok(Expr::WriteRef {
            reference: Box::new(rewrite_subblocks(*reference, arities, fid)?),
            value: Box::new(rewrite_subblocks(*value, arities, fid)?),
        }),
        Expr::ToProp(inner) => Ok(Expr::ToProp(Box::new(rewrite_subblocks(
            *inner, arities, fid,
        )?))),
        Expr::ToBool(inner) => Ok(Expr::ToBool(Box::new(rewrite_subblocks(
            *inner, arities, fid,
        )?))),
        Expr::LabeledBlock {
            mut body,
            result_ty,
        } => {
            rewrite_block(&mut body, arities, fid)?;
            Ok(Expr::LabeledBlock { body, result_ty })
        }
        Expr::Var(var) => Ok(Expr::Var(var)),
        Expr::Const(value) => Ok(Expr::Const(value)),
        Expr::Unit => Ok(Expr::Unit),
        Expr::BorrowLoc(var) => Ok(Expr::BorrowLoc(var)),
        Expr::BorrowGlobal(global) => Ok(Expr::BorrowGlobal(global)),
        Expr::WriteBack {
            node,
            edge,
            child,
            world,
        } => Ok(Expr::WriteBack {
            node,
            edge,
            child,
            world,
        }),
        Expr::IsParent { node, edge, child } => Ok(Expr::IsParent { node, edge, child }),
    }
}

fn rewrite_quant_domain(
    domain: crate::ir::QuantDomain,
    arities: &BTreeMap<FunId, usize>,
    fid: FunId,
) -> Result<crate::ir::QuantDomain, Stage4Error> {
    Ok(match domain {
        crate::ir::QuantDomain::Unbounded => crate::ir::QuantDomain::Unbounded,
        crate::ir::QuantDomain::Range { start, end } => crate::ir::QuantDomain::Range {
            start: Box::new(rewrite_subblocks(*start, arities, fid)?),
            end: Box::new(rewrite_subblocks(*end, arities, fid)?),
        },
        crate::ir::QuantDomain::VecRange { vec, start, end } => crate::ir::QuantDomain::VecRange {
            vec: Box::new(rewrite_subblocks(*vec, arities, fid)?),
            start: Box::new(rewrite_subblocks(*start, arities, fid)?),
            end: Box::new(rewrite_subblocks(*end, arities, fid)?),
        },
        crate::ir::QuantDomain::Collection(collection) => crate::ir::QuantDomain::Collection(
            Box::new(rewrite_subblocks(*collection, arities, fid)?),
        ),
    })
}

/// Thread the fixed enclosing world into world-threaded calls inside a
/// quantifier body, projecting the value and discarding the returned
/// world. See the `Expr::Quantifier` arm of `rewrite_subblocks`. The body
/// is a Bool predicate (validator enforces a `Value` tail).
fn thread_world_in_quantifier_body(
    body: &mut Block,
    binder: &VarId,
    arities: &BTreeMap<FunId, usize>,
) -> Result<(), Stage4Error> {
    let mut idx = 0usize;
    thread_world_in_snapshot_block(body, binder, &mut idx, arities);
    Ok(())
}

fn thread_world_in_snapshot_block(
    block: &mut Block,
    binder: &VarId,
    idx: &mut usize,
    arities: &BTreeMap<FunId, usize>,
) {
    let mut rewritten = Vec::with_capacity(block.stmts.len());
    for mut stmt in std::mem::take(&mut block.stmts) {
        let mut prelude = Vec::new();
        match &mut stmt {
            Stmt::Let {
                pattern,
                value:
                    Expr::Call {
                        fun,
                        type_args: _,
                        args,
                    },
            } if arities.contains_key(fun) => {
                for argument in args.iter_mut() {
                    hoist_world_calls(argument, &mut prelude, binder, idx, arities);
                }
                if !args_already_threaded(args) {
                    args.push(Expr::Var(world_varid()));
                }
                let head_count = arities[fun].saturating_sub(1);
                while pattern.len() < head_count {
                    pattern.push(None);
                }
                if pattern.len() == head_count {
                    pattern.push(None);
                } else if let Some(world_slot) = pattern.get_mut(head_count) {
                    *world_slot = None;
                }
            }
            Stmt::Eval(Expr::Call { fun, args, .. }) if arities.contains_key(fun) => {
                for argument in args.iter_mut() {
                    hoist_world_calls(argument, &mut prelude, binder, idx, arities);
                }
                if !args_already_threaded(args) {
                    args.push(Expr::Var(world_varid()));
                }
            }
            Stmt::Let { value, .. } | Stmt::Eval(value) => {
                hoist_world_calls(value, &mut prelude, binder, idx, arities);
            }
        }
        rewritten.extend(prelude);
        rewritten.push(stmt);
    }

    let tail_expr = match &mut block.tail {
        BlockTail::Value(expr) => expr,
        BlockTail::Break { value, .. }
        | BlockTail::Continue { value, .. }
        | BlockTail::Return(value)
        | BlockTail::ReturnFromBlock { value, .. } => value,
        BlockTail::Abort { code } => code,
    };
    let mut tail_prelude = Vec::new();
    hoist_world_calls(tail_expr, &mut tail_prelude, binder, idx, arities);
    rewritten.extend(tail_prelude);
    block.stmts = rewritten;
}

/// Recursively hoist world-threaded `Call`s in a quantifier-body
/// expression into `let (v.., _) := f(.. , world)` statements appended to
/// `prelude`, replacing each call with its projected value var(s). Pure
/// calls and other exprs are traversed for nested world-threaded calls.
/// Fresh var names derive from the quantifier binder (unique per
/// quantifier) + a local index, so they reach stage-5 SSA without
/// colliding.
fn hoist_world_calls(
    e: &mut Expr,
    prelude: &mut Vec<Stmt>,
    binder: &VarId,
    idx: &mut usize,
    arities: &BTreeMap<FunId, usize>,
) {
    match e {
        Expr::Call { fun, args, .. } => {
            let arity = arities.get(fun).copied();
            for a in args.iter_mut() {
                hoist_world_calls(a, prelude, binder, idx, arities);
            }
            let Some(arity) = arity else {
                return;
            };
            let taken = std::mem::replace(e, Expr::Unit);
            let Expr::Call {
                fun,
                type_args,
                mut args,
            } = taken
            else {
                unreachable!("matched Expr::Call above")
            };
            if !args_already_threaded(&args) {
                args.push(Expr::Var(world_varid()));
            }
            let head_count = arity.saturating_sub(1);
            let vnames: Vec<VarId> = (0..head_count)
                .map(|j| VarId::from(format!("{}__qw{}_{}", binder.as_ref(), *idx, j).as_str()))
                .collect();
            *idx += 1;
            let call = Expr::Call {
                fun,
                type_args,
                args,
            };
            if vnames.is_empty() {
                prelude.push(Stmt::Eval(call));
            } else {
                let mut pattern: Vec<Option<VarId>> = vnames.iter().cloned().map(Some).collect();
                pattern.push(None);
                prelude.push(Stmt::Let {
                    pattern,
                    value: call,
                });
            }
            *e = match vnames.len() {
                0 => Expr::Unit,
                1 => Expr::Var(vnames.into_iter().next().unwrap()),
                _ => Expr::Tuple(vnames.into_iter().map(Expr::Var).collect()),
            };
        }
        Expr::BinOp { lhs, rhs, .. } => {
            hoist_world_calls(lhs, prelude, binder, idx, arities);
            hoist_world_calls(rhs, prelude, binder, idx, arities);
        }
        Expr::UnOp { operand, .. } => hoist_world_calls(operand, prelude, binder, idx, arities),
        Expr::Tuple(items) => {
            for it in items.iter_mut() {
                hoist_world_calls(it, prelude, binder, idx, arities);
            }
        }
        Expr::Pack { fields, .. } => {
            for field in fields {
                hoist_world_calls(field, prelude, binder, idx, arities);
            }
        }
        Expr::Unpack { value, .. }
        | Expr::Field { base: value, .. }
        | Expr::ReadRef(value)
        | Expr::ToProp(value)
        | Expr::ToBool(value) => hoist_world_calls(value, prelude, binder, idx, arities),
        Expr::BitOp(op) => match op {
            crate::ir::BitOp::Extract { operand, .. }
            | crate::ir::BitOp::ZeroExtend { operand, .. }
            | crate::ir::BitOp::SignExtend { operand, .. } => {
                hoist_world_calls(operand, prelude, binder, idx, arities);
            }
            crate::ir::BitOp::Concat { high, low } => {
                hoist_world_calls(high, prelude, binder, idx, arities);
                hoist_world_calls(low, prelude, binder, idx, arities);
            }
        },
        Expr::If {
            cond,
            then_branch,
            else_branch,
        } => {
            hoist_world_calls(cond, prelude, binder, idx, arities);
            thread_world_in_snapshot_block(then_branch, binder, idx, arities);
            thread_world_in_snapshot_block(else_branch, binder, idx, arities);
        }
        Expr::Match {
            selector, cases, ..
        } => {
            hoist_world_calls(selector, prelude, binder, idx, arities);
            for arm in cases {
                thread_world_in_snapshot_block(&mut arm.body, binder, idx, arities);
            }
        }
        Expr::While {
            header,
            cond,
            body,
            iter_locals,
            ..
        } => {
            for (_, initial) in iter_locals {
                hoist_world_calls(initial, prelude, binder, idx, arities);
            }
            thread_world_in_snapshot_block(header, binder, idx, arities);
            let mut cond_prelude = Vec::new();
            hoist_world_calls(cond, &mut cond_prelude, binder, idx, arities);
            header.stmts.extend(cond_prelude);
            thread_world_in_snapshot_block(body, binder, idx, arities);
        }
        Expr::Borrow { step, base } => {
            for operand in step.exprs_mut() {
                hoist_world_calls(operand, prelude, binder, idx, arities);
            }
            hoist_world_calls(base, prelude, binder, idx, arities);
        }
        Expr::Update { step, base, value } => {
            for operand in step.exprs_mut() {
                hoist_world_calls(operand, prelude, binder, idx, arities);
            }
            hoist_world_calls(base, prelude, binder, idx, arities);
            hoist_world_calls(value, prelude, binder, idx, arities);
        }
        Expr::WriteRef { reference, value } => {
            hoist_world_calls(reference, prelude, binder, idx, arities);
            hoist_world_calls(value, prelude, binder, idx, arities);
        }
        Expr::LabeledBlock { body, .. } => {
            thread_world_in_snapshot_block(body, binder, idx, arities);
        }
        Expr::Quantifier {
            binder: nested_binder,
            domain,
            body,
            ..
        } => {
            hoist_world_calls_in_quant_domain(domain, prelude, binder, idx, arities);
            thread_world_in_snapshot_block(body, nested_binder, idx, arities);
        }
        Expr::Var(_)
        | Expr::Const(_)
        | Expr::Unit
        | Expr::BorrowLoc(_)
        | Expr::BorrowGlobal(_)
        | Expr::WriteBack { .. }
        | Expr::IsParent { .. } => {}
    }
}

fn hoist_world_calls_in_quant_domain(
    domain: &mut crate::ir::QuantDomain,
    prelude: &mut Vec<Stmt>,
    binder: &VarId,
    idx: &mut usize,
    arities: &BTreeMap<FunId, usize>,
) {
    match domain {
        crate::ir::QuantDomain::Unbounded => {}
        crate::ir::QuantDomain::Range { start, end } => {
            hoist_world_calls(start, prelude, binder, idx, arities);
            hoist_world_calls(end, prelude, binder, idx, arities);
        }
        crate::ir::QuantDomain::VecRange { vec, start, end } => {
            hoist_world_calls(vec, prelude, binder, idx, arities);
            hoist_world_calls(start, prelude, binder, idx, arities);
            hoist_world_calls(end, prelude, binder, idx, arities);
        }
        crate::ir::QuantDomain::Collection(collection) => {
            hoist_world_calls(collection, prelude, binder, idx, arities);
        }
    }
}
