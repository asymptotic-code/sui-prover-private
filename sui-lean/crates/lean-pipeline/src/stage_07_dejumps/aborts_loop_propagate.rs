//! Stage 7 (rewrite) phase 3a.5 -- propagate loop aborts in `.aborts`
//! variants.
//!
//! `loop_extract` (phase 3a) splits an `Expr::While` into `while_N`
//! (LoopBody) + `while_N.after` (LoopAfter) helpers whose return type is
//! the loop's *accumulator* (the live-out value the loop threads). For a
//! `.aborts` variant whose loop body can abort, that is wrong: the body
//! contains an abort exit (a `Return(Aborted)` callee-aborts splice, or a
//! source `Abort` not yet converted to `Return` at this stage), so the
//! helper must return `AbortResult`, not the accumulator. Because the
//! helper isn't `AbortResult`-typed, `return_lift` (phase 3b, gated on
//! `Option<MoveAbortCode>` returns) skips it and the inner abort renders
//! as a type-mismatched `if`-arm value (cetus-clmm `Position.lean`, every
//! `.aborts` fn with an aborting loop).
//!
//! This pass, between `loop_extract` and `return_lift`, converts the
//! aborting loop slots of each `.aborts` parent:
//!   1. `while_N` / `while_N.after` return `AbortResult`.
//!   2. `while_N.after`'s `Value(accumulator)` tail becomes `NoAbort`
//!      (the loop exited without aborting).
//!   3. the parent's loop-call consumption (`let v = <if .. while_N ..>;
//!      <NoAbort tail>`) is rewritten so non-loop arms deliver `NoAbort`
//!      and the function tail becomes
//!      `match v { NoAbort => <orig NoAbort tail>, Aborted _ => v }`,
//!      propagating the loop's abort verdict.
//! `return_lift` then lifts `while_N`'s inner abort returns normally.
//!
//! Strictly guarded: a slot is converted only when (a) `while_N`'s body
//! has an abort exit, (b) `while_N.after` is the trivial exit form (a
//! `Value` tail with no post-loop Return/Abort), and (c) the parent body
//! matches the propagatable shape with the loop result otherwise dead.
//! Any slot that doesn't match is left exactly as-is -- abort-free loops
//! and unusual shapes are untouched, so this cannot regress
//! currently-passing `.aborts` loops.

use std::collections::{BTreeMap, BTreeSet};

use crate::ir::analysis::free_vars::free_vars_of_expr;
use crate::ir::function::{FunctionKind, SpecKind};
use crate::ir::visit::{walk_block_mut_default, MutVisitor};
use crate::ir::{Block, BlockTail, Expr, FunId, MatchArm, Program, Stmt, VarId};

use super::aborts_variant::AbortsMap;
use super::option_aborts::{ensure_aborts_types, OPTION_NONE_TAG, OPTION_SOME_TAG};
use super::Stage7Error;

pub fn run(program: &mut Program, aborts_map: &AbortsMap) -> Result<(), Stage7Error> {
    let types = ensure_aborts_types(program);
    let option_id = types.option;
    let abort_result_ty = types.option_abort_code_type();
    let no_abort = || Expr::Pack {
        struct_id: option_id,
        type_args: vec![types.abort_code_type()],
        variant: Some(OPTION_NONE_TAG),
        fields: vec![],
    };

    let aborts_parents: Vec<FunId> = program
        .functions
        .iter()
        .filter(|(_, f)| {
            matches!(
                f.kind,
                FunctionKind::Spec {
                    kind: SpecKind::Aborts,
                    ..
                }
            )
        })
        .map(|(id, _)| *id)
        .collect();

    for parent_fid in aborts_parents {
        // SSA copies at branch exits can hide a loop's tail call behind
        // `let result = if ...; let copy = result; copy`. Expose that same
        // value before checking whether the abort companion discards it.
        let scalar_vars = super::aborts_variant::collect_function_var_types(
            &program.functions[&parent_fid],
            program,
        )
        .into_iter()
        .filter_map(|(var, ty)| {
            matches!(
                ty,
                crate::ir::Type::Bool
                    | crate::ir::Type::Prop
                    | crate::ir::Type::UInt(_)
                    | crate::ir::Type::Address
            )
            .then_some(var)
        })
        .collect();
        TailBindings { scalar_vars }
            .visit_block_mut(&mut program.functions.get_mut(&parent_fid).unwrap().body);
        // Group this parent's loop helpers by slot.
        let mut slots: BTreeMap<u32, (Option<FunId>, Option<FunId>)> = BTreeMap::new();
        for (fid, f) in program.functions.iter() {
            match f.kind {
                FunctionKind::LoopBody { parent, slot } if parent == parent_fid => {
                    slots.entry(slot).or_default().0 = Some(*fid);
                }
                FunctionKind::LoopAfter { parent, slot } if parent == parent_fid => {
                    slots.entry(slot).or_default().1 = Some(*fid);
                }
                _ => {}
            }
        }

        // Later loops may be the no-abort continuation of an earlier loop.
        // Retype the tail of the chain first so the preceding `.after` body
        // becomes inferably AbortResult-typed.
        for (_slot, (while_opt, after_opt)) in slots.into_iter().rev() {
            let (Some(while_fid), Some(after_fid)) = (while_opt, after_opt) else {
                continue;
            };
            // Guard A: while_N must contain an abort exit -- a `Return`
            // (callee-aborts splice) or an `Abort` (a source `abort` not
            // yet converted to `Return` at this pre-return_lift stage).
            // Abort-free loops keep the accumulator return type.
            let while_body = &program.functions.get(&while_fid).unwrap().body;
            if !block_has_return_or_abort(while_body)
                && !super::postcondition::collect_callees(while_body)
                    .iter()
                    .any(|callee| {
                        aborts_map.contains_key(callee)
                            && super::aborts_variant::callee_can_abort(program, *callee)
                    })
            {
                continue;
            }
            // Guard B: while_N.after must be the trivial exit form -- a
            // `Value` tail with no post-loop Return/Abort to drop.
            let after_already_abort_result = {
                let after = program.functions.get(&after_fid).unwrap();
                let result = block_delivers_abort_result(
                    &after.body,
                    program,
                    types.option,
                    types.abort_code,
                );
                if !matches!(after.body.tail, BlockTail::Value(_))
                    || (block_has_return_or_abort(&after.body) && !result)
                {
                    continue;
                }
                result
            };

            // Guard C0: the retype below is per-FUNCTION, but every
            // liveness check here is per-CALL-SITE. `try_propagate`
            // clears exactly one consumption, and the Err path below
            // searches the program for one more; neither looks at the
            // REST of the program. A loop consumed twice -- once with a
            // dead result, once live -- was therefore retyped to
            // AbortResult while the live consumer went on binding it as
            // the accumulator, producing an `if` whose arms are the
            // accumulator and an AbortResult.
            //
            // `mmt_v3::tick::update` is exactly that shape: the loop
            // result reaches `cont_0`, which hands it to its own
            // continuation. Refuse the whole slot when any consumer
            // still reads the accumulator -- the documented contract is
            // that a slot which does not match is left exactly as-is.
            if loop_result_read_anywhere(program, while_fid) {
                continue;
            }

            // Guard C + rewrite (3): try to propagate in the parent body.
            // Done first so a shape mismatch skips the slot WITHOUT having
            // mutated the helpers.
            let parent_body = std::mem::replace(
                &mut program.functions.get_mut(&parent_fid).unwrap().body,
                Block {
                    stmts: vec![],
                    tail: BlockTail::Value(Expr::Unit),
                },
            );
            match try_propagate(parent_body, while_fid, option_id, &no_abort) {
                Ok(new_body) => {
                    program.functions.get_mut(&parent_fid).unwrap().body = new_body;
                    // (1) retype while_N -- return_lift then lifts its
                    // inner abort returns.
                    program
                        .functions
                        .get_mut(&while_fid)
                        .unwrap()
                        .signature
                        .return_type = abort_result_ty.clone();
                    // (1) + (2) retype while_N.after + NoAbort tail.
                    let after = program.functions.get_mut(&after_fid).unwrap();
                    after.signature.return_type = abort_result_ty.clone();
                    if !after_already_abort_result {
                        after.body.tail = BlockTail::Value(no_abort());
                    }
                }
                Err(orig) => {
                    program.functions.get_mut(&parent_fid).unwrap().body = orig;
                    // In a chained-loop source, extraction places the next
                    // loop's consumption in the preceding loop's `.after`
                    // helper rather than in the root abort companion. Find
                    // that unique consumer and guard its remainder there.
                    let consumer = program
                        .functions
                        .keys()
                        .copied()
                        .filter(|fid| {
                            *fid != parent_fid
                                && *fid != after_fid
                                && !matches!(
                                    program.functions[fid].kind,
                                    FunctionKind::LoopBody { .. }
                                )
                        })
                        .find_map(|fid| {
                            let candidate = program.functions[&fid].body.clone();
                            try_propagate(candidate, while_fid, option_id, &no_abort)
                                .ok()
                                .map(|body| (fid, body))
                        });
                    if let Some((consumer_fid, consumer_body)) = consumer {
                        program.functions.get_mut(&consumer_fid).unwrap().body = consumer_body;
                        program
                            .functions
                            .get_mut(&while_fid)
                            .unwrap()
                            .signature
                            .return_type = abort_result_ty.clone();
                        let after = program.functions.get_mut(&after_fid).unwrap();
                        after.signature.return_type = abort_result_ty.clone();
                        if !after_already_abort_result {
                            after.body.tail = BlockTail::Value(no_abort());
                        }
                    }
                }
            }
        }
    }
    Ok(())
}

// State and aggregate values retain their bindings so World arguments stay in ANF.
struct TailBindings {
    scalar_vars: BTreeSet<VarId>,
}

#[cfg(test)]
mod tail_binding_tests {
    use super::*;

    #[test]
    fn state_returning_call_keeps_its_named_binding() {
        let world = VarId::from("world");
        let mut body = Block {
            stmts: vec![Stmt::Let {
                pattern: vec![Some(world.clone())],
                value: Expr::Call {
                    fun: 42,
                    type_args: vec![],
                    args: vec![],
                },
            }],
            tail: BlockTail::Value(Expr::Var(world)),
        };
        let original = body.clone();
        TailBindings {
            scalar_vars: BTreeSet::new(),
        }
        .visit_block_mut(&mut body);
        assert_eq!(
            body, original,
            "World results must stay named before continuation lifting"
        );
    }

    #[test]
    fn discarded_nested_loop_result_propagates_through_ssa_copies() {
        let var = |name: &str| VarId::from(name);
        let call = Expr::Call {
            fun: 42,
            type_args: vec![],
            args: vec![],
        };
        let nested = Block {
            stmts: vec![
                Stmt::Let {
                    pattern: vec![Some(var("result"))],
                    value: call,
                },
                Stmt::Let {
                    pattern: vec![Some(var("copy"))],
                    value: Expr::Var(var("result")),
                },
            ],
            tail: BlockTail::Value(Expr::Var(var("copy"))),
        };
        let mut body = Block {
            stmts: vec![Stmt::Let {
                pattern: vec![Some(var("discarded"))],
                value: Expr::If {
                    cond: Box::new(Expr::Const(crate::ir::ty::Const::Bool(true))),
                    then_branch: Box::new(nested),
                    else_branch: Box::new(Block {
                        stmts: vec![],
                        tail: BlockTail::Value(Expr::Const(crate::ir::ty::Const::Bool(false))),
                    }),
                },
            }],
            tail: BlockTail::Value(Expr::Unit),
        };
        TailBindings {
            scalar_vars: [var("result"), var("copy")].into_iter().collect(),
        }
        .visit_block_mut(&mut body);
        let rewritten = try_propagate(body, 42, 7, &|| Expr::Unit)
            .expect("discarded SSA copies must not hide the loop verdict");
        assert!(matches!(
            rewritten.tail,
            BlockTail::Value(Expr::Match { struct_id: 7, .. })
        ));
        let Stmt::Let {
            value:
                Expr::If {
                    then_branch,
                    else_branch,
                    ..
                },
            ..
        } = &rewritten.stmts[0]
        else {
            panic!("loop consumption retained");
        };
        assert!(matches!(
            then_branch.tail,
            BlockTail::Value(Expr::Call { fun: 42, .. })
        ));
        assert!(matches!(else_branch.tail, BlockTail::Value(Expr::Unit)));
    }
}

impl MutVisitor for TailBindings {
    fn visit_block_mut(&mut self, block: &mut Block) {
        walk_block_mut_default(self, block);
        loop {
            let BlockTail::Value(Expr::Var(tail_var)) = &block.tail else {
                break;
            };
            let Some(Stmt::Let { pattern, .. }) = block.stmts.last() else {
                break;
            };
            if pattern.as_slice() != [Some(tail_var.clone())]
                || !self.scalar_vars.contains(tail_var)
            {
                break;
            }
            let Some(Stmt::Let { value, .. }) = block.stmts.pop() else {
                unreachable!();
            };
            block.tail = BlockTail::Value(value);
        }
    }
}

/// True iff any function still binds `while_fid`'s result and reads it
/// afterwards, i.e. consumes the loop's ACCUMULATOR as a value.
///
/// Retyping `while_fid` to `AbortResult` is sound only once no such
/// consumer remains. The retype is per-function while the rewrites are
/// per-call-site, so this walks every body AND every nested block: the
/// offending consumption in `mmt_v3::tick::update` sits inside an `if`
/// arm inside a `match` arm, not at a body's top level.
///
/// The binder ARITY is not part of the question. A loop that threads the
/// World returns `(accumulator.., World)`, so its consumer destructures --
/// `let (acc, world) := while_N(..)` -- and an arity-1 test walked past
/// every one of them. scallop `borrow::assert_isolated_asset` is that
/// shape: two sibling loops in the arms of an `if`, one destructuring
/// `let`, and a post-loop `if acc { .. } else { abort .. }` reading the
/// accumulator. Both slots were converted, both `.after` helpers were
/// deadened to an unconditional `NoAbort`, and the abort condition
/// `unable_to_borrow_other_coin_with_isolated_asset` left the `.aborts`
/// face entirely.
fn loop_result_read_anywhere(program: &Program, while_fid: FunId) -> bool {
    program
        .functions
        .values()
        .any(|f| block_reads_loop_result(&f.body, while_fid))
}

fn block_reads_loop_result(body: &Block, while_fid: FunId) -> bool {
    for (index, stmt) in body.stmts.iter().enumerate() {
        let value = match stmt {
            Stmt::Let { pattern, value } => {
                if expr_tailcalls_while(value, while_fid)
                    && pattern
                        .iter()
                        .flatten()
                        .any(|var| var_used_after(body, index, var))
                {
                    return true;
                }
                value
            }
            Stmt::Eval(value) => value,
        };
        if expr_reads_loop_result(value, while_fid) {
            return true;
        }
    }
    match &body.tail {
        BlockTail::Value(e) => expr_reads_loop_result(e, while_fid),
        BlockTail::Return(e)
        | BlockTail::Abort { code: e }
        | BlockTail::Break { value: e, .. }
        | BlockTail::Continue { value: e, .. }
        | BlockTail::ReturnFromBlock { value: e, .. } => {
            expr_reads_loop_result(e.as_ref(), while_fid)
        }
    }
}

fn expr_reads_loop_result(e: &Expr, while_fid: FunId) -> bool {
    match e {
        Expr::If {
            then_branch,
            else_branch,
            ..
        } => {
            block_reads_loop_result(then_branch, while_fid)
                || block_reads_loop_result(else_branch, while_fid)
        }
        Expr::Match { cases, .. } => cases
            .iter()
            .any(|arm| block_reads_loop_result(&arm.body, while_fid)),
        Expr::LabeledBlock { body, .. } => block_reads_loop_result(body, while_fid),
        _ => false,
    }
}

fn block_delivers_abort_result(
    block: &Block,
    program: &Program,
    option_id: crate::ir::StructId,
    abort_code_id: crate::ir::StructId,
) -> bool {
    match &block.tail {
        BlockTail::Return(_) => true,
        BlockTail::Value(expr) => {
            expr_delivers_abort_result(expr, program, option_id, abort_code_id)
        }
        _ => false,
    }
}

fn expr_delivers_abort_result(
    expr: &Expr,
    program: &Program,
    option_id: crate::ir::StructId,
    abort_code_id: crate::ir::StructId,
) -> bool {
    match expr {
        Expr::Pack {
            struct_id,
            type_args,
            ..
        } => {
            *struct_id == option_id
                && matches!(type_args.as_slice(), [crate::ir::ty::Type::Struct { struct_id, type_args }] if *struct_id == abort_code_id && type_args.is_empty())
        }
        Expr::Call { fun, .. } => program.functions.get(fun).is_some_and(|function| {
            function.signature.return_type
                == crate::ir::ty::Type::Struct {
                    struct_id: option_id,
                    type_args: vec![crate::ir::ty::Type::Struct {
                        struct_id: abort_code_id,
                        type_args: vec![],
                    }],
                }
                || (matches!(function.kind, FunctionKind::LoopBody { .. })
                    && crate::ir::names::is_aborts_family_name(&function.name))
        }),
        Expr::If {
            then_branch,
            else_branch,
            ..
        } => {
            block_delivers_abort_result(then_branch, program, option_id, abort_code_id)
                && block_delivers_abort_result(else_branch, program, option_id, abort_code_id)
        }
        Expr::Match { cases, .. } => cases
            .iter()
            .all(|arm| block_delivers_abort_result(&arm.body, program, option_id, abort_code_id)),
        Expr::LabeledBlock { body, .. } => {
            block_delivers_abort_result(body, program, option_id, abort_code_id)
        }
        _ => false,
    }
}

/// Rewrite the parent `.aborts` body to propagate the loop's abort.
/// Returns `Ok(new_body)` on success, `Err(original_body)` if the shape
/// isn't the guarded propagatable form.
fn try_propagate(
    mut body: Block,
    while_fid: FunId,
    option_id: crate::ir::StructId,
    no_abort: &dyn Fn() -> Expr,
) -> Result<Block, Block> {
    // EVERY rewrite below replaces the block's value with an `AbortResult`,
    // and the caller pays for that by retyping `while_N` and deadening
    // `while_N.after` to an unconditional `NoAbort`. So this routine may
    // only ever be applied to a block whose value IS the `.aborts`
    // function's answer -- its own body, or an `if`/`match` arm reached
    // through the TAIL. Descending into a STATEMENT's value instead lands
    // on a block somebody downstream consumes, and there the whole trade is
    // wrong: the abort verdict the loop now computes is never consulted
    // again, so the `.aborts` face silently loses every abort path inside
    // the loop.
    //
    // Measured twice, same generator, same shape. scallop
    // `borrow::assert_isolated_asset`: the arm sits under
    // `let (acc, world) := if c { .. while_0(..) } else { .. while_1(..) }`,
    // the `direct_tail` shortcut below reported success having rewritten
    // NOTHING, and the post-loop check that raises
    // `unable_to_borrow_other_coin_with_isolated_asset` was left in a
    // continuation with no caller. cetus `position::update_rewards_internal`:
    // same shortcut, and there it also PRE-EMPTED the last-statement rewrite
    // further down that had been handling that body correctly, so the
    // companion rendered as a bare `NoAbort` while the Move source carries
    // two `assert!`s inside the loop -- an obligation that still had its
    // original statement hash and had become vacuous.

    // If the loop result is already returned directly in tail position,
    // there is no accumulator consumption or remainder to guard. Retyping
    // the loop is sufficient; sibling arms in an abort companion already
    // deliver NoAbort/Aborted values.
    let direct_tail = match &body.tail {
        BlockTail::Value(expr) => expr_tailcalls_while(expr, while_fid),
        BlockTail::Return(expr) => expr_tailcalls_while(expr.as_ref(), while_fid),
        _ => false,
    };
    if direct_tail {
        return Ok(body);
    }

    // Loop extraction preserves source nesting: a loop in an `else` branch
    // is consumed inside that branch, not necessarily in the abort
    // companion's root block.  Repair the innermost matching branch first;
    // its surrounding `if`/`match` already returns AbortResult in the other
    // arms, so the transformed branch composes directly. Reached through
    // the tail only, per the note above.
    let tail_expr = match &mut body.tail {
        BlockTail::Value(expr) => Some(expr),
        BlockTail::Return(expr)
        | BlockTail::Abort { code: expr }
        | BlockTail::Break { value: expr, .. }
        | BlockTail::Continue { value: expr, .. }
        | BlockTail::ReturnFromBlock { value: expr, .. } => Some(expr.as_mut()),
    };
    if tail_expr.is_some_and(|expr| try_propagate_in_expr(expr, while_fid, option_id, no_abort)) {
        return Ok(body);
    }

    // A loop need not be the parent's final statement.  Move stdlib's
    // `bit_vector::shift_left`, for example, has two sequential loops in one
    // branch.  Its first loop result is dead, but the second loop and the
    // function tail form a non-empty remainder.  Preserve that remainder in
    // the NoAbort arm and short-circuit it in the Aborted arm.
    if let Some(stmt_index) = (0..body.stmts.len().saturating_sub(1))
        .rev()
        .find(|&index| {
            let Stmt::Let { pattern, value } = &body.stmts[index] else {
                return false;
            };
            pattern.len() == 1
                && pattern[0].is_some()
                && expr_tailcalls_while(value, while_fid)
                && !var_used_after(&body, index, pattern[0].as_ref().unwrap())
        })
    {
        let v = match &body.stmts[stmt_index] {
            Stmt::Let { pattern, .. } => pattern[0].clone().unwrap(),
            Stmt::Eval(_) => unreachable!(),
        };
        let remainder_stmts = body.stmts.split_off(stmt_index + 1);
        let original_tail = std::mem::replace(&mut body.tail, BlockTail::Value(Expr::Unit));
        let Stmt::Let { value, .. } = &mut body.stmts[stmt_index] else {
            unreachable!()
        };
        rewrite_arms_to_no_abort(value, while_fid, no_abort);

        let none_arm = MatchArm {
            variant: OPTION_NONE_TAG,
            bindings: vec![],
            body: Box::new(Block {
                stmts: remainder_stmts,
                tail: original_tail,
            }),
        };
        let payload: VarId = std::rc::Rc::from("__loop_abort_payload");
        let some_arm = MatchArm {
            variant: OPTION_SOME_TAG,
            bindings: vec![payload],
            body: Box::new(Block {
                stmts: vec![],
                tail: BlockTail::Value(Expr::Var(v.clone())),
            }),
        };
        body.tail = BlockTail::Value(Expr::Match {
            struct_id: option_id,
            selector: Box::new(Expr::Var(v)),
            cases: vec![none_arm, some_arm],
        });
        return Ok(body);
    }

    // The loop result must be bound by the LAST top-level stmt:
    //   Let { pattern: [Some(v)], value }   where `value` tail-calls while_N.
    let Some(Stmt::Let { pattern, value }) = body.stmts.last() else {
        return Err(body);
    };
    if pattern.len() != 1 {
        return Err(body);
    }
    let Some(v) = pattern[0].clone() else {
        return Err(body);
    };
    if !expr_tailcalls_while(value, while_fid) {
        return Err(body);
    }

    // The function tail must deliver an AbortResult that does NOT use v
    // (the loop result is dead -- the `.aborts` tail is just NoAbort,
    // either `Value(NoAbort)` or, pre-return_lift, `Return(NoAbort)`).
    // Otherwise the accumulator is genuinely consumed and this rewrite
    // would be unsound.
    let (tail_is_return, orig_ref): (bool, &Expr) = match &body.tail {
        BlockTail::Value(e) => (false, e),
        BlockTail::Return(e) => (true, e),
        _ => return Err(body),
    };
    if free_vars_of_expr(orig_ref).contains(&v) {
        return Err(body);
    }

    // Rewrite: every non-while-N-calling Value arm of `value` -> NoAbort,
    // so `value : AbortResult`.
    let Some(Stmt::Let { value, .. }) = body.stmts.last_mut() else {
        return Err(body);
    };
    rewrite_arms_to_no_abort(value, while_fid, no_abort);

    // Function tail -> match v { NoAbort => <orig>, Aborted _ => v },
    // preserving whether the original tail was a Value or a Return.
    let orig_tail = match std::mem::replace(&mut body.tail, BlockTail::Value(Expr::Unit)) {
        BlockTail::Value(e) => e,
        BlockTail::Return(e) => *e,
        _ => unreachable!(),
    };
    let none_arm = MatchArm {
        variant: OPTION_NONE_TAG,
        bindings: vec![],
        body: Box::new(Block {
            stmts: vec![],
            tail: BlockTail::Value(orig_tail),
        }),
    };
    let payload: VarId = std::rc::Rc::from("__loop_abort_payload");
    let some_arm = MatchArm {
        variant: OPTION_SOME_TAG,
        bindings: vec![payload],
        body: Box::new(Block {
            stmts: vec![],
            tail: BlockTail::Value(Expr::Var(v.clone())),
        }),
    };
    let match_expr = Expr::Match {
        struct_id: option_id,
        selector: Box::new(Expr::Var(v)),
        cases: vec![none_arm, some_arm],
    };
    body.tail = if tail_is_return {
        BlockTail::Return(Box::new(match_expr))
    } else {
        BlockTail::Value(match_expr)
    };
    Ok(body)
}

/// Recurse into `expr`'s arm blocks. Only ever called on a TAIL expression,
/// so every arm reached here is itself in tail position.
fn try_propagate_in_expr(
    expr: &mut Expr,
    while_fid: FunId,
    option_id: crate::ir::StructId,
    no_abort: &dyn Fn() -> Expr,
) -> bool {
    let try_block = |block: &mut Box<Block>| {
        let original = block.as_ref().clone();
        match try_propagate(original, while_fid, option_id, no_abort) {
            Ok(rewritten) => {
                **block = rewritten;
                true
            }
            Err(_) => false,
        }
    };
    match expr {
        Expr::If {
            then_branch,
            else_branch,
            ..
        } => try_block(then_branch) || try_block(else_branch),
        Expr::Match { cases, .. } => cases.iter_mut().any(|arm| try_block(&mut arm.body)),
        Expr::LabeledBlock { body, .. } => try_block(body),
        _ => false,
    }
}

fn var_used_after(body: &Block, stmt_index: usize, var: &VarId) -> bool {
    body.stmts[stmt_index + 1..].iter().any(|stmt| {
        let expr = match stmt {
            Stmt::Let { value, .. } | Stmt::Eval(value) => value,
        };
        free_vars_of_expr(expr).contains(var)
    }) || match &body.tail {
        BlockTail::Value(expr) => free_vars_of_expr(expr).contains(var),
        BlockTail::Return(expr)
        | BlockTail::Abort { code: expr }
        | BlockTail::Break { value: expr, .. }
        | BlockTail::Continue { value: expr, .. }
        | BlockTail::ReturnFromBlock { value: expr, .. } => {
            free_vars_of_expr(expr.as_ref()).contains(var)
        }
    }
}

/// True iff `e`'s tail position eventually calls `fid` (directly, or
/// through `if` / `match` arm tails).
fn expr_tailcalls_while(e: &Expr, fid: FunId) -> bool {
    match e {
        Expr::Call { fun, .. } => *fun == fid,
        Expr::If {
            then_branch,
            else_branch,
            ..
        } => block_tailcalls_while(then_branch, fid) || block_tailcalls_while(else_branch, fid),
        Expr::Match { cases, .. } => cases.iter().any(|a| block_tailcalls_while(&a.body, fid)),
        _ => false,
    }
}

fn block_tailcalls_while(b: &Block, fid: FunId) -> bool {
    matches!(&b.tail, BlockTail::Value(e) if expr_tailcalls_while(e, fid))
}

/// In every `Value` tail leaf of `e` that does NOT call `fid`, replace
/// the leaf with `NoAbort`, so the whole expression's type is
/// `AbortResult`. while_N-calling leaves are already `AbortResult`.
fn rewrite_arms_to_no_abort(e: &mut Expr, fid: FunId, no_abort: &dyn Fn() -> Expr) {
    match e {
        Expr::Call { fun, .. } if *fun == fid => {}
        Expr::If {
            then_branch,
            else_branch,
            ..
        } => {
            rewrite_block_arms_to_no_abort(then_branch, fid, no_abort);
            rewrite_block_arms_to_no_abort(else_branch, fid, no_abort);
        }
        Expr::Match { cases, .. } => {
            for a in cases.iter_mut() {
                rewrite_block_arms_to_no_abort(&mut a.body, fid, no_abort);
            }
        }
        // A non-while, non-branch leaf -- this is a value arm (the
        // accumulator). Replace with NoAbort.
        other => {
            *other = no_abort();
        }
    }
}

fn rewrite_block_arms_to_no_abort(b: &mut Block, fid: FunId, no_abort: &dyn Fn() -> Expr) {
    if let BlockTail::Value(e) = &mut b.tail {
        rewrite_arms_to_no_abort(e, fid, no_abort);
    }
}

fn block_has_return_or_abort(b: &Block) -> bool {
    block_has(b, &mut |t| {
        matches!(t, BlockTail::Return(_) | BlockTail::Abort { .. })
    })
}

/// Walk every block tail reachable inside `b` (through stmts' Let values
/// and tail If/Match arms), testing `pred`.
fn block_has(b: &Block, pred: &mut dyn FnMut(&BlockTail) -> bool) -> bool {
    if pred(&b.tail) {
        return true;
    }
    for s in &b.stmts {
        let e = match s {
            Stmt::Let { value, .. } => value,
            Stmt::Eval(e) => e,
        };
        if expr_has(e, pred) {
            return true;
        }
    }
    match &b.tail {
        BlockTail::Value(e) => expr_has(e, pred),
        BlockTail::Return(e) => expr_has(e, pred),
        BlockTail::Break { value, .. }
        | BlockTail::Continue { value, .. }
        | BlockTail::ReturnFromBlock { value, .. } => expr_has(value, pred),
        BlockTail::Abort { code } => expr_has(code, pred),
    }
}

fn expr_has(e: &Expr, pred: &mut dyn FnMut(&BlockTail) -> bool) -> bool {
    match e {
        Expr::If {
            then_branch,
            else_branch,
            ..
        } => block_has(then_branch, pred) || block_has(else_branch, pred),
        Expr::Match { cases, .. } => cases.iter().any(|a| block_has(&a.body, pred)),
        _ => false,
    }
}
