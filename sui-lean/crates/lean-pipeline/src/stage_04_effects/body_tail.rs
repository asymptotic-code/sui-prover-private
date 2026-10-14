//! Transform E: augment `BlockTail::Return` and the function body's
//! fall-off `BlockTail::Value` to produce a tuple ending in
//! `Var(world)`.
//!
//! Mirrors `stage_03_mut_to_let::body_tail` in shape, simplified to
//! a single trailing slot (world). Pattern:
//!
//! - Recursive walk over the body. For every `BlockTail::Return(v)` reachable
//!   inside any block (top-level, If/Match/While/Quantifier arms), return the
//!   original result together with `Var(world)`.
//! - For the function body's **top-level** `BlockTail::Value(v)` (the fall-off
//!   exit), do the same. A direct `If`/`Match` exit is augmented inside each
//!   live arm so the selected World reaches Stage 5's join.
//! - Inner `BlockTail::Value(_)` is NOT wrapped -- it's a
//!   sub-expression value, not a function exit.
//! - `BlockTail::Break/Continue/Abort` are not wrapped (no world to
//!   thread on those control flows; loop break/continue carry
//!   loop-state introduced later by stage 5; abort doesn't return).

use std::collections::BTreeSet;

use crate::ir::{Block, BlockTail, Expr, FunId, MatchArm, Program, Stmt, StructId, VarId};

use super::common::{
    augment_value_with_world, original_was_unit_world, value_already_world_augmented, world_varid,
};
use super::Stage4Error;

/// Augment Return + fall-off tails for every non-native function in
/// `needs_world`.
pub fn augment_body_tails(
    program: &mut Program,
    world_id: StructId,
    needs_world: &BTreeSet<FunId>,
) -> Result<(), Stage4Error> {
    let world_var = world_varid();
    let fids: Vec<FunId> = needs_world
        .iter()
        .copied()
        .filter(|fid| program.functions.get(fid).map(|f| true).unwrap_or(false))
        .collect();
    for fid in fids {
        let func = program.functions.get_mut(&fid).unwrap();
        // Skip stub bodies (`stmts = [], tail = Value(Unit)`) when
        // the original return type wasn't Unit. These come from
        // upstream Move modules whose function bodies weren't lifted
        // (e.g., natives we don't have IR for). Augmenting the stub
        // tail produces invalid output. Leave them as stubs; the
        // renderer emits `sorry`.
        let is_stub =
            func.body.stmts.is_empty() && matches!(&func.body.tail, BlockTail::Value(Expr::Unit));
        let ret_is_unit = original_was_unit_world(&func.signature.return_type, world_id);
        if is_stub && !ret_is_unit {
            continue;
        }
        augment_in_block(
            &mut func.body,
            &world_var,
            ret_is_unit,
            /* top_level= */ true,
        );
    }
    Ok(())
}

fn augment_in_block(block: &mut Block, world_var: &VarId, ret_is_unit: bool, top_level: bool) {
    for stmt in block.stmts.iter_mut() {
        augment_in_stmt(stmt, world_var, ret_is_unit);
    }
    match &mut block.tail {
        BlockTail::Return(value) => {
            if !augment_control_exit(value, world_var, ret_is_unit) {
                recurse_expr(value, world_var, ret_is_unit);
                if !value_already_world_augmented(value, world_var) {
                    let taken = std::mem::replace(&mut **value, Expr::Unit);
                    **value = augment_value_with_world(taken, world_var, ret_is_unit);
                }
            }
        }
        BlockTail::Value(e) if top_level => {
            if !augment_control_exit(e, world_var, ret_is_unit) {
                // Recurse before wrapping so nested Returns in other compound
                // expressions receive the augmented function-exit shape.
                recurse_expr(e, world_var, ret_is_unit);
                if !value_already_world_augmented(e, world_var) {
                    let taken = std::mem::replace(e, Expr::Unit);
                    *e = augment_value_with_world(taken, world_var, ret_is_unit);
                }
            }
        }
        BlockTail::Value(e) => recurse_expr(e, world_var, ret_is_unit),
        BlockTail::Break { value, .. } | BlockTail::Continue { value, .. } => {
            recurse_expr(value, world_var, ret_is_unit);
        }
        BlockTail::Abort { code } => recurse_expr(code, world_var, ret_is_unit),
        BlockTail::ReturnFromBlock { value, .. } => {
            recurse_expr(value, world_var, ret_is_unit);
        }
    }
}

/// An `If` or `Match` used directly as a function exit must return World from
/// each live arm. Wrapping the whole control expression as
/// `Tuple([If/Match, world])` is stale when an arm advances World: Stage 5
/// restores subexpression-arm scopes before resolving the outer variable.
fn augment_control_exit(expr: &mut Expr, world_var: &VarId, ret_is_unit: bool) -> bool {
    match expr {
        Expr::If {
            cond,
            then_branch,
            else_branch,
        } => {
            recurse_expr(cond, world_var, ret_is_unit);
            augment_in_block(
                then_branch,
                world_var,
                ret_is_unit,
                /* top_level= */ true,
            );
            augment_in_block(
                else_branch,
                world_var,
                ret_is_unit,
                /* top_level= */ true,
            );
            true
        }
        Expr::Match {
            selector, cases, ..
        } => {
            recurse_expr(selector, world_var, ret_is_unit);
            for MatchArm { body, .. } in cases {
                augment_in_block(body, world_var, ret_is_unit, /* top_level= */ true);
            }
            true
        }
        _ => false,
    }
}

fn augment_in_stmt(stmt: &mut Stmt, world_var: &VarId, ret_is_unit: bool) {
    let value = match stmt {
        Stmt::Let { value, .. } => value,
        Stmt::Eval(e) => e,
    };
    recurse_expr(value, world_var, ret_is_unit);
}

fn recurse_expr(expr: &mut Expr, world_var: &VarId, ret_is_unit: bool) {
    match expr {
        Expr::If {
            cond,
            then_branch,
            else_branch,
        } => {
            recurse_expr(cond, world_var, ret_is_unit);
            augment_in_block(
                then_branch,
                world_var,
                ret_is_unit,
                /* top_level= */ false,
            );
            augment_in_block(
                else_branch,
                world_var,
                ret_is_unit,
                /* top_level= */ false,
            );
        }
        Expr::Match {
            selector, cases, ..
        } => {
            recurse_expr(selector, world_var, ret_is_unit);
            for MatchArm { body, .. } in cases.iter_mut() {
                augment_in_block(body, world_var, ret_is_unit, /* top_level= */ false);
            }
        }
        Expr::While {
            header, cond, body, ..
        } => {
            augment_in_block(header, world_var, ret_is_unit, /* top_level= */ false);
            recurse_expr(cond, world_var, ret_is_unit);
            augment_in_block(body, world_var, ret_is_unit, /* top_level= */ false);
        }
        Expr::Quantifier { body, .. } => {
            augment_in_block(body, world_var, ret_is_unit, /* top_level= */ false);
        }
        Expr::LabeledBlock { body, .. } => {
            // A `return` nested in a `LabeledBlock` (lifted by stage 2)
            // must have its tail world-augmented too. stage_03's sibling
            // and stage_04's own postcondition both descend here; this
            // transform must as well, or the return arity mismatches the
            // world-augmented signature.
            augment_in_block(body, world_var, ret_is_unit, /* top_level= */ false);
        }
        _ => {}
    }
}
