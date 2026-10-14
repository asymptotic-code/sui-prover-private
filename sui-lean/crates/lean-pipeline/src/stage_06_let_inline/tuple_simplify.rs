//! Sub-pass 2c -- tuple-pattern simplification and dead-let removal.
//!
//! For every `Stmt::Let { pattern, value }`:
//!
//! - Replace each `Some(v_i)` with `count(v_i) == 0` by `None`
//!   (wildcard).
//! - If every position becomes `None` AND `is_pure_total(value)`:
//!   drop the entire Let.
//! - Else if every position is `None`: convert to `Stmt::Eval(value)`
//!   (preserves the side effect / abort potential while making the
//!   binding-free shape explicit).
//!
//! This pass handles BOTH single-position dead Lets (single
//! `Some(v)` with count 0) and multi-position partial wildcards
//! (some `Some(v_i)` unused, others used).
//!
//! Augmented-call outputs are protected from nulling: a stage-4
//! `GlobalMut` call's threaded `world` slot must stay `Some` (else
//! stage 4's `LingeringUnthreadedCall` fails at render), and a
//! stage-3 mut-augmented call's whole pattern is kept (else it
//! collapses to a rejected `Stmt::Eval(Call)`). Dead unprotected
//! slots (including unused ghost outputs) are still nulled. See
//! `call_protection`.

use crate::ir::visit::{walk_block_mut_default, MutVisitor};
use crate::ir::{Block, Expr, Program, Stmt, StructId, Type};
use crate::stage_04_effects::common::is_world_type;

use super::effects_predicate::is_pure_total;
use super::use_count::{count_uses, UseCount};

/// Apply tuple-simplification over `body` once. Returns `true` when
/// any pattern position was replaced with wildcard, any Let was
/// dropped, or any Let was converted to `Stmt::Eval`.
pub fn tuple_simplify_once(body: &mut Block, program: &Program) -> bool {
    let counts = count_uses(body);
    let world_id = find_world_struct_id(program);
    let mut pass = TupleSimplify {
        counts: &counts,
        program,
        world_id,
        changed: false,
    };
    pass.visit_block_mut(body);
    pass.changed
}

/// Look up the synthetic World struct id, if stage 4 registered one.
/// `None` for hand-built programs (unit tests) or programs that never
/// went through stage 4.
fn find_world_struct_id(program: &Program) -> Option<StructId> {
    program.struct_id_by_qualified_name(crate::stage_04_effects::WORLD_QUALIFIED_NAME)
}

struct TupleSimplify<'a> {
    counts: &'a UseCount,
    program: &'a Program,
    world_id: Option<StructId>,
    changed: bool,
}

impl MutVisitor for TupleSimplify<'_> {
    fn visit_block_mut(&mut self, b: &mut Block) {
        // Phase 1: per-stmt pattern simplification / dead-let removal.
        // 1. Replace dead Some(v) positions with None.
        // 2. If all None: drop (if pure) or convert to Eval.
        let mut new_stmts: Vec<Stmt> = Vec::with_capacity(b.stmts.len());
        for s in std::mem::take(&mut b.stmts) {
            match simplify_stmt(s, self.counts, self.program, self.world_id) {
                SimplifyResult::Kept(s) => new_stmts.push(s),
                SimplifyResult::Updated(s) => {
                    new_stmts.push(s);
                    self.changed = true;
                }
                SimplifyResult::Dropped => {
                    self.changed = true;
                }
                SimplifyResult::AsEval(e) => {
                    new_stmts.push(Stmt::Eval(e));
                    self.changed = true;
                }
            }
        }
        b.stmts = new_stmts;
        // Phase 2: recurse into nested blocks via the framework walk.
        walk_block_mut_default(self, b);
    }
}

enum SimplifyResult {
    Kept(Stmt),
    Updated(Stmt),
    Dropped,
    AsEval(Expr),
}

fn simplify_stmt(
    s: Stmt,
    counts: &UseCount,
    program: &Program,
    world_id: Option<StructId>,
) -> SimplifyResult {
    let (pattern, value) = match s {
        Stmt::Let { pattern, value } => (pattern, value),
        other => return SimplifyResult::Kept(other),
    };
    // Stage 3's position-shift puts `WriteRef` and `WriteBack` in
    // value position with a `Stmt::Let { pattern: [Some(target)], .. }`
    // rebind. Stage 3 promises (held_through = Render) that no
    // `Stmt::Eval(WriteRef | WriteBack)` survives. Even if `target`
    // is unused downstream (e.g. stage 5 alpha-renamed it and no
    // later stmt references the renamed copy), we must keep the
    // `Some(target)` rebind -- converting to wildcard would either
    // produce an all-wildcard Let (rejected by the validator) or
    // collapse to `Stmt::Eval(WriteBack)` (rejected by stage 3's
    // invariant). Skip simplification for these values entirely.
    if matches!(value, Expr::WriteRef { .. } | Expr::WriteBack { .. }) {
        return SimplifyResult::Kept(Stmt::Let { pattern, value });
    }
    // A call with augmented outputs (stage-3 mut-outputs or a stage-4
    // threaded `world` slot) must not have those slots nulled: doing so
    // either collapses the Let to `Stmt::Eval(Call)` -- rejected by
    // stage 3's `UnaugmentedCallEval` and stage 4's
    // `LingeringUnthreadedCall` -- or, for the world slot specifically,
    // drops the threaded capture so stage 4's Let-arm check fails. The
    // protection is surgical: only the required slots are pinned;
    // genuinely-dead unprotected slots (e.g. unused ghost outputs) are still
    // nulled for a clean render.
    let protection = call_protection(&value, program, world_id);
    if matches!(protection, Protection::KeepAll) {
        return SimplifyResult::Kept(Stmt::Let { pattern, value });
    }
    let protected_idx = match protection {
        Protection::Protect(i) => Some(i),
        _ => None,
    };
    // Replace dead Some(v) with None, skipping any protected slot.
    //
    // A "dead" position is one where `v` has zero `Var(v)` references
    // AND no `BorrowLoc(v)` / `WriteBack { child: v, .. }` reference.
    // The base validator would reject a fully-wildcard `Stmt::Let`,
    // and a dangling `BorrowLoc(v)` post-drop would surface as
    // `UnboundVariable` -- skip such positions so the postcondition
    // diagnoses the upstream invariant violation instead of stage 6
    // producing broken IR.
    let mut new_pattern: Vec<Option<crate::ir::VarId>> = Vec::with_capacity(pattern.len());
    let mut pattern_changed = false;
    for (i, p) in pattern.iter().enumerate() {
        match p {
            Some(v)
                if counts.get(v) == 0 && !counts.has_borrow_use(v) && Some(i) != protected_idx =>
            {
                new_pattern.push(None);
                pattern_changed = true;
            }
            other => new_pattern.push(other.clone()),
        }
    }
    let all_wildcard = new_pattern.iter().all(|p| p.is_none());
    if all_wildcard {
        // Every captured value is dead. Augmented calls were protected
        // above (their world / mut-output slot stays `Some`, so they
        // never reach here all-wildcard), so any Call reaching this
        // point is safe to collapse: drop it when pure and total,
        // otherwise keep the side effect / abort potential as
        // `Stmt::Eval(value)`.
        if is_pure_total(&value, program) {
            return SimplifyResult::Dropped;
        }
        return SimplifyResult::AsEval(value);
    }
    if pattern_changed {
        SimplifyResult::Updated(Stmt::Let {
            pattern: new_pattern,
            value,
        })
    } else {
        SimplifyResult::Kept(Stmt::Let {
            pattern: new_pattern,
            value,
        })
    }
}

/// How a `Stmt::Let` binding a call result must be protected from
/// pattern-slot nulling.
enum Protection {
    /// Not an augmented call -- dead slots may be nulled freely.
    None,
    /// Stage-4 `GlobalMut` call (no `&mut` params): protect exactly the
    /// world output slot at this pattern index. Other dead slots
    /// (including unused ghost outputs) may still be nulled.
    Protect(usize),
    /// Mut-augmented call (`&mut` params): keep the entire pattern. The
    /// stage-3 mut-output slots are interleaved with original returns /
    /// world / ghost slots and aren't worth pinpointing; keeping all of
    /// them is always valid (only an all-`None` Let is rejected).
    KeepAll,
}

/// Classify how the call in `value` (if any) must be protected.
///
/// - `&mut` params -> `KeepAll` (stage-3 augmentation).
/// - `GlobalMut` without `&mut` params -> `Protect(world_slot)` when the
///   return type actually carries a `World` slot (stage-4 threading);
///   the slot index is read off the callee's return type, mirroring the
///   stage-4 postcondition's `well_threaded` check.
/// - anything else (pure calls, synthetic stubs with effects but no
///   augmented return) -> `None`.
fn call_protection(value: &Expr, program: &Program, world_id: Option<StructId>) -> Protection {
    let fun = match value {
        Expr::Call { fun, .. } => *fun,
        _ => return Protection::None,
    };
    let Some(callee) = program.lookup_callee(fun) else {
        return Protection::None;
    };
    let has_mut_params = callee
        .signature()
        .params
        .iter()
        .any(|p| matches!(p.ty, crate::ir::Type::MutableRef { .. }));
    if has_mut_params {
        return Protection::KeepAll;
    }
    if callee.effects().mutation == crate::ir::MutLevel::GlobalMut {
        if let Some(wid) = world_id {
            let world_idx = match &callee.signature().return_type {
                Type::Tuple(items) => items.iter().position(|t| is_world_type(t, wid)),
                t => {
                    if is_world_type(t, wid) {
                        Some(0)
                    } else {
                        None
                    }
                }
            };
            if let Some(i) = world_idx {
                return Protection::Protect(i);
            }
        }
    }
    Protection::None
}
