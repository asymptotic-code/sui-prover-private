//! Transform 5: augment Return tails and the function body's fall-off tail to
//! produce the original return plus each function state channel. Stage 3
//! introduces state for `&mut` params; it also normalizes functions that Stage
//! 4 will augment with `World` so Stage 5 can build their control-flow joins.
//!
//! See the design doc's Transform 5 for the rules. Walks the body
//! recursively to find every reachable `BlockTail::Return`. The
//! function body's top-level tail is augmented separately because it
//! represents the "fall-off" exit (a `BlockTail::Value` at the top
//! level IS a function exit; the same variant inside an arm is not).

use std::collections::BTreeSet;

use crate::ir::visit::{walk_expr_default, Visitor};
use crate::ir::{Block, BlockTail, Expr, Function, MatchArm, Program, Stmt, Type, VarId};

use super::common::{augment_value, mut_param_info, MutParam};
use super::Stage3Error;

/// Augment Return + fall-off tails for every function with `&mut` parameters,
/// and normalize state-changing control tails for the functions that Stage 4
/// will augment with `World`. `program.functions` is body-only post step 5.
pub fn augment_body_tails(program: &mut Program) -> Result<(), Stage3Error> {
    // Stage 5 must see every state-changing If/Match in statement position
    // so its phi construction can carry the selected state out.  Restrict
    // that structural normalization to functions which actually have such a
    // state channel: existing mutable-reference parameters, or the exact
    // transitive set that stage 4 will augment with World.  Rewriting every
    // pure control tree perturbs shapes consumed by stage 7's abort helpers
    // without providing any state-flow benefit.
    let needs_world = crate::stage_04_effects::common::compute_needs_world(program);
    let fids: Vec<crate::ir::FunId> = program.functions.keys().copied().collect();
    for fid in fids {
        let func = program.functions.get_mut(&fid).unwrap();
        let muts = mut_param_info(func);
        if muts.is_empty() && !needs_world.contains(&fid) {
            continue;
        }
        // Skip stub bodies (`stmts = [], tail = Value(Unit)`) entirely
        // when the original return type was non-Unit. These come from
        // upstream Move modules whose function bodies weren't lifted
        // (e.g., the stdlib's `option::borrow_mut` whose source isn't
        // in the user's compile target). Augmenting the stub
        // tail produces invalid output like `((), t)` where the first
        // tuple slot has type `Mutable T` but the value is `()`. Leave
        // these as stubs; the renderer emits `sorry`.
        let is_stub = func.body.stmts.is_empty()
            && matches!(
                &func.body.tail,
                crate::ir::BlockTail::Value(crate::ir::Expr::Unit)
            );
        let result_arity = original_result_arity(&func.signature.return_type, &muts);
        let ret_is_unit = result_arity == 0;
        if is_stub && !ret_is_unit {
            continue;
        }
        let mut exit_vars = ExitVars::from_function(func);
        augment_in_block(
            &mut func.body,
            &muts,
            ret_is_unit,
            result_arity,
            &mut exit_vars,
            result_arity,
            /* top_level= */ true,
        );
    }
    Ok(())
}

/// Recover whether the function's *original* (pre-Transform-4) return
/// type was `Unit`. Used by [`augment_value`] to decide whether to wrap
/// or drop the unit.
///
/// Per the always-Tuple invariant: an augmented return type is always
/// `Type::Tuple([...])`. The original was `Unit` iff the augmented
/// tuple's length equals `muts.len()` (no original element prepended).
fn original_result_arity(augmented: &Type, muts: &[MutParam]) -> usize {
    if muts.is_empty() {
        return match augmented {
            Type::Unit => 0,
            Type::Tuple(items) => items.len(),
            _ => 1,
        };
    }
    match augmented {
        Type::Tuple(items) => items.len().saturating_sub(muts.len()),
        // `augment_signatures` always produces a Tuple here. Retain the old
        // fail-later behavior for callers that invoke this transform alone.
        _ => 1,
    }
}

struct ExitVars {
    occupied: BTreeSet<VarId>,
    next: u64,
}

impl ExitVars {
    fn from_function(function: &Function) -> Self {
        struct Collector(BTreeSet<VarId>);

        impl Visitor for Collector {
            fn visit_var(&mut self, var: &VarId) {
                self.0.insert(var.clone());
            }

            fn visit_expr(&mut self, expr: &Expr) {
                if let Expr::While { live_out, .. } = expr {
                    for (inside, outside) in live_out {
                        self.visit_var(inside);
                        self.visit_var(outside);
                    }
                }
                walk_expr_default(self, expr);
            }
        }

        let mut collector = Collector(BTreeSet::new());
        for param in &function.signature.params {
            collector.visit_var(&param.var);
        }
        collector.visit_block(&function.body);
        Self {
            occupied: collector.0,
            next: 0,
        }
    }

    fn fresh(&mut self) -> VarId {
        loop {
            let candidate: VarId = format!("__mut_tail_result_{}", self.next).into();
            self.next = self
                .next
                .checked_add(1)
                .expect("stage 3 exit-result name space exhausted");
            if self.occupied.insert(candidate.clone()) {
                return candidate;
            }
        }
    }
}

fn augment_in_block(
    block: &mut Block,
    muts: &[MutParam],
    ret_is_unit: bool,
    result_arity: usize,
    exit_vars: &mut ExitVars,
    value_arity: usize,
    top_level: bool,
) {
    // Recurse into stmts for nested Return tails.
    for stmt in block.stmts.iter_mut() {
        augment_in_stmt(stmt, muts, ret_is_unit, result_arity, exit_vars);
    }
    // Tail handling:
    //  - Return tails always get augmented (any nesting level).
    //  - The function body's TOP-LEVEL Value tail gets augmented (it's
    //    the fall-off exit).
    //  - Inner Value tails (inside arms / loops / quantifiers) do NOT
    //    get augmented -- they feed the surrounding expression context.
    //  - Break / Continue don't exit the function; not augmented.
    //  - Abort doesn't return a value; not augmented.
    // For an originally-Unit function, `augment_value` intentionally omits
    // the semantic Unit and returns only the mutable state.  A non-literal
    // Unit expression can still contain control flow or effects, however, so
    // preserve it as the final statement before replacing the exit value.
    let mut trailing_stmt = None;
    match &mut block.tail {
        BlockTail::Return(value) => {
            // First recurse into the carried expression to handle
            // any further-nested Returns (Returns can be inside the
            // value's compound sub-blocks).
            recurse_expr(
                value,
                muts,
                ret_is_unit,
                result_arity,
                exit_vars,
                result_arity,
            );
            trailing_stmt = augment_exit_value(value, muts, ret_is_unit, result_arity, exit_vars);
        }
        BlockTail::Value(e) if top_level => {
            // CRITICAL: recurse into `e` BEFORE wrapping, so any
            // nested Returns inside `e` (e.g., `Value(If(c, Block { tail: Return(v) }, ..))`)
            // get augmented. Wrapping only handles the fall-off path
            // where `e`'s own value is the function's return; the
            // Returns inside arms are independent function exits.
            recurse_expr(e, muts, ret_is_unit, result_arity, exit_vars, result_arity);
            trailing_stmt = augment_exit_value(e, muts, ret_is_unit, result_arity, exit_vars);
        }
        // Non-top-level Value, Break, Continue, Abort: descend into
        // their carried expressions to find nested Returns.
        BlockTail::Value(e) => {
            recurse_expr(e, muts, ret_is_unit, result_arity, exit_vars, value_arity);
            if !control_never_falls_through(e) {
                trailing_stmt = normalize_block_value(e, value_arity, exit_vars);
            }
        }
        BlockTail::Break { value, .. } | BlockTail::Continue { value, .. } => {
            recurse_expr(value, muts, ret_is_unit, result_arity, exit_vars, 1);
        }
        BlockTail::Abort { code } => {
            recurse_expr(code, muts, ret_is_unit, result_arity, exit_vars, 1);
        }
        BlockTail::ReturnFromBlock { value, .. } => {
            recurse_expr(value, muts, ret_is_unit, result_arity, exit_vars, 1);
        }
    }
    if let Some(stmt) = trailing_stmt {
        block.stmts.push(stmt);
    }
}

/// Augment a function-exit value and return any expression that must move to
/// statement position before the new mutable-state tail.
fn augment_exit_value(
    value: &mut Expr,
    muts: &[MutParam],
    ret_is_unit: bool,
    result_arity: usize,
    exit_vars: &mut ExitVars,
) -> Option<Stmt> {
    if value_already_augmented(value, muts, ret_is_unit) {
        return None;
    }

    let taken = std::mem::replace(value, Expr::Unit);
    if ret_is_unit && !matches!(taken, Expr::Unit) {
        *value = augment_value(Expr::Unit, muts, true);
        Some(Stmt::Eval(taken))
    } else if !ret_is_unit && needs_statementization(&taken) {
        debug_assert!(result_arity > 0);
        let (stmt, result) = statementize_value(taken, result_arity, exit_vars);
        *value = augment_value(result, muts, false);
        Some(stmt)
    } else {
        *value = augment_value(taken, muts, ret_is_unit);
        None
    }
}

fn needs_statementization(expr: &Expr) -> bool {
    matches!(expr, Expr::If { .. } | Expr::Match { .. })
}

/// Prove that a control expression has no value-producing path back to its
/// enclosing block. Moving such an expression into a statement and replacing
/// its tail with `Value(Unit)` would manufacture a fallthrough edge that does
/// not exist in the source. In a loop body, that false edge becomes an
/// unchanged implicit continue and can turn a terminating nested-loop path
/// into nontermination.
///
/// This is deliberately structural and fail-closed. A direct nonlocal tail is
/// sufficient regardless of the statements before it; nested tail controls
/// qualify only when every arm recursively has the same property.
fn control_never_falls_through(expr: &Expr) -> bool {
    match expr {
        Expr::If {
            then_branch,
            else_branch,
            ..
        } => block_never_falls_through(then_branch) && block_never_falls_through(else_branch),
        Expr::Match { cases, .. } => {
            !cases.is_empty() && cases.iter().all(|arm| block_never_falls_through(&arm.body))
        }
        _ => false,
    }
}

fn block_never_falls_through(block: &Block) -> bool {
    match &block.tail {
        BlockTail::Return(_)
        | BlockTail::Break { .. }
        | BlockTail::Continue { .. }
        | BlockTail::Abort { .. }
        | BlockTail::ReturnFromBlock { .. } => true,
        BlockTail::Value(expr) => control_never_falls_through(expr),
    }
}

/// Move a control result to statement position and return the expression that
/// denotes its bound value.  `arity` is the consuming `Stmt::Let` pattern
/// arity, not necessarily the value type's tuple arity: a one-slot pattern
/// binds a tuple value as one value, while a multi-slot pattern destructures
/// it.
fn statementize_value(expr: Expr, arity: usize, exit_vars: &mut ExitVars) -> (Stmt, Expr) {
    if arity == 0 {
        return (Stmt::Eval(expr), Expr::Unit);
    }

    let result_vars: Vec<VarId> = (0..arity).map(|_| exit_vars.fresh()).collect();
    let result = if result_vars.len() == 1 {
        Expr::Var(result_vars[0].clone())
    } else {
        Expr::Tuple(result_vars.iter().cloned().map(Expr::Var).collect())
    };
    (
        Stmt::Let {
            pattern: result_vars.into_iter().map(Some).collect(),
            value: expr,
        },
        result,
    )
}

/// Put a nested `Value(If|Match)` in statement position so stage 5 performs
/// its phi construction before the enclosing branch observes the arm scope.
/// Without this ANF step, stage 5 treats the nested control as a subexpression,
/// restores its incoming scope, and loses mutable rebindings made in its arms.
///
/// Multi-slot consumers additionally require syntactic Tuple tails in every
/// value-producing arm (`stage_05_ssa::build_phi_arm_tail`).  Normalize an
/// otherwise valid tuple-valued leaf through a destructuring let.  While and
/// LabeledBlock values deliberately remain in their specialized forms: stages
/// 5 and 7 assign those expressions dedicated loop/labeled-block ABIs, so a
/// generic destructuring let would misrepresent their results.
fn normalize_block_value(
    value: &mut Expr,
    value_arity: usize,
    exit_vars: &mut ExitVars,
) -> Option<Stmt> {
    let is_control = needs_statementization(value);
    let needs_tuple_shape = value_arity > 1
        && !matches!(value, Expr::Tuple(items) if items.len() == value_arity)
        && !matches!(value, Expr::While { .. } | Expr::LabeledBlock { .. });
    if !is_control && !needs_tuple_shape {
        return None;
    }

    let taken = std::mem::replace(value, Expr::Unit);
    let (stmt, result) = statementize_value(taken, value_arity, exit_vars);
    *value = result;
    Some(stmt)
}

fn augment_in_stmt(
    stmt: &mut Stmt,
    muts: &[MutParam],
    ret_is_unit: bool,
    result_arity: usize,
    exit_vars: &mut ExitVars,
) {
    let (value, value_arity) = match stmt {
        Stmt::Let { pattern, value } => (value, pattern.len()),
        Stmt::Eval(e) => (e, 0),
    };
    recurse_expr(
        value,
        muts,
        ret_is_unit,
        result_arity,
        exit_vars,
        value_arity,
    );
}

/// Walk into compound expressions to find nested `BlockTail::Return`s.
/// Top-level Value tails are NOT augmented here -- only Returns.
fn recurse_expr(
    expr: &mut Expr,
    muts: &[MutParam],
    ret_is_unit: bool,
    result_arity: usize,
    exit_vars: &mut ExitVars,
    value_arity: usize,
) {
    match expr {
        Expr::If {
            cond,
            then_branch,
            else_branch,
        } => {
            recurse_expr(cond, muts, ret_is_unit, result_arity, exit_vars, 1);
            augment_in_block(
                then_branch,
                muts,
                ret_is_unit,
                result_arity,
                exit_vars,
                value_arity,
                /* top_level= */ false,
            );
            augment_in_block(
                else_branch,
                muts,
                ret_is_unit,
                result_arity,
                exit_vars,
                value_arity,
                /* top_level= */ false,
            );
        }
        Expr::Match {
            selector, cases, ..
        } => {
            recurse_expr(selector, muts, ret_is_unit, result_arity, exit_vars, 1);
            for MatchArm { body, .. } in cases.iter_mut() {
                augment_in_block(
                    body,
                    muts,
                    ret_is_unit,
                    result_arity,
                    exit_vars,
                    value_arity,
                    /* top_level= */ false,
                );
            }
        }
        Expr::While {
            header, cond, body, ..
        } => {
            augment_in_block(
                header,
                muts,
                ret_is_unit,
                result_arity,
                exit_vars,
                0,
                /* top_level= */ false,
            );
            recurse_expr(cond, muts, ret_is_unit, result_arity, exit_vars, 1);
            augment_in_block(
                body,
                muts,
                ret_is_unit,
                result_arity,
                exit_vars,
                0,
                /* top_level= */ false,
            );
        }
        Expr::Quantifier { body, .. } => {
            // Quantifier bodies cannot contain Returns (validator enforces
            // Value tail), but recurse anyway to keep the walker uniform.
            augment_in_block(
                body,
                muts,
                ret_is_unit,
                result_arity,
                exit_vars,
                1,
                /* top_level= */ false,
            );
        }
        Expr::LabeledBlock { body, .. } => {
            augment_in_block(
                body,
                muts,
                ret_is_unit,
                result_arity,
                exit_vars,
                value_arity,
                /* top_level= */ false,
            );
        }
        _ => {}
    }
}

/// Detect whether `value` is already augmented per `muts` /
/// `ret_is_unit`. Used to make this transform idempotent.
///
/// Per the always-Tuple invariant, the augmented value is always
/// `Expr::Tuple([...])`. The trailing `muts.len()` elements must be
/// `Var(p_i)` for each mut param `p_i`, and the head_count must match
/// `ret_is_unit` (0 for unit, >= 1 for non-unit).
fn value_already_augmented(value: &Expr, muts: &[MutParam], ret_is_unit: bool) -> bool {
    if muts.is_empty() {
        return true;
    }
    match value {
        Expr::Tuple(items) if items.len() >= muts.len() => {
            let head_count = items.len() - muts.len();
            let head_count_ok = if ret_is_unit {
                head_count == 0
            } else {
                head_count >= 1
            };
            if !head_count_ok {
                return false;
            }
            items[head_count..]
                .iter()
                .zip(muts.iter())
                .all(|(item, m)| matches!(item, Expr::Var(v) if v == &m.var))
        }
        _ => false,
    }
}
