//! Structural pure-and-total predicate.
//!
//! Stage 6's central decision oracle for inlining. An expression
//! is **pure-and-total** when it has no observable side effects AND
//! cannot abort. `Call { fun, .. }` dispatches on the callee's
//! `Function::effects` field, which stage 2's `classify_effects`
//! pass populates (Total + Det + NoMut, i.e. `Effects::PURE`).
//!
//! See `plans/lean-pipeline/stage-06-let-inline.md` "Pure-and-total
//! predicate" for the rule set; this implementation matches the
//! design-doc pseudocode.
//!
//! ## Bucket recap
//!
//! - **Atoms** (`Var`, `Const`, `Unit`) -- pure-and-total.
//! - **Arithmetic** -- `BinOp::can_abort_on_uint()` ops
//!   (`Add/Sub/Mul/Div/Mod/Shl/Shr`) are **not** pure-and-total
//!   (overflow / div-by-zero / shift-width). Bitwise / logical /
//!   comparison ops ARE pure-and-total.
//! - **Cast** -- `UnOp::Cast(_)` is **not** pure-and-total
//!   (narrowing abort). `Not` / `BitNot` are.
//! - **`BitOp`** -- pure-and-total iff every sub-expr is.
//! - **`Call`** -- pure-and-total iff callee `Function::effects ==
//!   Effects::PURE` AND every arg is pure-and-total.
//! - **`Tuple` / `Pack` / `Unpack` / `Field` / `UpdateField` /
//!   `UpdateVec`** -- pure-and-total iff every sub-expr is.
//! - **`If` / `Match`** -- pure-and-total iff cond / selector AND
//!   every arm body is pure-and-total (a block is pure-and-total
//!   only when its tail is `BlockTail::Value` -- terminator tails
//!   are jumps, never pure).
//! - **`While`** -- never pure-and-total (structural purity does not prove
//!   termination, so duplicating or discarding a loop is unsafe).
//! - **Mutref machinery** (`BorrowLoc` / `BorrowField` / `ReadRef` /
//!   `WriteRef` / `WriteBack`) -- never pure-and-total. Shouldn't
//!   appear post-stage-4 in non-pattern-4b bodies; defensive.
//! - **`ToProp` / `ToBool`** -- pass-through over the inner expr.
//! - **`Quantifier`** -- pure-and-total iff domain bounds and body
//!   are pure-and-total. (Quantifier bodies are pure predicates by
//!   IR contract; the predicate still walks them so partial-or-
//!   impure intrinsics inside the body propagate.)

use crate::ir::{quant::QuantDomain, BinOp, BitOp, BlockTail, Expr, Program, Stmt, UnOp};

/// True iff `e` has no observable side effects and cannot abort.
///
/// Walks the entire expression tree; `Call` dispatches on
/// `program.functions[fun].effects`. Callees absent from
/// `program.functions` (which excludes natives) are rejected --
/// the conservative choice for inlining contexts. See
/// [`is_eval_dce_droppable`] for the broader variant that accepts
/// pure-total native calls.
pub fn is_pure_total(e: &Expr, program: &Program) -> bool {
    is_pure_total_with(e, program, false)
}

/// A `Block` is pure-and-total iff its tail is `BlockTail::Value(_)`,
/// the tail expression is pure-and-total, AND every statement is
/// pure-and-total. Non-Value tails (Break / Continue / Return /
/// Abort) are jumps -- always partial.
pub fn is_pure_total_block(b: &crate::ir::Block, program: &Program) -> bool {
    is_pure_total_block_with(b, program, false)
}

/// A statement is pure-and-total iff its right-hand-side expression
/// is. `Stmt::Let` and `Stmt::Eval` have identical semantics here --
/// both contribute a single expression to the surrounding block.
pub fn is_pure_total_stmt(s: &Stmt, program: &Program) -> bool {
    is_pure_total_stmt_with(s, program, false)
}

/// Broader pure-total predicate used **only by `eval_dce`** to
/// decide whether a `Stmt::Eval(e)` can be dropped from a block.
/// Differs from `is_pure_total` in that it sees through `Call`s
/// to **native functions** whose registry entry is
/// `Effects::PURE` (the stricter `is_pure_total` accepts only
/// translated user functions). The asymmetry exists because
/// `single_use_inline` can't safely inline a pure-total native
/// call: inlining changes the call's tuple position into a
/// value-form expression whose `rendered_type_of` (with
/// `strip_mutable_ref_in_type`) doesn't line up with the surrounding
/// function-return type's `Mutation`-wrapped shape, and the
/// per-slot tuple coercion in the renderer doesn't handle the
/// resulting mismatch (`navi-lending:oracle` regression, see
/// commit message). Dropping a `Stmt::Eval(<native call>)` is
/// always safe when the native is pure-total: the call has no
/// observable effects and cannot abort, so the discarded value
/// is moot.
pub fn is_eval_dce_droppable(e: &Expr, program: &Program) -> bool {
    is_pure_total_with(e, program, true)
}

// ============================================================
// Shared walker
// ============================================================
//
// `is_pure_total` and `is_eval_dce_droppable` share 95% of their
// implementation -- they walk every `Expr` variant the same way
// and only diverge in the `Call` arm: the strict predicate looks
// up callees in `program.functions` (translated user fns only),
// the broader one consults `program.lookup_callee` (translated
// + natives) and accepts pure-total natives. The
// `accept_pure_natives` flag picks the dispatch.

fn is_pure_total_with(e: &Expr, program: &Program, accept_pure_natives: bool) -> bool {
    use crate::ir::natives::CalleeRef;
    match e {
        Expr::Borrow { .. } => false,
        Expr::Update { step, base, value } => {
            step.exprs()
                .all(|__pe| is_pure_total_with(__pe, program, accept_pure_natives))
                && is_pure_total_with(base, program, accept_pure_natives)
                && is_pure_total_with(value, program, accept_pure_natives)
        }
        Expr::Var(_) | Expr::Const(_) | Expr::Unit => true,

        // Arithmetic that can abort on bounded integers is partial.
        Expr::BinOp { op, lhs, rhs } => {
            if op.can_abort_on_uint() {
                return false;
            }
            is_pure_total_with(lhs, program, accept_pure_natives)
                && is_pure_total_with(rhs, program, accept_pure_natives)
        }

        // Cast may narrow; partial. Not / BitNot are total.
        Expr::UnOp { op, operand } => {
            if matches!(op, UnOp::Cast(_)) {
                return false;
            }
            is_pure_total_with(operand, program, accept_pure_natives)
        }

        Expr::BitOp(op) => is_pure_total_bitop_with(op, program, accept_pure_natives),

        Expr::Call { fun, args, .. } => {
            // Strict mode: only translated user functions count;
            // natives default to "not pure-and-total" because
            // `single_use_inline` can't safely substitute them.
            // Broader mode (`accept_pure_natives`): both translated
            // and native callees are accepted iff
            // `effects == Effects::PURE`. Used by `eval_dce` to
            // drop `Stmt::Eval(<pure-total native call>)`.
            let effects = if accept_pure_natives {
                match program.lookup_callee(*fun) {
                    Some(CalleeRef::Translated(f)) => f.effects,
                    Some(CalleeRef::Native(d)) => d.effects,
                    None => return false,
                }
            } else {
                match program.functions.get(fun) {
                    Some(f) => f.effects,
                    None => return false,
                }
            };
            if effects != crate::ir::Effects::PURE {
                return false;
            }
            args.iter()
                .all(|a| is_pure_total_with(a, program, accept_pure_natives))
        }

        Expr::Tuple(elems) | Expr::Pack { fields: elems, .. } => elems
            .iter()
            .all(|e| is_pure_total_with(e, program, accept_pure_natives)),

        Expr::Unpack { value, .. } | Expr::Field { base: value, .. } => {
            is_pure_total_with(value, program, accept_pure_natives)
        }

        Expr::If {
            cond,
            then_branch,
            else_branch,
        } => {
            is_pure_total_with(cond, program, accept_pure_natives)
                && is_pure_total_block_with(then_branch, program, accept_pure_natives)
                && is_pure_total_block_with(else_branch, program, accept_pure_natives)
        }

        Expr::Match {
            selector, cases, ..
        } => {
            is_pure_total_with(selector, program, accept_pure_natives)
                && cases
                    .iter()
                    .all(|arm| is_pure_total_block_with(&arm.body, program, accept_pure_natives))
        }

        // While is never pure-and-total: a pure body does not establish
        // termination, so inlining or discarding the loop is unsafe.
        Expr::While { .. } => false,

        // Mutref machinery is never pure-and-total. Shouldn't survive
        // stage 4 in non-pattern-4b bodies; defensive.
        Expr::BorrowLoc(_)
        | Expr::BorrowGlobal(_)
        | Expr::WriteRef { .. }
        | Expr::WriteBack { .. }
        | Expr::IsParent { .. } => false,

        // ReadRef: structurally a value read off a `Mutation` (the
        // renderer emits `.val` for it). The dereference itself has
        // no observable effect and can't abort -- the underlying
        // value already exists. Propagating pure-and-total to the
        // inner expression lets eval_dce drop dead `let _ := <ref>.val`
        // statements that survive into stage 7's aborts companion
        // bodies. Without this, dead chains of `let _ := pool.val;
        // let _ := callee(pool.val); ...` end up rendered inside an
        // if-then-else arm that's a struct-literal field value, and
        // Lean's parser rejects the multi-line layout (see
        // `plans/lean-pipeline/render -- single-line if-then-else`
        // commit message).
        Expr::ReadRef(inner) => is_pure_total_with(inner, program, accept_pure_natives),

        Expr::ToProp(inner) | Expr::ToBool(inner) => {
            is_pure_total_with(inner, program, accept_pure_natives)
        }

        Expr::Quantifier { domain, body, .. } => {
            is_pure_total_domain_with(domain, program, accept_pure_natives)
                && is_pure_total_block_with(body, program, accept_pure_natives)
        }
        Expr::LabeledBlock { body, .. } => {
            is_pure_total_block_with(body, program, accept_pure_natives)
        }
    }
}

fn is_pure_total_block_with(
    b: &crate::ir::Block,
    program: &Program,
    accept_pure_natives: bool,
) -> bool {
    let tail_expr = match &b.tail {
        BlockTail::Value(e) => e,
        _ => return false,
    };
    if !is_pure_total_with(tail_expr, program, accept_pure_natives) {
        return false;
    }
    b.stmts
        .iter()
        .all(|s| is_pure_total_stmt_with(s, program, accept_pure_natives))
}

fn is_pure_total_stmt_with(s: &Stmt, program: &Program, accept_pure_natives: bool) -> bool {
    match s {
        Stmt::Let { value, .. } => is_pure_total_with(value, program, accept_pure_natives),
        Stmt::Eval(e) => is_pure_total_with(e, program, accept_pure_natives),
    }
}

fn is_pure_total_bitop_with(op: &BitOp, program: &Program, accept_pure_natives: bool) -> bool {
    match op {
        BitOp::Extract { operand, .. }
        | BitOp::ZeroExtend { operand, .. }
        | BitOp::SignExtend { operand, .. } => {
            is_pure_total_with(operand, program, accept_pure_natives)
        }
        BitOp::Concat { high, low } => {
            is_pure_total_with(high, program, accept_pure_natives)
                && is_pure_total_with(low, program, accept_pure_natives)
        }
    }
}

fn is_pure_total_domain_with(
    d: &QuantDomain,
    program: &Program,
    accept_pure_natives: bool,
) -> bool {
    match d {
        QuantDomain::Unbounded => true,
        QuantDomain::Range { start, end } => {
            is_pure_total_with(start, program, accept_pure_natives)
                && is_pure_total_with(end, program, accept_pure_natives)
        }
        QuantDomain::VecRange { vec, start, end } => {
            is_pure_total_with(vec, program, accept_pure_natives)
                && is_pure_total_with(start, program, accept_pure_natives)
                && is_pure_total_with(end, program, accept_pure_natives)
        }
        QuantDomain::Collection(c) => is_pure_total_with(c, program, accept_pure_natives),
    }
}

// Defensive sanity check: every BinOp variant that "can abort on
// UInt" maps to a partial operation here. Caught at compile time
// rather than via test-coverage.
const _ASSERT_BIN_OP_PARTIAL_LIST: () = {
    // If a new BinOp variant is added, this match forces a
    // build-time review of whether it can abort on UInt.
    match BinOp::Add {
        BinOp::Add
        | BinOp::Sub
        | BinOp::Mul
        | BinOp::WrappingAdd
        | BinOp::WrappingSub
        | BinOp::WrappingMul
        | BinOp::SAdd
        | BinOp::SSub
        | BinOp::SMul
        | BinOp::Div
        | BinOp::Mod
        | BinOp::SDiv
        | BinOp::SMod
        | BinOp::Shl
        | BinOp::Shr
        | BinOp::LShr
        | BinOp::AShr
        | BinOp::BitAnd
        | BinOp::BitOr
        | BinOp::BitXor
        | BinOp::And
        | BinOp::Or
        | BinOp::Eq
        | BinOp::Neq
        | BinOp::Lt
        | BinOp::Le
        | BinOp::Gt
        | BinOp::Ge
        | BinOp::SLt
        | BinOp::SLe
        | BinOp::SGt
        | BinOp::SGe => (),
    }
};
