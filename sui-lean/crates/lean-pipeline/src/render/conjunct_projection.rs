//! Conjunct projections: additive named leaves + a characterization
//! theorem for a spec companion whose body is a conjunction tree.
//!
//! For each `.asserts` / `.ensures` / `.requires` companion whose body
//! ends in a top-level `&&` tree of arity >= 2, this pass emits -- right
//! after the companion, whose body stays BYTE-IDENTICAL:
//!
//! 1. one `def <companion>.c<k> <binders> : Bool := <leaf_k>` per
//!    top-level `&&` leaf (`k` 1-based, in left-to-right tree order).
//!    The leaf body reuses the companion's exact binder segment and is
//!    the companion body dead-let-eliminated down to just the lets the
//!    leaf transitively needs (so world-threading `let (t, w') := ...`
//!    pairs and nested short-circuit `if g then .. else false` /
//!    world-pair ites are reproduced verbatim inside the leaf they feed
//!    -- no intermediate-world args, no cases-cascade).
//! 2. one `theorem <companion>_conj <binders> : <companion> <args>
//!    <op> (c1 <args> && (c2 <args> && ..))` where `<op>` is `=` for a
//!    Bool companion and `↔` for a `Prop` (`Bool`-coerced) companion.
//!    The RHS reproduces the companion's exact `&&` association with
//!    each leaf replaced by `<companion>.c<k> <args>`, so the proof is a
//!    deterministic `unfold <leaves>; rfl` (Bool) / `..; exact Iff.rfl`
//!    (Prop) script: each leaf def is definitionally the corresponding
//!    conjunct in context, and unfolding the leaves first sidesteps the
//!    elaborator's let-telescope isDefEq incompleteness on deep leaf
//!    chains (a bare `rfl` fails on sui-system advance_epoch
//!    conservation c9 despite the equation being kernel-true).
//!
//! Scope note (disclosed): the top-level split is by `&&` (Bool `And`)
//! only. A companion whose whole body is a single short-circuit-ite /
//! world-pair-ite chain (no top-level `&&`) is arity-1 and gets no
//! projection -- among ember spec companions those are the genuine
//! single-predicate cases. Short-circuit / world-pair substructures
//! that FEED a top-level `&&` leaf are handled as leaf-internal detail,
//! which is why the proof stays uniformly `rfl`.
//!
//! These are rendered TEXT only: no IR `Function`, no `FunctionKind`, so
//! they are invisible to the obligation manifest / roster, and the
//! statement-freeze gate (which compares companion bodies) is unmoved.

use std::collections::BTreeSet;
use std::fmt::Write;

use crate::ir::analysis::free_vars::free_vars_of_expr;
use crate::ir::{
    BinOp, Block, BlockTail, Expr, Function, FunctionKind, SpecKind, Stmt, Type, VarId,
};

use super::escape;
use super::expr::{render_function_body, ExprCtx};
use super::writer::LeanWriter;
use super::RenderResult;

/// A leaf-index-annotated mirror of the companion's top-level `&&`
/// tree. `Leaf(k)` is the k-th conjunct in left-to-right order; `And`
/// preserves the exact association so the reconstructed RHS is `rfl`-
/// equal to the companion body.
enum ConjTree {
    Leaf(usize),
    And(Box<ConjTree>, Box<ConjTree>),
}

/// Split `e` into its top-level `&&` tree, pushing each leaf expression
/// into `leaves` in left-to-right order. A non-`&&` expression is a
/// single leaf.
fn build_conj_tree<'a>(e: &'a Expr, leaves: &mut Vec<&'a Expr>) -> ConjTree {
    if let Expr::BinOp {
        op: BinOp::And,
        lhs,
        rhs,
    } = e
    {
        let l = build_conj_tree(lhs, leaves);
        let r = build_conj_tree(rhs, leaves);
        ConjTree::And(Box::new(l), Box::new(r))
    } else {
        let idx = leaves.len();
        leaves.push(e);
        ConjTree::Leaf(idx)
    }
}

/// Render the characterization-theorem RHS: the companion's `&&` tree
/// with each leaf replaced by a fully-parenthesized `<companion>.c<k>
/// <args>` application. Fully parenthesizing every node keeps the term
/// unambiguous regardless of `&&` / application precedence.
fn rhs_text(tree: &ConjTree, companion: &str, applied: &str) -> String {
    match tree {
        ConjTree::Leaf(i) => {
            let leaf = crate::ir::names::conjunct_leaf_name(companion, i + 1);
            // `applied` already carries a leading space per arg.
            format!("({}{})", escape::escape_identifier(&leaf), applied)
        }
        ConjTree::And(l, r) => format!(
            "({} && {})",
            rhs_text(l, companion, applied),
            rhs_text(r, companion, applied)
        ),
    }
}

/// Build the dead-let-eliminated block whose value is `leaf`: keep only
/// the top-level statements (in original order) that `leaf` transitively
/// depends on. `Stmt::Eval` (discarded `let _ := ..`) statements bind
/// nothing and are always dropped. Multi-var tuple `let`s are kept whole
/// (a slot cannot be split off), so world-threading pairs survive intact.
fn dce_block_for_leaf(body: &Block, leaf: &Expr) -> Block {
    let mut needed: BTreeSet<VarId> = free_vars_of_expr(leaf);
    let mut kept_rev: Vec<Stmt> = Vec::new();
    for stmt in body.stmts.iter().rev() {
        match stmt {
            Stmt::Let { pattern, value } => {
                let binds: Vec<&VarId> = pattern.iter().flatten().collect();
                if binds.iter().any(|v| needed.contains(*v)) {
                    for v in &binds {
                        needed.remove(*v);
                    }
                    needed.extend(free_vars_of_expr(value));
                    kept_rev.push(stmt.clone());
                }
            }
            Stmt::Eval(_) => {}
        }
    }
    kept_rev.reverse();
    Block {
        stmts: kept_rev,
        tail: BlockTail::Value(leaf.clone()),
    }
}

/// Emit the conjunct projections for `func` (a spec companion) into `w`,
/// reusing the companion's captured binder segment `sig` and its ordered
/// type-param / value-param names. Emits nothing (returns `Ok(())`)
/// unless `func` is a non-aborts `.asserts` / `.ensures` / `.requires`
/// companion whose body is a top-level `&&` tree of arity >= 2 with no
/// implicit universe binders. All-or-nothing: the whole block is built
/// into a buffer first and only flushed when every leaf renders and
/// stays parameter-closed, so a companion never gets a partial set.
pub(in crate::render) fn emit_conjunct_projections<W: Write>(
    func: &Function,
    ctx: &ExprCtx<'_>,
    sig: &str,
    tp_names: &[String],
    pnames: &[String],
    w: &mut LeanWriter<W>,
) -> RenderResult<()> {
    // Only the three value-predicate spec companions. `.aborts` carries
    // abort-order semantics (split-based abort_peel is the right tool
    // there, not conjunct projection) and everything else is out of
    // scope.
    match func.kind {
        FunctionKind::Spec {
            kind: SpecKind::Asserts | SpecKind::Requires | SpecKind::Ensures,
            ..
        } => {}
        _ => return Ok(()),
    }
    // An implicit universe binder (`{__TyU}` / `{__BagU}` / `{__ObjU}`)
    // is uninferable from the explicit args when the companion is
    // re-applied inside the theorem, so skip such companions. In
    // practice these only arise in lemma packages; user-package spec
    // companions (the whole target corpus) never carry one.
    if sig.contains('{') {
        return Ok(());
    }

    // Peel an optional `ToProp` and decide the connective: `=` for a
    // Bool companion, `↔` for a `Prop` (Bool-coerced) one.
    let BlockTail::Value(tail) = &func.body.tail else {
        return Ok(());
    };
    let (top, coerced) = match tail {
        Expr::ToProp(inner) => (inner.as_ref(), true),
        other => (other, false),
    };
    let is_prop = coerced || matches!(func.signature.return_type, Type::Prop);

    let mut leaves: Vec<&Expr> = Vec::new();
    let tree = build_conj_tree(top, &mut leaves);
    if leaves.len() < 2 {
        return Ok(());
    }

    // Applied-args suffix: explicit type params (escaped) then value
    // params, in declaration order -- matching the companion's own
    // calling convention (instance / universe binders are inferred).
    let mut applied = String::new();
    for tp in tp_names {
        applied.push(' ');
        applied.push_str(&escape::escape_identifier(tp));
    }
    for pn in pnames {
        applied.push(' ');
        applied.push_str(pn);
    }

    // Parameter closure guard: a leaf must reference only function
    // params (top-level `&&` conjuncts always do -- the IR validator
    // rejects a reference to a var bound only inside a nested branch).
    // If a dead-let-eliminated leaf is not parameter-closed, something
    // is off-pattern; skip the whole companion rather than emit a def
    // with an unbound identifier.
    let param_vars: BTreeSet<VarId> = func
        .signature
        .params
        .iter()
        .map(|p| p.var.clone())
        .collect();

    let companion = &func.name;
    let esc_companion = escape::escape_identifier(companion);

    let mut out = LeanWriter::new(String::new());
    for (i, leaf) in leaves.iter().enumerate() {
        let dced = dce_block_for_leaf(&func.body, leaf);
        let leaf_free = crate::ir::analysis::free_vars::free_vars(&dced);
        if !leaf_free.is_subset(&param_vars) {
            return Ok(());
        }
        let leaf_name = crate::ir::names::conjunct_leaf_name(companion, i + 1);
        out.write("def ");
        out.write(&escape::escape_identifier(&leaf_name));
        out.write(sig);
        out.write(" : Bool :=");
        out.indent(true);
        // Reuses the same body machinery the companion went through, so
        // the leaf's rendered value is definitionally the conjunct in
        // context. A render error is impossible here (the full body
        // already rendered and this is a subset), but propagate it if
        // it ever fires.
        render_function_body(&dced, ctx, &mut out)?;
        out.dedent(false);
        out.newline();
        out.newline();
    }

    // Characterization theorem.
    let thm_name = crate::ir::names::conj_theorem_name(companion);
    out.write("theorem ");
    out.write(&escape::escape_identifier(&thm_name));
    out.write(sig);
    out.write(" : ");
    out.write(&esc_companion);
    out.write(&applied);
    out.write(if is_prop { " ↔ " } else { " = " });
    out.write(&rhs_text(&tree, companion, &applied));
    // Proof: `rfl` (/ `Iff.rfl`) closes every companion whose leaf
    // unfoldings stay small -- the equation is definitionally true by
    // construction. On companions with a very deep dead-let-eliminated
    // leaf (sui-system advance_epoch conservation c9: a ~30-let chain
    // against the parent's 62-let spine) the elaborator's isDefEq gives
    // up even though the kernel accepts the equality (verified via
    // unfold/delta/raw-text probes), so fall back to `simp` seeded with
    // exactly the companion and leaf names: its equation-lemma rewrite
    // plus default zeta normalization closes the same goal in ~1s. The
    // cascade is a fixed two-arm script -- no search space beyond it.
    out.write(" := by first | ");
    out.write(if is_prop { "exact Iff.rfl" } else { "rfl" });
    out.write(" | simp [");
    out.write(&esc_companion);
    for i in 1..=leaves.len() {
        out.write(", ");
        out.write(&escape::escape_identifier(
            &crate::ir::names::conjunct_leaf_name(companion, i),
        ));
    }
    out.write("]");
    out.newline();
    out.newline();

    w.write(&out.into_inner());
    Ok(())
}
