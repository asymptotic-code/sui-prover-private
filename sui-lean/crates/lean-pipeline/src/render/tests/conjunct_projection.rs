//! Renderer conjunct-projection regressions: named `.c<k>` leaf defs +
//! the `_conj` characterization theorem, for the four conjunction shapes
//! (fused `&&`, pure-Bool short-circuit ite, world-pair ite, `Prop`
//! ensures/requires) plus the arity-1 no-emission case.
//!
//! These assert the emitted STRUCTURE (names, connective, proof term).
//! The `rfl` / `Iff.rfl` proofs themselves are checked end-to-end by the
//! ember lake gate.

use crate::ir::{BinOp, Block, BlockTail, Const, Expr, FunctionKind, SpecKind, Stmt, Type, VarId};
use crate::render::render_program;

use super::fixtures::*;

fn bool_param(name: &str) -> crate::ir::Param {
    param(name, Type::Bool)
}

fn and(lhs: Expr, rhs: Expr) -> Expr {
    Expr::BinOp {
        op: BinOp::And,
        lhs: Box::new(lhs),
        rhs: Box::new(rhs),
    }
}

fn bool_lit(b: bool) -> Expr {
    Expr::Const(Const::Bool(b))
}

fn just_value(e: Expr) -> Block {
    Block {
        stmts: vec![],
        tail: BlockTail::Value(e),
    }
}

/// Install `f` as a `Spec` companion of a trivial target `Source` fn, so
/// the render loop routes it through the standalone (non-mutual) path.
fn program_with_companion(
    name: &str,
    sig_: crate::ir::Signature,
    body_: Block,
    ret: Type,
) -> String {
    let mut prog = empty_program();
    let target = func(
        "impl",
        sig(vec![], Type::Bool),
        just_value(bool_lit(true)),
        0,
    );
    add_function(&mut prog, 0, target);
    let mut companion = func(name, sig_, body_, 0);
    companion.kind = FunctionKind::Spec {
        kind: match () {
            _ if name.ends_with(".ensures") => SpecKind::Ensures,
            _ if name.ends_with(".requires") => SpecKind::Requires,
            _ => SpecKind::Asserts,
        },
        target: 0,
    };
    companion.signature.return_type = ret;
    add_function(&mut prog, 1, companion);
    render_program(&prog).expect("program renders")
}

#[test]
fn fused_and_emits_leaves_and_eq_theorem() {
    // asserts : Bool := (a && b)   -- two fused leaves.
    let out = program_with_companion(
        "foo_spec.asserts",
        sig(vec![bool_param("a"), bool_param("b")], Type::Bool),
        just_value(and(var("a"), var("b"))),
        Type::Bool,
    );
    assert!(
        out.contains("def foo_spec.asserts.c1"),
        "missing c1:\n{out}"
    );
    assert!(
        out.contains("def foo_spec.asserts.c2"),
        "missing c2:\n{out}"
    );
    assert!(
        !out.contains("foo_spec.asserts.c3"),
        "unexpected c3:\n{out}"
    );
    assert!(
        out.contains("theorem foo_spec.asserts_conj"),
        "missing conj theorem:\n{out}"
    );
    // Bool companion: `=` and `by rfl`, RHS is the named-leaf `&&` tree.
    assert!(
        out.contains(
            "foo_spec.asserts a b = ((foo_spec.asserts.c1 a b) && (foo_spec.asserts.c2 a b)) := by first | rfl | simp [foo_spec.asserts, foo_spec.asserts.c1, foo_spec.asserts.c2]"
        ),
        "unexpected conj statement/proof:\n{out}"
    );
    // The leaf bodies project each conjunct.
    assert!(out.contains("def foo_spec.asserts.c1 (a : Bool) (b : Bool) : Bool :=\n  a\n"));
    assert!(out.contains("def foo_spec.asserts.c2 (a : Bool) (b : Bool) : Bool :=\n  b\n"));
}

#[test]
fn left_nested_and_association_is_preserved() {
    // asserts : Bool := ((a && b) && c)  -- three leaves, left-nested.
    let out = program_with_companion(
        "tri_spec.asserts",
        sig(
            vec![bool_param("a"), bool_param("b"), bool_param("c")],
            Type::Bool,
        ),
        just_value(and(and(var("a"), var("b")), var("c"))),
        Type::Bool,
    );
    for k in 1..=3 {
        assert!(
            out.contains(&format!("def tri_spec.asserts.c{k}")),
            "missing c{k}:\n{out}"
        );
    }
    assert!(out.contains(
        "tri_spec.asserts a b c = (((tri_spec.asserts.c1 a b c) && (tri_spec.asserts.c2 a b c)) && (tri_spec.asserts.c3 a b c)) := by first | rfl | simp [tri_spec.asserts, tri_spec.asserts.c1, tri_spec.asserts.c2, tri_spec.asserts.c3]"
    ), "association not preserved:\n{out}");
}

#[test]
fn pure_bool_short_circuit_ite_leaf_is_reproduced() {
    // asserts : Bool := (let t := if g then a else false; (t && a))
    // Leaf c1 must reproduce the short-circuit ite verbatim.
    let body_ = Block {
        stmts: vec![Stmt::Let {
            pattern: vec![Some(VarId::from("t"))],
            value: Expr::If {
                cond: Box::new(var("g")),
                then_branch: Box::new(just_value(var("a"))),
                else_branch: Box::new(just_value(bool_lit(false))),
            },
        }],
        tail: BlockTail::Value(and(var("t"), var("a"))),
    };
    let out = program_with_companion(
        "sc_spec.asserts",
        sig(vec![bool_param("a"), bool_param("g")], Type::Bool),
        body_,
        Type::Bool,
    );
    assert!(out.contains("def sc_spec.asserts.c1"), "missing c1:\n{out}");
    assert!(out.contains("def sc_spec.asserts.c2"), "missing c2:\n{out}");
    // c1 reproduces the short-circuit ite (peephole inlines the tail
    // `let t`, leaving the ite as the leaf's tail -- rendered multi-line
    // in tail position, same term as the companion's inline `let` value).
    assert!(
        out.contains(
            "def sc_spec.asserts.c1 (a : Bool) (g : Bool) : Bool :=\n  if g then\n    a\n  else\n    false\n"
        ),
        "c1 did not reproduce the short-circuit ite:\n{out}"
    );
    // c2 is the bare second conjunct.
    assert!(out.contains("def sc_spec.asserts.c2 (a : Bool) (g : Bool) : Bool :=\n  a\n"));
    assert!(out.contains(
        "sc_spec.asserts a g = ((sc_spec.asserts.c1 a g) && (sc_spec.asserts.c2 a g)) := by first | rfl | simp [sc_spec.asserts, sc_spec.asserts.c1, sc_spec.asserts.c2]"
    ));
}

#[test]
fn world_pair_ite_tuple_let_survives_dce() {
    // asserts : Bool := (let (t, w2) := if g then (true, wrld) else (a, wrld); (t && a))
    // `wrld` stands in for a threaded World; the pair-let must be kept
    // WHOLE inside the leaf that needs `t` (a slot can't be split off).
    let body_ = Block {
        stmts: vec![Stmt::Let {
            pattern: vec![Some(VarId::from("t")), Some(VarId::from("w2"))],
            value: Expr::If {
                cond: Box::new(var("g")),
                then_branch: Box::new(just_value(Expr::Tuple(vec![bool_lit(true), var("wrld")]))),
                else_branch: Box::new(just_value(Expr::Tuple(vec![var("a"), var("wrld")]))),
            },
        }],
        tail: BlockTail::Value(and(var("t"), var("a"))),
    };
    let out = program_with_companion(
        "wp_spec.asserts",
        sig(
            vec![bool_param("a"), bool_param("g"), bool_param("wrld")],
            Type::Bool,
        ),
        body_,
        Type::Bool,
    );
    assert!(out.contains("def wp_spec.asserts.c1"), "missing c1:\n{out}");
    // c1 keeps the whole world-pair binding (both slots) plus the ite.
    assert!(
        out.contains("let (t, w2) := if g then (true, wrld) else (a, wrld)"),
        "world-pair tuple let not reproduced in a leaf:\n{out}"
    );
    // c2 (needs only `a`) drops the pair-let entirely.
    assert!(
        out.contains("def wp_spec.asserts.c2 (a : Bool) (g : Bool) (wrld : Bool) : Bool :=\n  a\n")
    );
    assert!(out.contains(
        "wp_spec.asserts a g wrld = ((wp_spec.asserts.c1 a g wrld) && (wp_spec.asserts.c2 a g wrld)) := by first | rfl | simp [wp_spec.asserts, wp_spec.asserts.c1, wp_spec.asserts.c2]"
    ));
}

#[test]
fn prop_ensures_uses_iff_and_iff_rfl() {
    // ensures : Prop := (a && b)  -- Prop (Bool-coerced) companion.
    let out = program_with_companion(
        "bar_spec.ensures",
        sig(vec![bool_param("a"), bool_param("b")], Type::Prop),
        just_value(and(var("a"), var("b"))),
        Type::Prop,
    );
    assert!(
        out.contains("def bar_spec.ensures.c1"),
        "missing c1:\n{out}"
    );
    assert!(
        out.contains("def bar_spec.ensures.c2"),
        "missing c2:\n{out}"
    );
    // Leaf defs are Bool even though the parent is Prop.
    assert!(out.contains("def bar_spec.ensures.c1 (a : Bool) (b : Bool) : Bool :=\n  a\n"));
    // Prop companion: `↔` and `Iff.rfl`.
    assert!(
        out.contains(
            "bar_spec.ensures a b ↔ ((bar_spec.ensures.c1 a b) && (bar_spec.ensures.c2 a b)) := by first | exact Iff.rfl | simp [bar_spec.ensures, bar_spec.ensures.c1, bar_spec.ensures.c2]"
        ),
        "prop companion must use ↔ / Iff.rfl:\n{out}"
    );
}

#[test]
fn requires_companion_also_projects() {
    let out = program_with_companion(
        "baz_spec.requires",
        sig(vec![bool_param("a"), bool_param("b")], Type::Prop),
        just_value(and(var("a"), var("b"))),
        Type::Prop,
    );
    assert!(out.contains("def baz_spec.requires.c1"));
    assert!(out.contains(
        "baz_spec.requires a b ↔ ((baz_spec.requires.c1 a b) && (baz_spec.requires.c2 a b)) := by first | exact Iff.rfl | simp [baz_spec.requires, baz_spec.requires.c1, baz_spec.requires.c2]"
    ));
}

#[test]
fn arity_one_asserts_emits_no_projection() {
    // asserts : Bool := a  -- single predicate, nothing to project.
    let out = program_with_companion(
        "single_spec.asserts",
        sig(vec![bool_param("a")], Type::Bool),
        just_value(var("a")),
        Type::Bool,
    );
    assert!(
        out.contains("def single_spec.asserts"),
        "companion itself missing:\n{out}"
    );
    assert!(
        !out.contains("single_spec.asserts.c1"),
        "arity-1 must not project:\n{out}"
    );
    assert!(
        !out.contains("single_spec.asserts_conj"),
        "arity-1 must not emit theorem:\n{out}"
    );
}

#[test]
fn aborts_companion_is_not_projected() {
    // `.aborts` is out of scope even when its body is a `&&` tree.
    let mut prog = empty_program();
    add_function(
        &mut prog,
        0,
        func(
            "impl",
            sig(vec![], Type::Bool),
            just_value(bool_lit(true)),
            0,
        ),
    );
    let mut companion = func(
        "q_spec.aborts",
        sig(vec![bool_param("a"), bool_param("b")], Type::Bool),
        just_value(and(var("a"), var("b"))),
        0,
    );
    companion.kind = FunctionKind::Spec {
        kind: SpecKind::Aborts,
        target: 0,
    };
    add_function(&mut prog, 1, companion);
    let out = render_program(&prog).expect("program renders");
    assert!(
        out.contains("def q_spec.aborts"),
        "aborts companion missing:\n{out}"
    );
    assert!(
        !out.contains("q_spec.aborts.c1"),
        "aborts must not project:\n{out}"
    );
    assert!(
        !out.contains("q_spec.aborts_conj"),
        "aborts must not emit theorem:\n{out}"
    );
}
