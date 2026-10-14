//! `escape_identifier` keyword-collision regression tests. The
//! renderer emits a number of bare identifiers (`default`,
//! `initialize`, `if`, ...) that collide with either Lean keywords
//! or Lean type-class methods like `Inhabited.default`. The
//! `escape_identifier` map must rewrite every such Move name to a
//! `<name>_` form before it reaches Lean.

use super::super::escape::escape_identifier;

#[test]
fn unknown_identifier_passes_through() {
    // Identifiers not on the collision list survive verbatim. The
    // `escape_identifier` map is conservative -- only known
    // collisions get a `_` suffix.
    assert_eq!(escape_identifier("foo"), "foo");
    assert_eq!(escape_identifier("bar_baz"), "bar_baz");
    assert_eq!(escape_identifier("CamelCase"), "CamelCase");
}

#[test]
fn underscore_param_is_renamed_to_arg() {
    // A Move parameter literally named `_` is allowed (it signals
    // "intentionally unused"), but Lean reads bare `_` as the
    // inference placeholder. The escape rewrites to `_arg` so the
    // parameter is a real binder.
    assert_eq!(escape_identifier("_"), "_arg");
}

#[test]
fn dollar_prefix_normalises_to_t_prefix() {
    // Stage-5 SSA fresh vars are `$t0`, `$t1`, ... -- a leading `$`
    // is illegal in Lean, so the escape rewrites to `t_t0`, etc.
    // Internal `$` characters get the `_t_` infix.
    assert_eq!(escape_identifier("$t0"), "t_t0");
    assert_eq!(escape_identifier("$t12"), "t_t12");
    assert_eq!(escape_identifier("a$b"), "a_t_b");
}

#[test]
fn hash_is_underscored() {
    // `#` is illegal in Lean identifiers; map to `_`.
    assert_eq!(escape_identifier("foo#1"), "foo_1");
}

#[test]
fn colon_colon_qualifier_is_underscored() {
    // Move's `::` is illegal in Lean identifiers; map to `_` so the
    // rendered stub at least parses.
    assert_eq!(escape_identifier("prover::asserts"), "prover_asserts");
}

// ---- keyword collisions: must get a `_` suffix ----

#[test]
fn default_is_escaped_to_default_underscore() {
    // The renderer emits bare `default` for `Inhabited.default` as
    // a polymorphic placeholder (BorrowMapKey writeback fallback
    // lambdas, struct-field stubs). A Move function literally
    // named `default` (e.g. current-lending::protocol::Referral::default)
    // would otherwise shadow the type-class method.
    assert_eq!(escape_identifier("default"), "default_");
}

#[test]
fn initialize_is_escaped() {
    // `initialize` is Lean's module-initializer keyword and a
    // very common Move function name.
    assert_eq!(escape_identifier("initialize"), "initialize_");
}

#[test]
fn include_is_escaped() {
    // `include` is Lean's theorem-variable inclusion keyword;
    // collides with the Move parameter idiom `(include: bool)`
    // (e.g. `find_next` in `skip_list` / `linked_table`).
    assert_eq!(escape_identifier("include"), "include_");
}

#[test]
fn boolean_literal_names_are_escaped() {
    // `true` / `false` are Lean literals.
    assert_eq!(escape_identifier("true"), "true_");
    assert_eq!(escape_identifier("false"), "false_");
}

#[test]
fn control_flow_keywords_are_escaped() {
    // A representative sample of Lean control-flow keywords. Each
    // collides with valid Move identifiers and must be rewritten.
    for kw in &["if", "then", "else", "let", "in", "do", "match", "fun"] {
        assert_eq!(escape_identifier(kw), format!("{}_", kw));
    }
}

#[test]
fn declaration_keywords_are_escaped() {
    for kw in &[
        "axiom",
        "theorem",
        "lemma",
        "def",
        "abbrev",
        "structure",
        "inductive",
        "instance",
        "class",
        "namespace",
        "section",
        "variable",
        "import",
        "open",
    ] {
        assert_eq!(escape_identifier(kw), format!("{}_", kw));
    }
}

#[test]
fn type_quantifier_keywords_are_escaped() {
    // `Type`, `Prop`, `Sort` are valid Move type-parameter names
    // that conflict with Lean's universe markers.
    for kw in &["forall", "exists", "Type", "Prop", "Sort"] {
        assert_eq!(escape_identifier(kw), format!("{}_", kw));
    }
}

#[test]
fn end_keyword_is_escaped() {
    // `end` closes Lean `namespace ... end` blocks; valid Move
    // function name otherwise.
    assert_eq!(escape_identifier("end"), "end_");
}
