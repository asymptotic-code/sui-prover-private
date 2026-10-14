//! Companion-function naming conventions -- single source of truth.
//!
//! The pipeline synthesizes companion functions whose relationship to
//! their source is carried structurally by [`super::FunctionKind`], but
//! whose NAMES follow dotted-suffix conventions consumed by the
//! renderer and by humans reading output:
//!
//! - `f.aborts` / `f.requires` / `f.ensures` -- spec companions
//! - `f.while_N` / `f.while_N.after` -- loop body / continuation helpers
//! - `f.cont_N` -- return-lift continuations
//! - `f.labeled_N` -- labeled-block helpers
//! - `f.asserts.c<k>` -- named leaf conjunct of a conjunction-tree
//!   companion, plus the `f.asserts_conj` characterization theorem
//!   (see [`conjunct_leaf_name`] / [`conj_theorem_name`]).
//!
//! Suffixes compose (`f.aborts.while_0.after`, `f.aborts.cont_1`).
//! Every `format!` that builds one of these names and every string
//! match that parses one back lives here. Native OP-name matching
//! (e.g. the df dispatch on `"add.aborts"` against registered native
//! decl names) is intentionally out of scope.

pub fn aborts_name(base: &str) -> String {
    format!("{base}.aborts")
}

pub fn requires_name(base: &str) -> String {
    format!("{base}.requires")
}

pub fn ensures_name(base: &str) -> String {
    format!("{base}.ensures")
}

pub fn while_name(base: &str, slot: u32) -> String {
    format!("{base}.while_{slot}")
}

pub fn after_name(base: &str, slot: u32) -> String {
    format!("{base}.while_{slot}.after")
}

pub fn cont_name(base: &str, slot: u32) -> String {
    format!("{base}.cont_{slot}")
}

pub fn labeled_name(base: &str, slot: u32) -> String {
    format!("{base}.labeled_{slot}")
}

/// `.asserts` spec companion -- the conjunction of a spec wrapper's
/// `prover::asserts(p)` predicates, exposed as a standalone `Prop`
/// (Bool) companion so the abort-faithfulness theorem can reference
/// it directly (the asserts are otherwise only folded into `.aborts`).
pub fn asserts_name(base: &str) -> String {
    format!("{base}.asserts")
}

/// Functional-correctness theorem name (`requires -> asserts ->
/// ensures`). Underscore suffix (not a dotted companion) -- this is a
/// proof obligation, not a predicate companion.
pub fn correct_theorem_name(base: &str) -> String {
    format!("{}_correct", theorem_base(base))
}

/// Assert-faithfulness theorem name (`impl.aborts <-> not asserts`):
/// the implementation aborts iff the spec author's `asserts` is
/// violated.
pub fn asserts_correct_theorem_name(base: &str) -> String {
    format!("{}_asserts_correct", theorem_base(base))
}

/// Named leaf-conjunct companion of a spec companion whose body is a
/// conjunction tree: `<companion>.c<k>` with 1-based `index` (e.g.
/// `mint_spec.asserts.c3`). Emitted next to the parent companion by the
/// renderer's conjunct-projection pass -- one `def` per top-level `&&`
/// leaf, exposing that predicate under a stable positional name so
/// downstream proofs (and the FvKit `spec_conjuncts` semantic-naming
/// command) can reference it without re-deriving `Bool.and_eq_true`
/// ladders. The parent companion body is unchanged; these are purely
/// additive.
pub fn conjunct_leaf_name(companion: &str, index: usize) -> String {
    format!("{companion}.c{index}")
}

/// Characterization-theorem name for a companion's conjunct projection:
/// `<companion>_conj` (e.g. `mint_spec.asserts_conj`). Underscore
/// suffix (not a dotted `.` companion) -- like `_correct`, this names a
/// theorem, not a predicate companion. Its statement equates the parent
/// companion to the `&&` (Bool companions) / `↔`-coerced (`Prop`
/// companions) of its named `c<k>` leaves; the proof is a fixed
/// `rfl`-class script.
pub fn conj_theorem_name(companion: &str) -> String {
    format!("{companion}_conj")
}

/// Name of the `axiom` declaration asserting a trusted obligation Prop
/// (`FunctionKind::Axiom`): `axiom <prop>_holds (params) : <ns>.<prop> args`.
pub fn axiom_holds_name(prop: &str) -> String {
    format!("{prop}_holds")
}

/// Obligation base name for a TARGETLESS prove-spec (`#[spec(prove)]`
/// with no `target=`): the wrapper's own name with `_spec` dropped, so a
/// standalone lemma reads like every other obligation
/// (`<lemma>_correct`, not `<lemma>_spec_correct`). A paired obligation
/// borrows the impl's name instead; here there is no impl. One rule, no
/// collision fallback -- `sui-lean`'s authoritative-roster mirror
/// (`planned_obligation_names`) reproduces it in one call.
pub fn targetless_obligation_base(wrapper_name: &str) -> &str {
    wrapper_name.strip_suffix("_spec").unwrap_or(wrapper_name)
}

fn theorem_base(base: &str) -> String {
    base.replace("::", "_").replace('.', "_")
}

pub fn is_aborts_name(name: &str) -> bool {
    name.ends_with(".aborts")
}

/// True for an `.aborts` companion and every helper derived from it.
///
/// Derived names compose after the marker (`f.aborts.while_0.after`,
/// `f.aborts.cont_1`), so exact-suffix recognition is intentionally too
/// narrow for questions about the whole logical abort-simulation family.
pub fn is_aborts_family_name(name: &str) -> bool {
    is_aborts_name(name) || name.contains(".aborts.")
}

pub(crate) fn world_ssa_generation(name: &str) -> Option<u64> {
    if name == crate::stage_04_effects::common::WORLD_VAR {
        return Some(0);
    }
    name.strip_prefix(crate::stage_04_effects::common::WORLD_VAR)?
        .strip_prefix('_')?
        .parse::<u64>()
        .ok()
        .and_then(|generation| generation.checked_add(1))
}

/// `"f.cont_3"` -> `Some("f")`. Rejects non-numeric or empty slot
/// suffixes (`"f.cont_"`, `"f.cont_x"`).
pub fn cont_parent(name: &str) -> Option<&str> {
    let pos = name.rfind(".cont_")?;
    let slot = &name[pos + ".cont_".len()..];
    if !slot.is_empty() && slot.bytes().all(|b| b.is_ascii_digit()) {
        Some(&name[..pos])
    } else {
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn builders() {
        assert_eq!(aborts_name("m::f"), "m::f.aborts");
        assert_eq!(requires_name("f"), "f.requires");
        assert_eq!(ensures_name("f"), "f.ensures");
        assert_eq!(while_name("f", 0), "f.while_0");
        assert_eq!(after_name("f", 2), "f.while_2.after");
        assert_eq!(cont_name("f.aborts", 1), "f.aborts.cont_1");
        assert_eq!(labeled_name("f", 4), "f.labeled_4");
        assert_eq!(asserts_name("f"), "f.asserts");
        assert_eq!(conjunct_leaf_name("f.asserts", 1), "f.asserts.c1");
        assert_eq!(
            conjunct_leaf_name("f_spec.ensures", 12),
            "f_spec.ensures.c12"
        );
        assert_eq!(conj_theorem_name("f.asserts"), "f.asserts_conj");
        assert_eq!(conj_theorem_name("f_spec.requires"), "f_spec.requires_conj");
        assert_eq!(correct_theorem_name("m::f"), "m_f_correct");
        assert_eq!(asserts_correct_theorem_name("f"), "f_asserts_correct");
        assert_eq!(axiom_holds_name("f_correct"), "f_correct_holds");
        assert_eq!(
            axiom_holds_name(&asserts_correct_theorem_name("f")),
            "f_asserts_correct_holds"
        );
    }

    #[test]
    fn theorem_names_preserve_companion_continuation_path() {
        assert_eq!(
            correct_theorem_name("pow_spec.aborts.cont_0.cont_0"),
            "pow_spec_aborts_cont_0_cont_0_correct"
        );
        assert_eq!(
            asserts_correct_theorem_name("pow_spec.aborts.cont_0"),
            "pow_spec_aborts_cont_0_asserts_correct"
        );
    }

    #[test]
    fn asserts_is_not_an_aborts_name() {
        // `.asserts` must not be misread as `.aborts` by `is_aborts_name`.
        assert!(!is_aborts_name(&asserts_name("f")));
    }

    #[test]
    fn aborts_recognition() {
        assert!(is_aborts_name(&aborts_name("f")));
        assert!(!is_aborts_name("f"));
        assert!(!is_aborts_name("f.aborts.while_0"));

        assert!(is_aborts_family_name("f.aborts"));
        assert!(is_aborts_family_name("f.aborts.while_0"));
        assert!(is_aborts_family_name("f.aborts.while_0.after"));
        assert!(is_aborts_family_name("f.aborts.cont_1"));
        assert!(!is_aborts_family_name("f.asserts.cont_1"));
        assert!(!is_aborts_family_name("aborts"));
    }

    #[test]
    fn world_generations_are_numeric_and_canonical_only() {
        assert_eq!(world_ssa_generation("world"), Some(0));
        assert_eq!(world_ssa_generation("world_0"), Some(1));
        assert_eq!(world_ssa_generation("world_10"), Some(11));
        assert_eq!(world_ssa_generation("world_snapshot"), None);
        assert_eq!(world_ssa_generation("some_world_1"), None);
    }

    #[test]
    fn cont_parent_roundtrip() {
        assert_eq!(cont_parent(&cont_name("f", 3)), Some("f"));
        assert_eq!(cont_parent(&cont_name("f.aborts", 12)), Some("f.aborts"));
        assert_eq!(cont_parent("f.cont_"), None);
        assert_eq!(cont_parent("f.cont_x"), None);
        assert_eq!(cont_parent("f"), None);
    }
}
