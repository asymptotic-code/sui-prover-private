//! `obligations.toml`'s `[[spec_no_obligation]]` section: the declared
//! `#[spec(prove)]` wrappers stage 12 emitted nothing for. It is the only
//! machine-readable record of that class -- `proof_status.toml` counts it
//! straight from here -- so the derivation is pinned by name.

use std::collections::BTreeMap;

use crate::ir::{Block, BlockTail, Expr, FunctionKind, Type};

use super::fixtures::*;

const IMPL: crate::ir::FunId = 0;
const WRAPPER: crate::ir::FunId = 1;
const LEMMA: crate::ir::FunId = 2;
const OBLIGATION: crate::ir::FunId = 3;

fn unit_body() -> Block {
    Block {
        stmts: Vec::new(),
        tail: BlockTail::Value(Expr::Const(crate::ir::Const::Bool(true))),
    }
}

fn unproduced(raw: &str) -> Vec<(String, String)> {
    let parsed: toml::Value = toml::from_str(raw).expect("manifest parses");
    parsed
        .get("spec_no_obligation")
        .map(|rows| {
            rows.as_array()
                .expect("array")
                .iter()
                .map(|row| {
                    (
                        row["source"].as_str().unwrap().to_string(),
                        row["reason"].as_str().unwrap().to_string(),
                    )
                })
                .collect()
        })
        .unwrap_or_default()
}

fn manifest(prog: &crate::ir::Program) -> String {
    let temp = tempfile::tempdir().unwrap();
    let mut fingerprints: BTreeMap<(String, String), String> = BTreeMap::new();
    for f in prog.functions.values() {
        if matches!(f.kind, FunctionKind::Theorem { .. }) {
            fingerprints.insert(("p.M".to_string(), f.name.clone()), "0".repeat(64));
        }
    }
    super::super::write_obligations_manifest(prog, temp.path(), &fingerprints).expect("manifest");
    std::fs::read_to_string(temp.path().join("obligations.toml")).unwrap()
}

fn base_program() -> crate::ir::Program {
    let mut prog = empty_program();
    add_function(
        &mut prog,
        IMPL,
        func("foo", sig(vec![], Type::Bool), unit_body(), 0),
    );
    add_function(
        &mut prog,
        WRAPPER,
        func("foo_spec", sig(vec![], Type::Bool), unit_body(), 0),
    );
    add_function(
        &mut prog,
        LEMMA,
        func("frozen_rate_spec", sig(vec![], Type::Bool), unit_body(), 0),
    );
    prog.spec_to_impl.insert(WRAPPER, IMPL);
    prog.targetless_prove_specs.insert(LEMMA);
    prog
}

#[test]
fn prove_specs_that_emitted_nothing_are_listed_with_their_reason() {
    let raw = manifest(&base_program());
    assert_eq!(
        unproduced(&raw),
        vec![
            ("p::m::foo_spec".to_string(), "no_ensures".to_string()),
            (
                "p::m::frozen_rate_spec".to_string(),
                "no_target_and_no_ensures".to_string()
            ),
        ],
        "{raw}"
    );
}

#[test]
fn a_prove_spec_that_produced_an_obligation_is_not_listed() {
    let mut prog = base_program();
    let mut theorem = func("foo_correct", sig(vec![], Type::Bool), unit_body(), 0);
    theorem.kind = FunctionKind::Theorem {
        target: IMPL,
        source: WRAPPER,
    };
    add_function(&mut prog, OBLIGATION, theorem);

    let raw = manifest(&prog);
    assert_eq!(
        unproduced(&raw),
        vec![(
            "p::m::frozen_rate_spec".to_string(),
            "no_target_and_no_ensures".to_string()
        )],
        "{raw}"
    );
}

/// A clean corpus writes the section away entirely -- the counter reads 0
/// because nothing is listed, not because the field was omitted.
#[test]
fn a_corpus_with_no_unproduced_prove_specs_lists_nothing() {
    let mut prog = empty_program();
    add_function(
        &mut prog,
        IMPL,
        func("foo", sig(vec![], Type::Bool), unit_body(), 0),
    );
    let raw = manifest(&prog);
    assert!(unproduced(&raw).is_empty(), "{raw}");
}

/// A declared prove-spec that reached NEITHER map -- its `target=` has no
/// IR function, or the wrapper itself was never lifted -- has no `FunId`
/// for the reconciliation above to find it by, so stage 2 hands it over
/// pre-named. Before this it was an eprintln and nothing else: the render
/// log said so once, `obligations.toml` did not, and every downstream
/// counter read the request as absent rather than as unmet.
#[test]
fn a_prove_spec_that_never_reached_either_map_is_disclosed_by_name() {
    let mut prog = empty_program();
    prog.unmapped_prove_specs.insert((
        "p::m::orphan_target_spec".to_string(),
        "target_not_translated".to_string(),
    ));
    prog.unmapped_prove_specs.insert((
        "p::m::unlifted_spec".to_string(),
        "wrapper_not_translated".to_string(),
    ));

    let raw = manifest(&prog);
    assert_eq!(
        unproduced(&raw),
        vec![
            (
                "p::m::orphan_target_spec".to_string(),
                "target_not_translated".to_string()
            ),
            (
                "p::m::unlifted_spec".to_string(),
                "wrapper_not_translated".to_string()
            ),
        ],
        "{raw}"
    );
}

/// A paired prove-spec whose wrapper never grew a translated body is
/// absent from `functions`, which is where the reconciliation reads names.
/// It must still be named -- from `prove_spec_names`, captured while the
/// Move model was in scope -- because skipping it is exactly the silence
/// this section exists to prevent.
#[test]
fn a_paired_prove_spec_with_no_translated_body_is_still_disclosed() {
    let mut prog = empty_program();
    add_function(
        &mut prog,
        IMPL,
        func("foo", sig(vec![], Type::Bool), unit_body(), 0),
    );
    prog.spec_to_impl.insert(WRAPPER, IMPL);
    prog.targetless_prove_specs.insert(LEMMA);
    prog.prove_spec_names
        .insert(WRAPPER, "p::m::foo_spec".to_string());
    prog.prove_spec_names
        .insert(LEMMA, "p::m::frozen_rate_spec".to_string());

    let raw = manifest(&prog);
    assert_eq!(
        unproduced(&raw),
        vec![
            ("p::m::foo_spec".to_string(), "no_ensures".to_string()),
            (
                "p::m::frozen_rate_spec".to_string(),
                "no_target_and_no_ensures".to_string()
            ),
        ],
        "{raw}"
    );
}

/// The whole point, stated as one property: for EVERY declared prove-spec,
/// the manifest carries either an `[[obligation]]` or a
/// `[[spec_no_obligation]]`. Producing neither is the defect -- 16 bluefin
/// and 11 momentum requested proofs vanished that way, and a `0` in the
/// disclosure counter was read as full coverage.
#[test]
fn every_declared_prove_spec_is_either_an_obligation_or_a_disclosure() {
    let mut prog = base_program();
    // Fourth shape: declared, but neither end resolved to a `FunId`.
    prog.unmapped_prove_specs.insert((
        "p::m::unlifted_spec".to_string(),
        "wrapper_not_translated".to_string(),
    ));
    // The paired wrapper is the one that DID produce a theorem.
    let mut theorem = func("foo_correct", sig(vec![], Type::Bool), unit_body(), 0);
    theorem.kind = FunctionKind::Theorem {
        target: IMPL,
        source: WRAPPER,
    };
    add_function(&mut prog, OBLIGATION, theorem);

    let raw = manifest(&prog);
    let parsed: toml::Value = toml::from_str(&raw).expect("manifest parses");
    let proved: Vec<String> = parsed
        .get("obligation")
        .map(|rows| {
            rows.as_array()
                .expect("array")
                .iter()
                .map(|row| row["source"].as_str().unwrap().to_string())
                .collect()
        })
        .unwrap_or_default();
    let disclosed: Vec<String> = unproduced(&raw).into_iter().map(|(s, _)| s).collect();

    for declared in [
        "p::m::foo_spec",
        "p::m::frozen_rate_spec",
        "p::m::unlifted_spec",
    ] {
        assert!(
            proved.contains(&declared.to_string()) || disclosed.contains(&declared.to_string()),
            "`{declared}` is declared `#[spec(prove)]` and appears in neither section: {raw}"
        );
    }
}

/// Trusted specs are a different class: they are ASSUMED, so producing no
/// theorem is their normal state and counting them here would make the
/// number unreadable.
#[test]
fn trusted_specs_are_not_counted_as_unproduced_prove_specs() {
    let mut prog = empty_program();
    add_function(
        &mut prog,
        IMPL,
        func("foo", sig(vec![], Type::Bool), unit_body(), 0),
    );
    add_function(
        &mut prog,
        WRAPPER,
        func("foo_spec", sig(vec![], Type::Bool), unit_body(), 0),
    );
    prog.trusted_spec_to_impl
        .insert(WRAPPER, (IMPL, crate::ir::TrustReason::NonProve));

    let raw = manifest(&prog);
    assert!(unproduced(&raw).is_empty(), "{raw}");
}
