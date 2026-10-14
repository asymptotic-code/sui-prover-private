use std::path::{Path, PathBuf};

use crate::render::{
    apply_source_proof_updates, durable_proof_stub_source, proof_fingerprint_marker, ProofFilePlan,
    ProofStub, SourceProofUpdate, PROOF_SOURCE_MARKER, PROOF_SOURCE_VERSION,
};

struct LakeFixture {
    _temp: tempfile::TempDir,
    proofs: PathBuf,
}

impl LakeFixture {
    fn new() -> Self {
        let temp = tempfile::tempdir().unwrap();
        let proofs = temp.path().join("lean");
        std::fs::create_dir_all(proofs.join("Playground")).unwrap();
        Self {
            _temp: temp,
            proofs,
        }
    }

    fn proof(&self, stem: &str) -> PathBuf {
        self.proofs
            .join("Playground")
            .join(format!("{stem}_Proofs.lean"))
    }

    fn apply(&self, updates: &[SourceProofUpdate]) -> crate::render::RenderResult<()> {
        apply_source_proof_updates(&self.proofs, updates)
    }
}

fn fingerprint(ch: char) -> String {
    std::iter::repeat_n(ch, 64).collect()
}

fn stub(name: &str, fingerprint: &str) -> ProofStub {
    ProofStub {
        name: name.to_string(),
        source: format!("theorem _root_.{name} : Playground.Math.{name} := by sorry\n"),
        fingerprint: fingerprint.to_string(),
        generated_prop: format!("Playground.Math.{name}"),
        generated_statement: format!("def Playground.Math.{name} : Prop := True\n"),
        proof_declaration_sha256: std::iter::repeat_n('d', 64).collect(),
    }
}

fn update_with(path: PathBuf, root: &str, mut stubs: Vec<ProofStub>) -> SourceProofUpdate {
    for stub in &mut stubs {
        stub.source =
            durable_proof_stub_source(&stub.name, &stub.fingerprint, root, &stub.source).unwrap();
    }
    let body = format!(
        "-- {PROOF_SOURCE_MARKER} {PROOF_SOURCE_VERSION}\nimport Playground.Math\n\n{}",
        stubs
            .iter()
            .map(|stub| stub.source.as_str())
            .collect::<String>()
    );
    SourceProofUpdate {
        path,
        root: root.to_string(),
        plan: ProofFilePlan {
            body,
            required_import: "Playground.Math".to_string(),
            stubs,
        },
    }
}

fn update(path: PathBuf) -> SourceProofUpdate {
    update_with(
        path,
        "Playground.Math_Proofs",
        vec![stub("pow_correct", &fingerprint('a'))],
    )
}

fn rooted_update(path: PathBuf, root: &str, stubs: Vec<ProofStub>) -> SourceProofUpdate {
    update_with(path, &format!("Playground.{root}_Proofs"), stubs)
}

fn write_proof(path: &Path, source: &str) {
    std::fs::create_dir_all(path.parent().unwrap()).unwrap();
    std::fs::write(path, source).unwrap();
}

#[test]
fn concurrent_updates_insert_a_missing_stub_once() {
    let fixture = LakeFixture::new();
    let proof = fixture.proof("Math");
    write_proof(&proof, "import Playground.Math\n\n");
    let worker_count = 4;
    let barrier = std::sync::Barrier::new(worker_count);

    std::thread::scope(|scope| {
        let mut handles = Vec::new();
        for _ in 0..worker_count {
            let barrier = &barrier;
            let fixture = &fixture;
            let proof = proof.clone();
            handles.push(scope.spawn(move || {
                barrier.wait();
                fixture.apply(&[update(proof)])
            }));
        }
        for handle in handles {
            handle.join().expect("update thread").expect("update");
        }
    });

    let rendered = std::fs::read_to_string(proof).unwrap();
    assert_eq!(
        rendered
            .matches("export Playground.Math_Proofs (pow_correct)")
            .count(),
        1
    );
    assert_eq!(
        rendered.matches("sui-lean:obligation-fingerprint").count(),
        1
    );
}

#[test]
fn missing_proof_source_is_seeded_as_managed() {
    let fixture = LakeFixture::new();
    let proof = fixture.proof("Math");

    fixture.apply(&[update(proof.clone())]).unwrap();

    let rendered = std::fs::read_to_string(proof).unwrap();
    assert!(rendered.starts_with("-- sui-lean:proof-source v1\n"));
    assert_eq!(
        rendered
            .matches("export Playground.Math_Proofs (pow_correct)")
            .count(),
        1
    );
    assert_eq!(
        rendered.matches("sui-lean:obligation-fingerprint").count(),
        1
    );
}

#[test]
fn matching_fingerprint_preserves_human_proof() {
    let fixture = LakeFixture::new();
    let proof = fixture.proof("Math");
    let hash = fingerprint('a');
    let source = format!(
        "import Playground.Math\n\n{}\ntheorem pow_correct : Playground.Math.pow_correct := by\n  -- human proof body may change\n  trivial\n",
        proof_fingerprint_marker("pow_correct", &hash)
    );
    write_proof(&proof, &source);

    fixture.apply(&[update(proof.clone())]).unwrap();

    assert_eq!(std::fs::read_to_string(proof).unwrap(), source);
}

#[test]
fn managed_source_inserts_an_unmentioned_stub_once() {
    let fixture = LakeFixture::new();
    let proof = fixture.proof("Math");
    let original =
        format!("-- {PROOF_SOURCE_MARKER} {PROOF_SOURCE_VERSION}\nimport Playground.Math\n");
    write_proof(&proof, &original);

    fixture.apply(&[update(proof.clone())]).unwrap();
    fixture.apply(&[update(proof.clone())]).unwrap();

    let rendered = std::fs::read_to_string(proof).unwrap();
    assert!(rendered.starts_with(&original));
    assert_eq!(
        rendered
            .matches("export Playground.Math_Proofs (pow_correct)")
            .count(),
        1
    );
    assert_eq!(
        rendered.matches("sui-lean:obligation-fingerprint").count(),
        1
    );
}

#[test]
fn managed_source_rejects_an_unmarked_obligation_reference() {
    let fixture = LakeFixture::new();
    let proof = fixture.proof("Math");
    let source = format!(
        "-- {PROOF_SOURCE_MARKER} {PROOF_SOURCE_VERSION}\nimport Playground.Math\n\ntheorem pow_correct : Playground.Math.pow_correct := by trivial\n"
    );
    write_proof(&proof, &source);

    let error = fixture.apply(&[update(proof.clone())]).unwrap_err();

    assert!(matches!(
        error,
        crate::render::RenderError::Io { what }
            if what.contains("without its fingerprint marker")
    ));
    assert_eq!(std::fs::read_to_string(proof).unwrap(), source);
}

#[test]
fn malformed_and_duplicate_proof_source_markers_fail_closed() {
    let fixture = LakeFixture::new();
    let proof = fixture.proof("Math");
    for source in [
        "-- sui-lean:proof-source\nimport Playground.Math\n",
        "-- sui-lean:proof-source v2\nimport Playground.Math\n",
        "-- sui-lean:proof-sourceX v1\nimport Playground.Math\n",
        "-- sui-lean:proof-source v1\n-- sui-lean:proof-source v1\nimport Playground.Math\n",
    ] {
        write_proof(&proof, source);

        let error = fixture.apply(&[update(proof.clone())]).unwrap_err();

        assert!(matches!(
            error,
            crate::render::RenderError::Io { what }
                if what.contains("invalid proof metadata")
        ));
        assert_eq!(std::fs::read_to_string(&proof).unwrap(), source);
    }
}

#[test]
fn legacy_name_occurrence_in_a_comment_safely_suppresses_insertion() {
    let fixture = LakeFixture::new();
    let proof = fixture.proof("Math");
    let source = "import Playground.Math\n\n-- pow_correct is intentionally discussed here\n";
    write_proof(&proof, source);

    fixture.apply(&[update(proof.clone())]).unwrap();

    assert_eq!(std::fs::read_to_string(proof).unwrap(), source);
}

/// Regression: bluefin `Pool_Proofs::{flash_swap_correct, swap_correct}`.
///
/// The legacy-file suppression scan must match a WHOLE Lean identifier. A
/// surviving `repay_flash_swap_correct` contains both names as substrings, and
/// under a plain `line.contains` it suppressed their stubs forever -- leaving
/// them `missing`, which is an audit integrity failure nobody sees until an
/// audit is run. 22 of bluefin's 608 theorem obligations sit on this trap.
#[test]
fn legacy_substring_of_a_longer_name_does_not_suppress_insertion() {
    let fixture = LakeFixture::new();
    let proof = fixture.proof("Math");
    let source = "import Playground.Math

                  theorem repay_flash_pow_correct : True := by trivial
";
    write_proof(&proof, source);

    fixture
        .apply(&[rooted_update(
            proof.clone(),
            "Math",
            vec![stub("pow_correct", &fingerprint('a'))],
        )])
        .unwrap();

    let updated = std::fs::read_to_string(&proof).unwrap();
    assert!(
        updated.contains(&proof_fingerprint_marker("pow_correct", &fingerprint('a'))),
        "the stub must be inserted -- `repay_flash_pow_correct` is a different \
         declaration, not this obligation:\n{updated}"
    );
    assert!(
        updated.contains("theorem repay_flash_pow_correct"),
        "existing content must be preserved byte-for-byte:\n{updated}"
    );
}

/// The dual: a REAL whole-identifier occurrence still suppresses, including
/// through a namespace prefix (`.` is not an identifier byte) and through Lean's
/// guillemet-quoted spelling.
#[test]
fn legacy_qualified_and_quoted_name_occurrences_still_suppress_insertion() {
    for mention in [
        "theorem t : Playground.Math_Proofs.pow_correct := by trivial",
        "theorem t : «pow_correct» := by trivial",
    ] {
        let fixture = LakeFixture::new();
        let proof = fixture.proof("Math");
        let source = format!("import Playground.Math\n\n{mention}\n");
        write_proof(&proof, &source);

        fixture.apply(&[update(proof.clone())]).unwrap();

        assert_eq!(
            std::fs::read_to_string(&proof).unwrap(),
            source,
            "a whole-identifier mention must still suppress: {mention}"
        );
    }
}

#[test]
fn legacy_macro_name_occurrence_is_preserved_for_audit() {
    let fixture = LakeFixture::new();
    let proof = fixture.proof("Math");
    let source = r#"import Lean
import Playground.Math

macro "declarePowCorrect " name:ident : command =>
  `(theorem $name : Playground.Math.pow_correct := by trivial)

declarePowCorrect pow_correct
"#;
    write_proof(&proof, source);

    fixture.apply(&[update(proof.clone())]).unwrap();

    assert_eq!(std::fs::read_to_string(proof).unwrap(), source);
}

#[test]
fn invalid_legacy_import_is_preserved_for_audit() {
    let fixture = LakeFixture::new();
    let proof = fixture.proof("Math");
    let source = "import Playground.Math\nimport Proofs.OnlyStale\n\ntheorem pow_correct : Playground.Math.pow_correct := by trivial\n";
    write_proof(&proof, source);

    fixture.apply(&[update(proof.clone())]).unwrap();

    assert_eq!(std::fs::read_to_string(proof).unwrap(), source);
}

#[test]
fn statement_drift_fails_before_inserting_any_missing_stub() {
    let fixture = LakeFixture::new();
    let proof = fixture.proof("Math");
    let recorded = fingerprint('a');
    let generated = fingerprint('b');
    let original = format!(
        "import Playground.Math\n\n{}\ntheorem pow_correct : Playground.Math.pow_correct := by trivial\n",
        proof_fingerprint_marker("pow_correct", &recorded)
    );
    write_proof(&proof, &original);
    let update = update_with(
        proof.clone(),
        "Playground.Math_Proofs",
        vec![
            stub("pow_correct", &generated),
            stub("fresh_correct", &fingerprint('c')),
        ],
    );

    let error = fixture.apply(&[update]).unwrap_err();

    assert!(matches!(
        error,
        crate::render::RenderError::ProofStatementDrift {
            obligation,
            recorded_fingerprint,
            generated_fingerprint,
            generated_statement,
            replacement_marker,
            ..
        } if obligation == "pow_correct"
            && recorded_fingerprint == format!("sha256:{recorded}")
            && generated_fingerprint == format!("sha256:{generated}")
            && generated_statement.contains("pow_correct")
            && replacement_marker == proof_fingerprint_marker("pow_correct", &generated)
    ));
    assert_eq!(std::fs::read_to_string(proof).unwrap(), original);
}

#[test]
fn character_literal_cannot_hide_drift_from_the_fingerprint_parser() {
    let fixture = LakeFixture::new();
    let proof = fixture.proof("Math");
    let recorded = fingerprint('a');
    let generated = fingerprint('b');
    let original = format!(
        "import Playground.Math\n\ndef quote : Char := '\"'\n{}\nthis stale proof no longer elaborates\n",
        proof_fingerprint_marker("pow_correct", &recorded)
    );
    write_proof(&proof, &original);
    let update = update_with(
        proof.clone(),
        "Playground.Math_Proofs",
        vec![stub("pow_correct", &generated)],
    );

    let error = fixture.apply(&[update]).unwrap_err();

    assert!(matches!(
        error,
        crate::render::RenderError::ProofStatementDrift { obligation, .. }
            if obligation == "pow_correct"
    ));
    assert_eq!(std::fs::read_to_string(proof).unwrap(), original);
}

#[test]
fn raw_and_interpolated_strings_cannot_hide_fingerprint_drift() {
    let fixture = LakeFixture::new();
    let proof = fixture.proof("Math");
    let recorded = fingerprint('a');
    let generated = fingerprint('b');
    for literal in [
        r##"def raw := r#"a"b"#"##,
        r##"def interpolated := s!"prefix {"\""} suffix""##,
        r##"def traced : Nat := dbg_trace "prefix {"\""} suffix"; 0"##,
        r##"def message : Lean.MessageData := m!"prefix {'"'} suffix""##,
    ] {
        let original = format!(
            "import Playground.Math\n\n{literal}\n{}\nthis stale proof no longer elaborates\n",
            proof_fingerprint_marker("pow_correct", &recorded)
        );
        write_proof(&proof, &original);
        let update = update_with(
            proof.clone(),
            "Playground.Math_Proofs",
            vec![stub("pow_correct", &generated)],
        );

        let error = fixture.apply(&[update]).unwrap_err();

        assert!(matches!(
            error,
            crate::render::RenderError::ProofStatementDrift { obligation, .. }
                if obligation == "pow_correct"
        ));
        assert_eq!(std::fs::read_to_string(&proof).unwrap(), original);
    }
}

#[test]
fn malformed_and_duplicate_markers_fail_closed() {
    let fixture = LakeFixture::new();
    let proof = fixture.proof("Math");
    let hash = fingerprint('a');
    let cases = [
        "import Playground.Math\n\n-- sui-lean:obligation-fingerprint\ntheorem pow_correct : Playground.Math.pow_correct := by trivial\n".to_string(),
        "import Playground.Math\n\n-- sui-lean:obligation-fingerprintX v1 name=pow_correct sha256=aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\ntheorem pow_correct : Playground.Math.pow_correct := by trivial\n".to_string(),
        format!(
            "import Playground.Math\n\n-- sui-lean:obligation-fingerprint v2 name=pow_correct sha256={hash}\ntheorem pow_correct : Playground.Math.pow_correct := by trivial\n"
        ),
        "import Playground.Math\n\n-- sui-lean:obligation-fingerprint v1 name=pow_correct sha256=1234\ntheorem pow_correct : Playground.Math.pow_correct := by trivial\n".to_string(),
        format!(
            "import Playground.Math\n\n{}\n{}\ntheorem pow_correct : Playground.Math.pow_correct := by trivial\n",
            proof_fingerprint_marker("pow_correct", &hash),
            proof_fingerprint_marker("pow_correct", &hash)
        ),
    ];
    for source in cases {
        write_proof(&proof, &source);

        let error = fixture.apply(&[update(proof.clone())]).unwrap_err();

        assert!(matches!(
            error,
            crate::render::RenderError::Io { what }
                if what.contains("invalid proof metadata")
        ));
        assert_eq!(std::fs::read_to_string(&proof).unwrap(), source);
    }
}

#[test]
fn obsolete_marker_metadata_is_preserved_but_not_part_of_the_manifest_audit() {
    let fixture = LakeFixture::new();
    let proof = fixture.proof("Math");
    let source = format!(
        "import Playground.Math\n\n{}\ntheorem pow_correct : Playground.Math.pow_correct := by trivial\n",
        proof_fingerprint_marker("missing_correct", &fingerprint('a'))
    );
    write_proof(&proof, &source);

    fixture.apply(&[update(proof.clone())]).unwrap();

    assert_eq!(std::fs::read_to_string(proof).unwrap(), source);
}

#[test]
fn marker_like_text_on_non_metadata_lines_is_ignored() {
    let fixture = LakeFixture::new();
    let proof = fixture.proof("Math");
    let fake = proof_fingerprint_marker("pow_correct", &fingerprint('b'));
    let source = format!(
        "import Playground.Math\n\ndef note := \"{fake}\"\ndef rawNote := r#\"{fake}\"#\n/- {fake} -/\ntheorem pow_correct : Playground.Math.pow_correct := by trivial\n"
    );
    write_proof(&proof, &source);

    fixture.apply(&[update(proof.clone())]).unwrap();

    assert_eq!(std::fs::read_to_string(proof).unwrap(), source);
}

#[test]
fn reserved_metadata_line_inside_lean_text_fails_closed() {
    let fixture = LakeFixture::new();
    let proof = fixture.proof("Math");
    let fake = proof_fingerprint_marker("pow_correct", &fingerprint('b'));
    let source = format!(
        "import Playground.Math\n\ndef rawNote := r#\"\n{fake}\n\"#\ntheorem pow_correct : Playground.Math.pow_correct := by trivial\n"
    );
    write_proof(&proof, &source);

    let error = fixture.apply(&[update(proof.clone())]).unwrap_err();

    assert!(matches!(
        error,
        crate::render::RenderError::ProofStatementDrift { .. }
    ));
    assert_eq!(std::fs::read_to_string(proof).unwrap(), source);
}

#[test]
fn batch_preflight_prevents_earlier_file_mutation_on_later_drift() {
    let fixture = LakeFixture::new();
    let first = fixture.proof("A");
    let second = fixture.proof("B");
    let recorded = fingerprint('a');
    let original = format!(
        "import Playground.Math\n\n{}\ntheorem pow_correct : Playground.Math.pow_correct := by trivial\n",
        proof_fingerprint_marker("pow_correct", &recorded)
    );
    write_proof(&second, &original);
    let updates = vec![
        rooted_update(
            first.clone(),
            "A",
            vec![stub("pow_correct", &fingerprint('a'))],
        ),
        rooted_update(
            second.clone(),
            "B",
            vec![stub("pow_correct", &fingerprint('b'))],
        ),
    ];

    let error = fixture.apply(&updates).unwrap_err();

    assert!(matches!(
        error,
        crate::render::RenderError::ProofStatementDrift { .. }
    ));
    assert!(!first.exists());
    assert_eq!(std::fs::read_to_string(second).unwrap(), original);
}

#[test]
fn missing_stub_is_inserted_before_a_broken_legacy_body() {
    let fixture = LakeFixture::new();
    let first = fixture.proof("A");
    let second = fixture.proof("B");
    let broken = "import Playground.Math\n\nthis is not a Lean command\n";
    write_proof(&second, broken);
    let updates = vec![
        rooted_update(
            first.clone(),
            "A",
            vec![stub("pow_correct", &fingerprint('a'))],
        ),
        rooted_update(
            second.clone(),
            "B",
            vec![stub("pow_correct", &fingerprint('a'))],
        ),
    ];

    fixture.apply(&updates).unwrap();

    assert!(first.exists());
    let second = std::fs::read_to_string(second).unwrap();
    assert!(second.contains("export Playground.B_Proofs (pow_correct)"));
    assert!(second.contains("this is not a Lean command"));
    assert!(
        second
            .find("export Playground.B_Proofs (pow_correct)")
            .unwrap()
            < second.find("this is not a Lean command").unwrap()
    );
}

#[test]
fn planned_files_reconcile_independently_when_one_imports_another() {
    let fixture = LakeFixture::new();
    let first = fixture.proof("A");
    let second = fixture.proof("B");
    let existing = "import Playground.Math\nimport Playground.B_Proofs\n\ntheorem pow_correct : Playground.Math.pow_correct := by trivial\n";
    write_proof(&first, existing);
    let updates = vec![
        rooted_update(
            first.clone(),
            "A",
            vec![stub("pow_correct", &fingerprint('a'))],
        ),
        rooted_update(
            second.clone(),
            "B",
            vec![stub("fresh_correct", &fingerprint('b'))],
        ),
    ];

    fixture.apply(&updates).unwrap();

    assert_eq!(std::fs::read_to_string(first).unwrap(), existing);
    let seeded = std::fs::read_to_string(second).unwrap();
    assert!(seeded.contains("export Playground.B_Proofs (fresh_correct)"));
}

#[test]
fn independent_reconciliation_inserts_a_missing_dependency_stub() {
    let fixture = LakeFixture::new();
    let first = fixture.proof("A");
    let second = fixture.proof("B");
    let existing_first = "import Playground.Math\nimport Playground.B_Proofs\n\ntheorem pow_correct : Playground.Math.pow_correct := by exact fresh_correct\n";
    let existing_second = "import Playground.Math\n";
    write_proof(&first, existing_first);
    write_proof(&second, existing_second);
    let updates = vec![
        rooted_update(
            first.clone(),
            "A",
            vec![stub("pow_correct", &fingerprint('a'))],
        ),
        rooted_update(
            second.clone(),
            "B",
            vec![stub("fresh_correct", &fingerprint('b'))],
        ),
    ];

    fixture.apply(&updates).unwrap();

    assert_eq!(std::fs::read_to_string(first).unwrap(), existing_first);
    let seeded = std::fs::read_to_string(second).unwrap();
    assert!(seeded.starts_with(existing_second));
    assert!(seeded.contains("export Playground.B_Proofs (fresh_correct)"));
}

#[test]
fn concurrent_conflicting_fingerprints_commit_one_complete_version() {
    let fixture = LakeFixture::new();
    let proof = fixture.proof("Math");
    let barrier = std::sync::Barrier::new(2);

    let results = std::thread::scope(|scope| {
        let handles = ['a', 'b'].map(|version| {
            let barrier = &barrier;
            let fixture = &fixture;
            let proof = proof.clone();
            scope.spawn(move || {
                let update = update_with(
                    proof,
                    "Playground.Math_Proofs",
                    vec![stub("pow_correct", &fingerprint(version))],
                );
                barrier.wait();
                fixture.apply(&[update])
            })
        });
        handles.map(|handle| handle.join().unwrap())
    });

    assert_eq!(results.iter().filter(|result| result.is_ok()).count(), 1);
    assert_eq!(
        results
            .iter()
            .filter(|result| matches!(
                result,
                Err(crate::render::RenderError::ProofStatementDrift { .. })
            ))
            .count(),
        1
    );
    let rendered = std::fs::read_to_string(proof).unwrap();
    assert_eq!(
        rendered
            .matches("export Playground.Math_Proofs (pow_correct)")
            .count(),
        1
    );
    assert_eq!(
        rendered.matches("sui-lean:obligation-fingerprint").count(),
        1
    );
    assert!(rendered.contains(&fingerprint('a')) || rendered.contains(&fingerprint('b')));
}

#[test]
fn nested_legacy_theorem_name_is_conservatively_preserved_for_audit() {
    let fixture = LakeFixture::new();
    let proof = fixture.proof("Math");
    let original = "import Playground.Math\n\nnamespace Helper\ntheorem pow_correct : Playground.Math.pow_correct := by trivial\nend Helper\n";
    write_proof(&proof, original);

    fixture.apply(&[update(proof.clone())]).unwrap();

    assert_eq!(std::fs::read_to_string(proof).unwrap(), original);
}

#[test]
fn private_legacy_theorem_name_is_conservatively_preserved_for_audit() {
    let fixture = LakeFixture::new();
    let proof = fixture.proof("Math");
    let original = "import Playground.Math\n\nprivate theorem pow_correct : Playground.Math.pow_correct := by trivial\n";
    write_proof(&proof, original);

    fixture.apply(&[update(proof.clone())]).unwrap();

    assert_eq!(std::fs::read_to_string(proof).unwrap(), original);
}

#[test]
fn legacy_declaration_kinds_are_preserved_for_audit() {
    let fixture = LakeFixture::new();
    let proof = fixture.proof("Math");
    let source = r#"import Playground.Math

def def_correct : Prop := True
opaque opaque_correct : Prop
axiom axiom_correct : Prop
abbrev abbrev_correct : Prop := True
instance instance_correct : Inhabited Nat := ⟨0⟩
structure structure_correct where
  value : Nat
"#;
    write_proof(&proof, source);
    let names = [
        "def_correct",
        "opaque_correct",
        "axiom_correct",
        "abbrev_correct",
        "instance_correct",
        "structure_correct",
    ];
    for name in names {
        let update = update_with(
            proof.clone(),
            "Playground.Math_Proofs",
            vec![stub(name, &fingerprint('a'))],
        );

        fixture.apply(&[update]).unwrap();

        assert_eq!(std::fs::read_to_string(&proof).unwrap(), source);
    }
}

#[test]
fn module_qualified_stub_does_not_collide_with_an_imported_bare_homonym() {
    let fixture = LakeFixture::new();
    let proof = fixture.proof("Math");
    let source = "import Foreign\nimport Playground.Math\n";
    write_proof(&proof, source);

    fixture.apply(&[update(proof.clone())]).unwrap();

    let rendered = std::fs::read_to_string(proof).unwrap();
    assert!(rendered.starts_with(source));
    assert!(rendered.contains("namespace Playground.Math_Proofs"));
    assert!(rendered.contains("theorem pow_correct : Playground.Math.pow_correct"));
    assert!(rendered.contains("export Playground.Math_Proofs (pow_correct)"));
}

#[test]
fn insertion_uses_only_real_leading_import_commands() {
    let fixture = LakeFixture::new();
    let proof = fixture.proof("Math");
    let source = r##"-- import Playground.Math
/- outer comment
   /- import Playground.Math -/
-/
import Foreign

def note := r#"
import Playground.Math
"#
"##;
    write_proof(&proof, source);

    let error = fixture.apply(&[update(proof.clone())]).unwrap_err();

    assert!(matches!(
        error,
        crate::render::RenderError::Io { what }
            if what.contains("does not directly import `Playground.Math`")
    ));
    assert_eq!(std::fs::read_to_string(proof).unwrap(), source);
}

#[test]
fn fake_imports_after_the_header_cannot_move_the_insertion_boundary() {
    let fixture = LakeFixture::new();
    let proof = fixture.proof("Math");
    let source = r##"import Playground.Math

def note := r#"
import Foreign
"#
/- import Still.Foreign -/
namespace Human
end Human
"##;
    write_proof(&proof, source);

    fixture.apply(&[update(proof.clone())]).unwrap();

    let rendered = std::fs::read_to_string(proof).unwrap();
    let inserted = rendered
        .find("namespace Playground.Math_Proofs")
        .expect("inserted proof namespace");
    assert!(inserted < rendered.find("def note").unwrap());
    assert!(rendered[inserted..].contains(source.trim_start_matches("import Playground.Math\n")));
}

#[test]
fn leading_comments_and_real_imports_form_the_only_insertion_header() {
    let fixture = LakeFixture::new();
    let proof = fixture.proof("Math");
    let source = r#"/- copyright /- nested -/ notice -/
-- imports begin below
import Foreign -- helper
/- between imports -/
import Playground.Math

section Human
end Human
"#;
    write_proof(&proof, source);

    fixture.apply(&[update(proof.clone())]).unwrap();

    let rendered = std::fs::read_to_string(proof).unwrap();
    assert!(rendered.starts_with(
        "/- copyright /- nested -/ notice -/\n-- imports begin below\nimport Foreign -- helper\n/- between imports -/\nimport Playground.Math\n"
    ));
    assert!(
        rendered.find("export Playground.Math_Proofs").unwrap()
            < rendered.find("section Human").unwrap()
    );
}

#[test]
fn malformed_or_unterminated_import_headers_fail_without_mutation() {
    let fixture = LakeFixture::new();
    let proof = fixture.proof("Math");
    for source in [
        "import Playground.Math trailing\n",
        "import Playground.Math\nimport\n",
        "import Playground.Math\n/- unterminated\n",
    ] {
        write_proof(&proof, source);

        let error = fixture.apply(&[update(proof.clone())]).unwrap_err();

        assert!(matches!(
            error,
            crate::render::RenderError::Io { what }
                if what.contains("cannot safely locate the import header")
        ));
        assert_eq!(std::fs::read_to_string(&proof).unwrap(), source);
    }
}

#[test]
fn inserted_options_are_scoped_to_the_generated_theorem() {
    let fixture = LakeFixture::new();
    let proof = fixture.proof("Math");
    let source = "import Playground.Math\n\nset_option maxHeartbeats 17\n";
    write_proof(&proof, source);

    fixture.apply(&[update(proof.clone())]).unwrap();

    let rendered = std::fs::read_to_string(proof).unwrap();
    for option in [
        "set_option maxRecDepth 4096 in\n",
        "set_option maxHeartbeats 8000000 in\n",
        "set_option synthInstance.maxHeartbeats 4000000 in\n",
        "set_option linter.unusedVariables false in\n",
    ] {
        assert!(rendered.contains(option));
    }
    assert!(!rendered.contains("set_option maxRecDepth 4096\n"));
    assert!(
        rendered
            .find("export Playground.Math_Proofs (pow_correct)")
            .unwrap()
            < rendered.find("set_option maxHeartbeats 17").unwrap()
    );
}

#[test]
fn missing_direct_generated_import_blocks_stub_insertion_without_mutation() {
    let fixture = LakeFixture::new();
    let proof = fixture.proof("Math");
    let source = "import Foreign\n";
    write_proof(&proof, source);

    let error = fixture.apply(&[update(proof.clone())]).unwrap_err();

    assert!(matches!(
        error,
        crate::render::RenderError::Io { what }
            if what.contains("does not directly import `Playground.Math`")
    ));
    assert_eq!(std::fs::read_to_string(proof).unwrap(), source);
}

#[test]
fn exported_generated_stub_elaborates_in_a_legacy_bare_cross_module_reference() {
    let fixture = LakeFixture::new();
    std::fs::write(
        fixture.proofs.join("lakefile.lean"),
        "import Lake\nopen Lake DSL\npackage ProofReconcile where\nlean_lib Playground where\n  roots := #[`Playground.Math, `Playground.A_Proofs, `Playground.B_Proofs]\n",
    )
    .unwrap();
    std::fs::write(
        fixture.proofs.join("Playground/Math.lean"),
        "namespace Playground.Math\ndef pow_correct : Prop := True\ndef fresh_correct : Prop := True\nend Playground.Math\n",
    )
    .unwrap();
    let first = fixture.proof("A");
    let second = fixture.proof("B");
    write_proof(
        &first,
        "import Playground.Math\nimport Playground.B_Proofs\n\ntheorem legacy_consumer : Playground.Math.fresh_correct := by\n  exact fresh_correct\n",
    );
    fixture
        .apply(&[
            rooted_update(first, "A", vec![stub("pow_correct", &fingerprint('a'))]),
            rooted_update(second, "B", vec![stub("fresh_correct", &fingerprint('b'))]),
        ])
        .unwrap();

    let output = std::process::Command::new("lake")
        .arg("build")
        .current_dir(&fixture.proofs)
        .output()
        .expect("run lake build");

    assert!(
        output.status.success(),
        "generated proof aliases did not elaborate:\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
fn legacy_namespaced_name_occurrence_preserves_the_source() {
    let fixture = LakeFixture::new();
    let proof = fixture.proof("Math");
    let source = "import Foreign\nimport Playground.Math\n\nnamespace Playground.Math_Proofs\ntheorem pow_correct : Playground.Math.pow_correct := by trivial\nend Playground.Math_Proofs\n";
    write_proof(&proof, source);

    fixture.apply(&[update(proof.clone())]).unwrap();

    assert_eq!(std::fs::read_to_string(proof).unwrap(), source);
}

#[test]
fn the_same_raw_legacy_name_is_preserved_in_each_proof_root() {
    let fixture = LakeFixture::new();
    let first = fixture.proof("A");
    let second = fixture.proof("B");
    let source = "import Playground.Math\n\ntheorem pow_correct : Playground.Math.pow_correct := by trivial\n";
    write_proof(&first, source);
    write_proof(&second, source);
    let updates = vec![
        rooted_update(
            first.clone(),
            "A",
            vec![stub("pow_correct", &fingerprint('a'))],
        ),
        rooted_update(
            second.clone(),
            "B",
            vec![stub("pow_correct", &fingerprint('a'))],
        ),
    ];

    fixture.apply(&updates).unwrap();

    assert_eq!(std::fs::read_to_string(first).unwrap(), source);
    assert_eq!(std::fs::read_to_string(second).unwrap(), source);
}

#[test]
fn missing_stub_is_inserted_before_an_unclosed_namespace() {
    let fixture = LakeFixture::new();
    let proof = fixture.proof("Math");
    let original = "import Playground.Math\n\nnamespace Helper\n";
    write_proof(&proof, original);

    fixture.apply(&[update(proof.clone())]).unwrap();

    let first = std::fs::read_to_string(&proof).unwrap();
    assert!(first.contains("export Playground.Math_Proofs (pow_correct)"));
    assert!(first.contains("namespace Helper"));
    assert!(
        first
            .find("export Playground.Math_Proofs (pow_correct)")
            .unwrap()
            < first.find("namespace Helper").unwrap()
    );
    fixture.apply(&[update(proof.clone())]).unwrap();
    assert_eq!(std::fs::read_to_string(proof).unwrap(), first);
}

#[test]
fn missing_stub_is_inserted_before_included_section_variables() {
    let fixture = LakeFixture::new();
    let proof = fixture.proof("Math");
    let original = "import Playground.Math\n\nsection\nvariable (h : True)\ninclude h\n";
    write_proof(&proof, original);

    fixture.apply(&[update(proof.clone())]).unwrap();

    let rendered = std::fs::read_to_string(proof).unwrap();
    assert!(rendered.contains("export Playground.Math_Proofs (pow_correct)"));
    assert!(rendered.contains("section\nvariable (h : True)\ninclude h\n"));
    assert!(
        rendered
            .find("export Playground.Math_Proofs (pow_correct)")
            .unwrap()
            < rendered.find("section\n").unwrap()
    );
}

#[test]
fn missing_stub_is_inserted_before_exit() {
    let fixture = LakeFixture::new();
    let proof = fixture.proof("Math");
    let original = "import Playground.Math\n\nexit\n";
    write_proof(&proof, original);

    fixture.apply(&[update(proof.clone())]).unwrap();

    let rendered = std::fs::read_to_string(proof).unwrap();
    assert!(rendered.contains("export Playground.Math_Proofs (pow_correct)"));
    assert!(rendered.contains("\nexit\n"));
    assert!(
        rendered
            .find("export Playground.Math_Proofs (pow_correct)")
            .unwrap()
            < rendered.find("exit\n").unwrap()
    );
}

#[cfg(unix)]
#[test]
fn symlink_proof_is_rejected_without_replacing_or_mutating_it() {
    use std::os::unix::fs::symlink;

    let fixture = LakeFixture::new();
    let target = fixture.proofs.join("human.lean");
    let proof = fixture.proof("Math");
    let original = "import Playground.Math\n";
    std::fs::write(&target, original).unwrap();
    symlink(&target, &proof).unwrap();

    let error = fixture.apply(&[update(proof.clone())]).unwrap_err();

    assert!(matches!(
        error,
        crate::render::RenderError::Io { what } if what.contains("must not be a symlink")
    ));
    assert!(std::fs::symlink_metadata(&proof)
        .unwrap()
        .file_type()
        .is_symlink());
    assert_eq!(std::fs::read_to_string(target).unwrap(), original);
}

#[cfg(unix)]
#[test]
fn symlinked_package_directory_cannot_escape_the_proof_overlay() {
    use std::os::unix::fs::symlink;

    let fixture = LakeFixture::new();
    let package_dir = fixture.proofs.join("Playground");
    let outside = fixture._temp.path().join("outside");
    std::fs::remove_dir(&package_dir).unwrap();
    std::fs::create_dir(&outside).unwrap();
    symlink(&outside, &package_dir).unwrap();
    let proof = fixture.proof("Math");

    let error = fixture.apply(&[update(proof)]).unwrap_err();

    assert!(matches!(
        error,
        crate::render::RenderError::Io { what }
            if what.contains("proof overlay directory must be a non-symlink directory")
    ));
    assert!(!outside.join("Math_Proofs.lean").exists());
}
