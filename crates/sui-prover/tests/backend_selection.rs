use move_compiler::{editions::Flavor, shared::known_attributes::ModeAttribute};
use move_package::BuildConfig as MoveBuildConfig;
use move_stackless_bytecode::{
    package_targets::{PackageTargets, SpecBackend, VALID_RUN_ON_VALUES},
    target_filter::TargetFilterOptions,
};
use std::{collections::BTreeSet, fs};
use sui_prover::build_model::move_model_for_package_legacy_unlocked;

fn selected_spec_names(backend: SpecBackend) -> BTreeSet<String> {
    let temp = tempfile::tempdir().unwrap();
    let prover_package = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .join("packages/sui-prover")
        .display()
        .to_string()
        .replace('\\', "/");

    fs::write(
        temp.path().join("Move.toml"),
        format!(
            r#"[package]
name = "backend-selection-test"
edition = "2024.beta"

[dependencies]
SuiProver = {{ local = "{prover_package}", override = true }}

[addresses]
backend_selection = "0x42"
"#,
        ),
    )
    .unwrap();
    fs::create_dir(temp.path().join("sources")).unwrap();
    fs::write(
        temp.path().join("sources/backend_selection.move"),
        r#"module backend_selection::example;

#[spec(prove)]
fun default_spec() {}

#[ext(backend=b"both")]
#[spec(prove)]
fun both_spec() {}

#[ext(backend=b"lean")]
#[spec(prove)]
fun lean_spec() {}

#[ext(backend=b"boogie")]
#[spec(prove)]
fun boogie_spec() {}

"#,
    )
    .unwrap();

    let mut config = MoveBuildConfig::default();
    config.default_flavor = Some(Flavor::Sui);
    config.modes = vec![ModeAttribute::VERIFY_ONLY.into()];
    config.skip_fetch_latest_git_deps = true;
    let model = move_model_for_package_legacy_unlocked(config, temp.path()).unwrap();
    assert!(!model.has_errors());

    PackageTargets::new(&model, TargetFilterOptions::default(), true, None)
        .select_backend(backend)
        .target_specs()
        .iter()
        .map(|qid| model.get_function(*qid).get_name_str())
        .collect()
}

#[test]
fn per_spec_backend_selects_lean_boogie_both_and_default() {
    let lean = selected_spec_names(SpecBackend::Lean);
    assert!(lean.contains("default_spec"));
    assert!(lean.contains("both_spec"));
    assert!(lean.contains("lean_spec"));
    assert!(lean.contains("boogie_spec"));

    let boogie = selected_spec_names(SpecBackend::Boogie);
    assert!(boogie.contains("default_spec"));
    assert!(boogie.contains("both_spec"));
    assert!(boogie.contains("boogie_spec"));
    assert!(!boogie.contains("lean_spec"));
}

#[test]
fn run_on_only_accepts_execution_locations() {
    assert_eq!(VALID_RUN_ON_VALUES, &["local", "cloud"]);
}
