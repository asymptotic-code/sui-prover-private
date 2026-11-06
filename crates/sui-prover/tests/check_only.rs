use codespan_reporting::term::termcolor::Buffer;
use move_compiler::{editions::Flavor, shared::known_attributes::ModeAttribute};
use move_package::BuildConfig as MoveBuildConfig;
use move_prover_boogie_backend::generator::run_move_prover_with_model;
use move_prover_boogie_backend::generator_options::Options;
use move_stackless_bytecode::attr_query::SPEC_MODE;
use std::fs;
use sui_prover::build_model::move_model_for_package_legacy_unlocked;

const UNRELATED_SPEC: &str = r#"module check_only::unrelated;

#[ext(pure)]
public fun fine(x: u64): u64 {
    x + 1
}

public fun target(x: u64): u64 {
    x
}

#[mode(spec), ext(spec(prove, target = check_only::unrelated::target))]
fun target_spec(x: u64): u64 {
    target(x)
}
"#;

const HELPER_WITH_MUTABLE_REFERENCE: &str = r#"module check_only::helpers;

#[ext(pure)]
public fun with_mutable_reference(x: u64): vector<u64> {
    let mut items = vector[x];
    std::vector::push_back(&mut items, x);
    items
}
"#;

fn check_only(sources: &[(&str, &str)]) -> Result<String, String> {
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
name = "check-only-test"
edition = "2024.beta"

[dependencies]
SuiProver = {{ local = "{prover_package}", override = true }}

[addresses]
check_only = "0x42"
"#,
        ),
    )
    .unwrap();
    fs::create_dir(temp.path().join("sources")).unwrap();
    for (name, source) in sources {
        fs::write(temp.path().join("sources").join(name), source).unwrap();
    }

    let mut config = MoveBuildConfig::default();
    config.default_flavor = Some(Flavor::Sui);
    config.modes = vec![ModeAttribute::VERIFY_ONLY.into(), SPEC_MODE.into()];
    config.skip_fetch_latest_git_deps = true;
    let model = move_model_for_package_legacy_unlocked(config, temp.path()).unwrap();

    let mut options = Options::default();
    options.prover.check_only = true;
    options.prover.skip_spec_no_abort = true;
    options.backend.no_verify = true;
    options.output_path = temp.path().join("output").display().to_string();
    let mut errors = Buffer::no_color();
    let result = tokio::runtime::Runtime::new()
        .unwrap()
        .block_on(run_move_prover_with_model(
            &model,
            &mut errors,
            options,
            None,
        ));
    let diagnostics = String::from_utf8_lossy(errors.as_slice()).to_string();
    result.map_err(|err| format!("{err}\n{diagnostics}"))
}

#[test]
fn a_clean_package_passes_and_generates_nothing() {
    let result = check_only(&[("unrelated.move", UNRELATED_SPEC)]);
    assert_eq!(result.unwrap(), "Package-wide transformation passed");
}

#[test]
fn another_modules_pure_helper_with_a_mutable_reference_is_refused() {
    let error = check_only(&[
        ("unrelated.move", UNRELATED_SPEC),
        ("helpers.move", HELPER_WITH_MUTABLE_REFERENCE),
    ])
    .unwrap_err();
    assert!(
        error.contains("exiting with bytecode transformation errors"),
        "{error}"
    );
    assert!(
        error.contains("Pure functions with mutable references are not supported"),
        "{error}"
    );
}
