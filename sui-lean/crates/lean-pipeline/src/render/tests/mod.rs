//! Render-side fixtures for normalized post-pipeline IR.

#![cfg(test)]

mod conjunct_projection;
mod consts;
mod df_universe;
mod escape;
mod fixpoint_match;
mod fixtures;
mod globals;
mod match_bindings;
mod mutation;
mod mutation_e2e;
mod mutkey_bridge;
mod native_dispatch;
mod obligations_manifest;
mod prefix_agnostic;
mod proof_sources;
mod render_shapes;
mod rendered_types;
mod serialize;
mod smoke;
mod test_declarations;
mod ty;
mod world;

#[test]
fn proof_automation_dependencies_follow_the_runtime_lemmas_tree() {
    let temp = tempfile::tempdir().unwrap();
    // canonicalize so vendor-containment asserts agree with the canonicalized
    // dependency directories production returns (macOS /var -> /private/var)
    let runtime = temp.path().canonicalize().unwrap().join("relocated");
    let lemmas = runtime.join("bundle/lemmas");
    let move_auto = lemmas.join("natives/Prover/MoveAuto.lean");
    std::fs::create_dir_all(move_auto.parent().unwrap()).unwrap();
    std::fs::write(move_auto, "import Lean\n").unwrap();

    let vendor = runtime.join("vendor");
    std::fs::create_dir_all(&vendor).unwrap();
    std::fs::write(vendor.join("VERSIONS.md"), "fixture\n").unwrap();
    for (folder, config) in [
        ("batteries", "lakefile.toml"),
        ("aesop", "lakefile.toml"),
        ("lean-auto", "lakefile.lean"),
    ] {
        let directory = vendor.join(folder);
        std::fs::create_dir_all(&directory).unwrap();
        std::fs::write(directory.join(config), "").unwrap();
        std::fs::write(directory.join("lake-manifest.json"), "{}").unwrap();
        std::fs::write(
            directory.join("lean-toolchain"),
            super::GENERATED_LEAN_TOOLCHAIN,
        )
        .unwrap();
        std::fs::write(
            directory.join("Source.lean"),
            format!("def {folder} := True\n"),
        )
        .unwrap();
    }

    let batteries_digest = super::dependency_source_digest(&vendor.join("batteries")).unwrap();
    let aesop_digest = super::dependency_source_digest(&vendor.join("aesop")).unwrap();
    let auto_digest = super::dependency_source_digest(&vendor.join("lean-auto")).unwrap();
    let specs = [
        super::AutomationDependency {
            name: "batteries",
            folder: "batteries",
            config_file: "lakefile.toml",
            source_digest: &batteries_digest,
        },
        super::AutomationDependency {
            name: "aesop",
            folder: "aesop",
            config_file: "lakefile.toml",
            source_digest: &aesop_digest,
        },
        super::AutomationDependency {
            name: "auto",
            folder: "lean-auto",
            config_file: "lakefile.lean",
            source_digest: &auto_digest,
        },
    ];

    std::fs::write(vendor.join("aesop/Source.lean"), "def aesop := False\n").unwrap();
    let error = super::proof_automation_dependencies_with_specs(Some(&lemmas), &specs).unwrap_err();
    assert!(format!("{error:?}").contains("source digest"), "{error:?}");
    std::fs::write(vendor.join("aesop/Source.lean"), "def aesop := True\n").unwrap();

    let dependencies =
        super::proof_automation_dependencies_with_specs(Some(&lemmas), &specs).unwrap();

    assert_eq!(dependencies.len(), 3);
    assert!(dependencies
        .iter()
        .all(|dependency| dependency.directory.starts_with(&vendor)));

    std::fs::write(
        vendor.join("aesop/lean-toolchain"),
        "leanprover/lean4:v4.31.0\n",
    )
    .unwrap();
    assert!(super::proof_automation_dependencies_with_specs(Some(&lemmas), &specs).is_err());
}

#[test]
fn proof_automation_dependency_pins_match_the_vendored_sources() {
    let lemmas = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("lemmas");
    let dependencies = super::proof_automation_dependencies(Some(&lemmas)).unwrap();
    assert_eq!(
        dependencies
            .iter()
            .map(|dependency| dependency.name.as_str())
            .collect::<Vec<_>>(),
        ["batteries", "aesop", "auto"]
    );
}
