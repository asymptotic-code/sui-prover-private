use std::path::{Path, PathBuf};

/// Skipped when walking the bundle: build output and version control, never
/// part of the model the proofs elaborate against.
const SKIPPED_DIRS: [&str; 3] = [".git", ".lake", "vendor"];

fn main() {
    // Large Move packages traverse deeply nested IR on the CLI's main thread.
    // Match the integration harness's stack reserve on Windows, where the
    // linker default is too small even for existing client specifications.
    if std::env::var("CARGO_CFG_TARGET_OS").as_deref() == Ok("windows")
        && std::env::var("CARGO_CFG_TARGET_ENV").as_deref() == Ok("msvc")
    {
        println!("cargo:rustc-link-arg-bin=sui-lean=/STACK:67108864");
    }

    let manifest_dir =
        PathBuf::from(std::env::var("CARGO_MANIFEST_DIR").expect("cargo sets CARGO_MANIFEST_DIR"));
    let lemmas_dir = manifest_dir
        .parent()
        .expect("the sui-lean crate has a parent `crates` directory")
        .join("lean-pipeline/lemmas");
    assert!(
        lemmas_dir.join("Prelude/BoundedNat.lean").is_file()
            && lemmas_dir.join("natives/Prover/MoveAuto.lean").is_file(),
        "the Lean model bundle is not where the sui-lean build script expects it: {}",
        lemmas_dir.display()
    );

    let mut files = Vec::new();
    collect(&lemmas_dir, &lemmas_dir, &mut files);
    files.sort();
    assert!(
        !files.is_empty(),
        "the Lean model bundle at {} is empty",
        lemmas_dir.display()
    );

    let mut generated = String::from("static LEMMA_BUNDLE_FILES: &[(&str, &[u8])] = &[\n");
    for (relative, absolute) in &files {
        generated.push_str(&format!(
            "    ({:?}, include_bytes!({:?})),\n",
            relative,
            absolute.to_str().expect("bundle path is valid UTF-8")
        ));
    }
    generated.push_str("];\n");

    let out_dir = PathBuf::from(std::env::var("OUT_DIR").expect("cargo sets OUT_DIR"));
    std::fs::write(out_dir.join("lemma_bundle.rs"), generated)
        .expect("writing the generated lemma bundle manifest");

    // Directories catch additions and removals, files catch edits.
    println!("cargo:rerun-if-changed=build.rs");
    for directory in directories(&lemmas_dir) {
        println!("cargo:rerun-if-changed={}", directory.display());
    }
    for (_, absolute) in &files {
        println!("cargo:rerun-if-changed={}", absolute.display());
    }
}

fn collect(root: &Path, dir: &Path, out: &mut Vec<(String, PathBuf)>) {
    let entries = std::fs::read_dir(dir)
        .unwrap_or_else(|error| panic!("read_dir({}): {error}", dir.display()));
    for entry in entries {
        let entry = entry.unwrap_or_else(|error| panic!("entry under {}: {error}", dir.display()));
        let path = entry.path();
        let name = path
            .file_name()
            .and_then(|name| name.to_str())
            .unwrap_or_else(|| panic!("non-UTF-8 name under {}", dir.display()))
            .to_string();
        let metadata = std::fs::symlink_metadata(&path)
            .unwrap_or_else(|error| panic!("metadata({}): {error}", path.display()));
        if metadata.is_dir() {
            if !SKIPPED_DIRS.contains(&name.as_str()) {
                collect(root, &path, out);
            }
            continue;
        }
        if !metadata.is_file() {
            continue;
        }
        let relative = path
            .strip_prefix(root)
            .expect("bundle file is beneath the bundle root")
            .to_str()
            .unwrap_or_else(|| panic!("non-UTF-8 path {}", path.display()))
            .replace('\\', "/");
        out.push((relative, path));
    }
}

fn directories(root: &Path) -> Vec<PathBuf> {
    let mut out = vec![root.to_path_buf()];
    let mut index = 0;
    while index < out.len() {
        let dir = out[index].clone();
        index += 1;
        let Ok(entries) = std::fs::read_dir(&dir) else {
            continue;
        };
        for entry in entries.flatten() {
            let path = entry.path();
            let is_skipped = path
                .file_name()
                .and_then(|name| name.to_str())
                .is_some_and(|name| SKIPPED_DIRS.contains(&name));
            if !is_skipped && std::fs::symlink_metadata(&path).is_ok_and(|m| m.is_dir()) {
                out.push(path);
            }
        }
    }
    out
}
