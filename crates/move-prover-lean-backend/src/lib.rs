// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

use std::collections::HashSet;
use std::fs;
use std::path::{Path, PathBuf};

pub mod backend;
pub mod escape;
pub mod native_ghost_fields;
pub mod prelude;
pub mod renderer;
pub mod runtime;

// Re-exports for convenience
pub use backend::{
    run_backend, run_backend_with_boogie_proven, run_backend_with_options,
    scan_lean_termination_decls, GhostNativeSeed,
};
pub use runtime::run_lake_build_targets;

/// Tracks all .lean files written during a generation run.
/// After generation, `remove_stale` deletes any .lean files in the output
/// directory that weren't written this run.
pub struct WrittenFiles {
    paths: HashSet<PathBuf>,
}

impl WrittenFiles {
    pub fn new() -> Self {
        Self {
            paths: HashSet::new(),
        }
    }

    pub fn record(&mut self, path: &Path) {
        self.paths.insert(path.to_path_buf());
    }

    /// Remove .lean files under `dir` that weren't recorded, skipping .lake/.
    pub fn remove_stale(&self, dir: &Path) {
        let Ok(entries) = fs::read_dir(dir) else {
            return;
        };
        for entry in entries.flatten() {
            let path = entry.path();
            let name = entry.file_name();
            if name == ".lake" || name == "lake-packages" {
                continue;
            }
            if path.is_dir() {
                self.remove_stale(&path);
            } else if path.extension().is_some_and(|ext| ext == "lean")
                && !self.paths.contains(&path)
            {
                fs::remove_file(&path).ok();
            }
        }
    }
}

/// Write content to a file only if it differs from the existing content.
/// Records the path in `written` for stale file cleanup.
pub fn write_if_changed(
    path: &Path,
    content: &str,
    written: &mut WrittenFiles,
) -> anyhow::Result<bool> {
    written.record(path);
    if path.exists() {
        let existing = fs::read_to_string(path)?;
        if existing == content {
            return Ok(false);
        }
    }
    if let Some(parent) = path.parent() {
        fs::create_dir_all(parent)?;
    }
    fs::write(path, content)?;
    Ok(true)
}

/// Copy a file only if source and destination differ.
/// Records the destination path in `written` for stale file cleanup.
pub fn copy_if_changed(src: &Path, dst: &Path, written: &mut WrittenFiles) -> anyhow::Result<bool> {
    written.record(dst);
    if dst.exists() {
        let src_content = fs::read(src)?;
        let dst_content = fs::read(dst)?;
        if src_content == dst_content {
            return Ok(false);
        }
    }
    if let Some(parent) = dst.parent() {
        fs::create_dir_all(parent)?;
    }
    fs::copy(src, dst)?;
    Ok(true)
}

/// Writes the lakefile.lean and lake-manifest.json for the project.
/// `packages` is the list of package names that should become Lake libraries.
pub fn write_lakefile(
    output_path: &Path,
    module_name: &str,
    packages: &[String],
    proofs_src_dir: Option<&str>,
    termination_src_dir: Option<&str>,
    hooks_src_dir: Option<&str>,
    written: &mut WrittenFiles,
) -> anyhow::Result<()> {
    // `moreLeanArgs := #["--tstack=1048576"]` gives the Lean worker a 1 GB
    // thread stack (default ~8 MB), which the big inlined test bodies
    // (some 8000+ lines, e.g. `Test_charge_accrued_platform_fees.lean`)
    // and large proof-import surfaces (e.g. the bluefin tick_math bridge,
    // which overflows a 128 MB stack on `.olean` import) need to elaborate
    // without `Stack overflow detected. Aborting.`.
    // Without this the build dies with exit code 134 before
    // `maxRecDepth` even fires.
    let mut lakefile_content = format!(
        r#"import Lake
open Lake DSL

package «{}» where
  moreLeanArgs := #["--tstack=1048576"]

lean_lib Prelude where
  roots := #[`Prelude]
  globs := #[.submodules `Prelude]

"#,
        module_name
    );

    // Generate a lean_lib for each package
    for package in packages {
        lakefile_content.push_str(&format!(
            r#"@[default_target]
lean_lib {} where
  roots := #[`{}]
  globs := #[.submodules `{}]

"#,
            package, package, package
        ));
    }

    // Termination and Proofs libs hold user-maintained files. When the package
    // has sources/lean/{Termination,Proofs}/, srcDir points lake at those
    // directories so the files are built in place — no copies in the output.
    let user_lib = |name: &str, src_dir: Option<&str>| -> String {
        let src_line = src_dir
            .map(|d| format!("  srcDir := \"{}\"\n", d))
            .unwrap_or_default();
        format!(
            "@[default_target]\nlean_lib {} where\n{}  roots := #[`{}]\n  globs := #[.submodules `{}]\n\n",
            name, src_line, name, name
        )
    };
    // Add Termination library for user-provided termination measures and proofs.
    // Generated while-loop functions reference definitions from Termination/ files.
    lakefile_content.push_str(&user_lib("Termination", termination_src_dir));

    // Add Proofs library for user-written proof files.
    lakefile_content.push_str(&user_lib("Proofs", proofs_src_dir));

    // Add the unified client hook library (unified-backend design §8) ONLY
    // when the package has a sources/lean/Hooks/ directory — packages on the
    // legacy Termination/ layout keep a byte-identical lakefile.
    if hooks_src_dir.is_some() {
        lakefile_content.push_str(&user_lib("Hooks", hooks_src_dir));
    }

    // Add Correctness library for spec proof obligations (ensures/requires theorems)
    lakefile_content.push_str(
        r#"@[default_target]
lean_lib Correctness where
  roots := #[`Correctness]
  globs := #[.submodules `Correctness]

"#,
    );

    write_if_changed(
        &output_path.join("lakefile.lean"),
        &lakefile_content,
        written,
    )?;

    // Write minimal lake-manifest.json (compatible with Lake 4.15+)
    let manifest = format!(
        r#"{{"version": "1.1.0",
 "packagesDir": ".lake/packages",
 "packages": [],
 "name": "«{}»",
 "lakeDir": ".lake"}}"#,
        module_name
    );
    write_if_changed(&output_path.join("lake-manifest.json"), &manifest, written)?;

    Ok(())
}
