// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Prelude File Management
//!
//! This module handles copying Prelude files (type definitions, helpers) to the output directory.

use crate::{copy_if_changed, WrittenFiles};
use anyhow::{Context, Result};
use log::{error, info};
use std::fs;
use std::path::{Path, PathBuf};

/// Prelude file manager
pub struct PreludeManager {
    /// Output directory (where Impls/ and Specs/ are)
    output_dir: PathBuf,

    /// Source directory for Prelude files (crates/move-prover-lean-backend/lemmas/)
    source_dir: PathBuf,
}

impl PreludeManager {
    /// Create a new prelude manager
    pub fn new(output_dir: PathBuf) -> Self {
        let source_dir = Self::find_prelude_source_dir(&output_dir);

        Self {
            output_dir,
            source_dir,
        }
    }

    /// Find the lemmas directory (contains Prelude and natives subdirs)
    fn find_prelude_source_dir(output_dir: &Path) -> PathBuf {
        let lemmas_subpath = "crates/move-prover-lean-backend/lemmas";

        // Try using CARGO_MANIFEST_DIR which points to move-prover-lean-backend crate
        // This is the most reliable method as it's set at compile time
        let manifest_dir = env!("CARGO_MANIFEST_DIR");
        let candidate = PathBuf::from(manifest_dir).join("lemmas");
        if candidate.join("Prelude").exists() {
            return candidate;
        }

        // Try walking up from output_dir to find project root
        let mut current = output_dir.to_path_buf();
        while current.pop() {
            let candidate = current.join(lemmas_subpath);
            if candidate.join("Prelude").exists() {
                return candidate;
            }
        }

        // Try current working directory
        if let Ok(cwd) = std::env::current_dir() {
            let candidate = cwd.join(lemmas_subpath);
            if candidate.join("Prelude").exists() {
                return candidate;
            }

            // Try parent of current working directory
            if let Some(parent) = cwd.parent() {
                let candidate = parent.join(lemmas_subpath);
                if candidate.join("Prelude").exists() {
                    return candidate;
                }
            }
        }

        // Fallback to relative path from output_dir
        output_dir.join("../../").join(lemmas_subpath)
    }

    /// Initialize the Prelude directory structure and copy files
    pub fn initialize(&self, written: &mut WrittenFiles) -> Result<()> {
        self.copy_prelude_files(written)
            .context("Failed to copy Prelude files")?;

        self.copy_prelude_required_natives(written)
            .context("Failed to copy Prelude-required natives files")?;

        Ok(())
    }

    /// Get list of Prelude module names from source directory
    /// Returns module names like "Prelude.UInt128", "Prelude.Helpers", etc.
    pub fn get_prelude_imports(&self) -> Result<Vec<String>> {
        let prelude_source = self.source_dir.join("Prelude");

        if !prelude_source.exists() {
            return Ok(vec![]);
        }

        let entries = fs::read_dir(&prelude_source).context("Failed to read Prelude directory")?;

        let mut imports = Vec::new();
        for entry in entries.flatten() {
            let path = entry.path();
            if path.extension().and_then(|s| s.to_str()) == Some("lean") {
                if let Some(file_stem) = path.file_stem().and_then(|s| s.to_str()) {
                    imports.push(format!("Prelude.{}", file_stem));
                }
            }
        }

        // Sort for consistent ordering
        imports.sort();
        Ok(imports)
    }

    /// Copy natives files that the unconditionally-emitted Prelude depends on.
    ///
    /// Some Prelude lemma files (e.g. `Prelude/Quantifiers.lean`) `import`
    /// `MoveStdlib.MoveVectorNatives` even though no Move code in the package
    /// references `std::vector`. Without this, lake build fails with
    /// "no such file or directory" on the missing native.
    ///
    /// Keep this list aligned with non-Prelude `import` statements inside
    /// `lemmas/Prelude/*.lean`. If you add another such cross-namespace import
    /// to a Prelude file, add the corresponding native here.
    fn copy_prelude_required_natives(&self, written: &mut WrittenFiles) -> Result<()> {
        // (relative path under `lemmas/`, destination subdir under output_dir)
        const REQUIRED_NATIVES: &[(&str, &str)] =
            &[("natives/MoveStdlib/MoveVectorNatives.lean", "MoveStdlib")];

        for (rel_src, dest_subdir) in REQUIRED_NATIVES {
            let source_path = self.source_dir.join(rel_src);
            if !source_path.exists() {
                error!(
                    "Required native file not found at: {} (Prelude depends on it)",
                    source_path.display()
                );
                continue;
            }

            let file_name = source_path.file_name().with_context(|| {
                format!("Native source has no filename: {}", source_path.display())
            })?;
            let dest_dir = self.output_dir.join(dest_subdir);
            fs::create_dir_all(&dest_dir).with_context(|| {
                format!(
                    "Failed to create native dest directory {}",
                    dest_dir.display()
                )
            })?;
            let dest_path = dest_dir.join(file_name);

            copy_if_changed(&source_path, &dest_path, written).with_context(|| {
                format!(
                    "Failed to copy {} to {}",
                    source_path.display(),
                    dest_path.display()
                )
            })?;
        }

        Ok(())
    }

    /// Copy Prelude files from lean backend to output directory
    fn copy_prelude_files(&self, written: &mut WrittenFiles) -> Result<()> {
        let prelude_source = self.source_dir.join("Prelude");

        if !prelude_source.exists() {
            error!(
                "Prelude directory not found at: {}",
                prelude_source.display()
            );
            return Ok(());
        }

        info!("Copying Prelude files from: {}", prelude_source.display());

        let output_prelude = self.output_dir.join("Prelude");
        fs::create_dir_all(&output_prelude).context("Failed to create Prelude directory")?;

        let entries = fs::read_dir(&prelude_source).context("Failed to read Prelude directory")?;

        for entry in entries.flatten() {
            let path = entry.path();
            if path.extension().and_then(|s| s.to_str()) == Some("lean") {
                if let Some(file_name) = path.file_name() {
                    let dest = output_prelude.join(file_name);
                    copy_if_changed(&path, &dest, written).with_context(|| {
                        format!("Failed to copy {} to {}", path.display(), dest.display())
                    })?;
                }
            }
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use tempfile::TempDir;

    #[test]
    fn test_initialize() {
        let temp_dir = TempDir::new().unwrap();
        let manager = PreludeManager::new(temp_dir.path().to_path_buf());

        let mut written = WrittenFiles::new();
        manager.initialize(&mut written).unwrap();

        assert!(temp_dir.path().join("Prelude/MoveType.lean").exists());
    }
}
