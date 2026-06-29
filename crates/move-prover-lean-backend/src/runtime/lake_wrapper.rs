// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Lake build execution for Lean projects

use anyhow::{anyhow, Result};
use log::debug;
use tokio::process::Command;

/// Runs `lake build` in the specified directory
///
/// Returns the combined stdout/stderr output on success, or an error if Lake fails.
pub async fn run_lake_build(project_dir: &str) -> Result<String> {
    run_lake_build_targets(project_dir, &[]).await
}

/// Runs `lake build [targets...]` in the specified directory.
/// When `targets` is empty, builds the default targets (same as
/// [`run_lake_build`]). When non-empty, restricts the build to the
/// listed Lake library / module names — useful for `--test`, where the
/// model contains many `*_tests` modules from dep packages whose Spec
/// rendering is broken: per-test `lake env lean --run` only needs
/// `Prelude` + the user's package built.
pub async fn run_lake_build_targets(project_dir: &str, targets: &[String]) -> Result<String> {
    debug!(
        "running lake build in {} with targets {:?}",
        project_dir, targets
    );

    let mut cmd = Command::new("lake");
    cmd.arg("build");
    for t in targets {
        cmd.arg(t);
    }
    // 20 min: large packages (cetus_clmm `Pool_tests.lean` ~3.5 MB) routinely
    // need several minutes per file. Anything shorter than ~10 min causes
    // mid-build aborts on the bigger packages, after which test drivers fail
    // to link with VM_INVARIANT_VIOLATION.
    const LAKE_TIMEOUT_SECS: u64 = 1200;
    let output = tokio::time::timeout(
        std::time::Duration::from_secs(LAKE_TIMEOUT_SECS),
        cmd.current_dir(project_dir).output(),
    )
    .await
    .map_err(|_| anyhow!("lake build timed out after {} seconds", LAKE_TIMEOUT_SECS))?
    .map_err(|e| anyhow!("failed to execute lake: {}", e))?;

    let stdout = String::from_utf8_lossy(&output.stdout).to_string();
    let stderr = String::from_utf8_lossy(&output.stderr).to_string();
    let combined_output = format!("{}\n{}", stdout, stderr);

    // Check for errors in stderr or non-zero exit code
    let has_error =
        !output.status.success() || stderr.contains(": error") || stderr.contains("error:");

    if has_error {
        Err(anyhow!(
            "lake build failed with exit code {}\n{}",
            output.status,
            combined_output
        ))
    } else {
        Ok(combined_output)
    }
}
