// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Lake build execution for Lean projects

use anyhow::{anyhow, Context, Result};
use log::debug;
use std::{
    ffi::{OsStr, OsString},
    io,
    path::{Path, PathBuf},
    process::Output,
    process::Stdio,
    time::Duration,
};
use tokio::io::AsyncReadExt;
use tokio::process::Command;

#[cfg(unix)]
fn kill_process_group(pid: u32) {
    use std::ffi::c_int;

    extern "C" {
        fn kill(pid: c_int, signal: c_int) -> c_int;
    }

    const SIGKILL: c_int = 9;
    let Ok(pid) = c_int::try_from(pid) else {
        return;
    };
    unsafe {
        kill(-pid, SIGKILL);
    }
}

async fn terminate_child(child: &mut tokio::process::Child, pid: Option<u32>) {
    #[cfg(unix)]
    if let Some(pid) = pid {
        kill_process_group(pid);
    }
    let _ = child.start_kill();
    let _ = child.wait().await;
}

async fn collect_pipe(task: tokio::task::JoinHandle<io::Result<Vec<u8>>>) -> io::Result<Vec<u8>> {
    task.await
        .map_err(|error| io::Error::new(io::ErrorKind::Other, error))?
}

async fn output_with_timeout(mut cmd: Command, timeout: Duration) -> io::Result<Option<Output>> {
    cmd.stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .kill_on_drop(true);
    #[cfg(unix)]
    cmd.process_group(0);

    let mut child = cmd.spawn()?;
    let pid = child.id();
    let mut stdout = child.stdout.take().expect("piped stdout");
    let mut stderr = child.stderr.take().expect("piped stderr");
    let stdout_task = tokio::spawn(async move {
        let mut output = Vec::new();
        stdout.read_to_end(&mut output).await?;
        Ok(output)
    });
    let stderr_task = tokio::spawn(async move {
        let mut output = Vec::new();
        stderr.read_to_end(&mut output).await?;
        Ok(output)
    });

    let status = match tokio::time::timeout(timeout, child.wait()).await {
        Ok(Ok(status)) => status,
        Ok(Err(error)) => {
            terminate_child(&mut child, pid).await;
            stdout_task.abort();
            stderr_task.abort();
            return Err(error);
        }
        Err(_) => {
            terminate_child(&mut child, pid).await;
            stdout_task.abort();
            stderr_task.abort();
            return Ok(None);
        }
    };
    let stdout = collect_pipe(stdout_task).await?;
    let stderr = collect_pipe(stderr_task).await?;
    Ok(Some(Output {
        status,
        stdout,
        stderr,
    }))
}

fn command_timeout_secs() -> u64 {
    std::env::var("FOXY_LAKE_TIMEOUT_SECS")
        .ok()
        .and_then(|value| value.parse().ok())
        .unwrap_or(2400)
}

fn sanitize_audit_environment(cmd: &mut Command) {
    for key in [
        "ELAN_HOME",
        "ELAN_TOOLCHAIN",
        "LEAN",
        "LEAN_PATH",
        "LEAN_SRC_PATH",
        "LEAN_GITHASH",
        "LEAN_SYSROOT",
        "LAKE_OVERRIDE_LEAN",
        "LAKE_CACHE_KEY",
        "LAKE_CACHE_ARTIFACT_ENDPOINT",
        "LAKE_CACHE_REVISION_ENDPOINT",
        "LAKE_CACHE_SERVICE",
        "LD_LIBRARY_PATH",
        "LD_PRELOAD",
        "LD_AUDIT",
        "DYLD_LIBRARY_PATH",
        "DYLD_FALLBACK_LIBRARY_PATH",
        "DYLD_INSERT_LIBRARIES",
        "DYLD_FRAMEWORK_PATH",
        "DYLD_FALLBACK_FRAMEWORK_PATH",
        "DYLD_ROOT_PATH",
        "LIBPATH",
        "SHLIB_PATH",
    ] {
        cmd.env_remove(key);
    }
    cmd.env("LAKE_CACHE_DIR", "")
        .env("LAKE_ARTIFACT_CACHE", "false")
        .env("LAKE_RESTORE_ARTIFACTS", "false")
        .env("LAKE_NO_CACHE", "true");
}

pub async fn run_lake_command<I, S>(project_dir: &Path, args: I) -> Result<Output>
where
    I: IntoIterator<Item = S>,
    S: AsRef<OsStr>,
{
    let args: Vec<OsString> = args
        .into_iter()
        .map(|arg| arg.as_ref().to_os_string())
        .collect();
    let command = args
        .iter()
        .map(|arg| arg.to_string_lossy())
        .collect::<Vec<_>>()
        .join(" ");
    let timeout_secs = command_timeout_secs();
    let mut cmd = Command::new("lake");
    cmd.args(&args).current_dir(project_dir);
    output_with_timeout(cmd, Duration::from_secs(timeout_secs))
        .await
        .map_err(|error| anyhow!("failed to execute lake: {error}"))?
        .ok_or_else(|| anyhow!("lake {command} timed out after {timeout_secs} seconds"))
}

fn canonical_executable(path: &Path, context: &str) -> Result<PathBuf> {
    let executable = path
        .canonicalize()
        .with_context(|| format!("{context}: canonicalize {}", path.display()))?;
    let metadata = std::fs::metadata(&executable)
        .with_context(|| format!("{context}: read metadata for {}", executable.display()))?;
    if !metadata.is_file() {
        return Err(anyhow!(
            "{context}: executable is not a file: {}",
            executable.display()
        ));
    }
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        if metadata.permissions().mode() & 0o111 == 0 {
            return Err(anyhow!(
                "{context}: file is not executable: {}",
                executable.display()
            ));
        }
    }
    Ok(executable)
}

fn lake_candidate_on_path() -> Result<PathBuf> {
    let path = std::env::var_os("PATH").context("PATH is not set while resolving audit Lake")?;
    let file_name = if cfg!(windows) { "lake.exe" } else { "lake" };
    for directory in std::env::split_paths(&path) {
        if !directory.is_absolute() {
            continue;
        }
        let candidate = directory.join(file_name);
        if candidate.is_file() {
            return Ok(candidate);
        }
    }
    Err(anyhow!(
        "could not resolve `lake` from absolute PATH entries"
    ))
}

fn elan_home_for_executable(candidate: &Path) -> Option<PathBuf> {
    let bin = candidate.parent()?;
    if bin.file_name()? != "bin" {
        return None;
    }
    let owner = bin.parent()?;
    let executable = if cfg!(windows) { "elan.exe" } else { "elan" };
    if owner.join("toolchains").is_dir() && owner.join("bin").join(executable).is_file() {
        return Some(owner.to_path_buf());
    }
    let toolchains = owner.parent()?;
    if toolchains.file_name()? != "toolchains" {
        return None;
    }
    let home = toolchains.parent()?;
    home.join("bin")
        .join(executable)
        .is_file()
        .then(|| home.to_path_buf())
}

fn executable_path_from_stdout(stdout: &[u8], context: &str) -> Result<PathBuf> {
    let path = std::str::from_utf8(stdout)
        .with_context(|| format!("{context}: command returned non-UTF-8 output"))?
        .trim();
    if path.is_empty() || path.lines().count() != 1 {
        return Err(anyhow!("{context}: command returned an invalid path"));
    }
    let path = Path::new(path);
    if !path.is_absolute() {
        return Err(anyhow!(
            "{context}: command returned a non-absolute path: {}",
            path.display()
        ));
    }
    canonical_executable(path, context)
}

async fn resolve_audit_lake_from_candidate(
    project_dir: &Path,
    candidate: &Path,
) -> Result<PathBuf> {
    let canonical_candidate = canonical_executable(candidate, "inherited audit Lake candidate")?;
    let Some(elan_home) = elan_home_for_executable(&canonical_candidate)
        .or_else(|| elan_home_for_executable(candidate))
    else {
        return Ok(canonical_candidate);
    };
    let elan = canonical_executable(
        &elan_home
            .join("bin")
            .join(if cfg!(windows) { "elan.exe" } else { "elan" }),
        "audit Elan selector",
    )?;
    let timeout_secs = command_timeout_secs();
    let mut cmd = Command::new(&elan);
    cmd.args(["which", "lake"]).current_dir(project_dir);
    sanitize_audit_environment(&mut cmd);
    cmd.env("ELAN_HOME", &elan_home);
    let output = output_with_timeout(cmd, Duration::from_secs(timeout_secs))
        .await
        .map_err(|error| anyhow!("failed to execute audit Elan selector: {error}"))?
        .ok_or_else(|| anyhow!("elan which lake timed out after {timeout_secs} seconds"))?;
    if !output.status.success() {
        return Err(anyhow!(
            "selecting audit Lake for {} failed:\n{}\n{}",
            project_dir.display(),
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        ));
    }
    executable_path_from_stdout(&output.stdout, "project-selected audit Lake")
}

pub async fn resolve_audit_lake_executable(project_dir: &Path) -> Result<PathBuf> {
    let candidate = lake_candidate_on_path()?;
    resolve_audit_lake_from_candidate(project_dir, &candidate).await
}

pub async fn run_audit_lake_command<I, S>(
    lake_executable: &Path,
    project_dir: &Path,
    args: I,
) -> Result<Output>
where
    I: IntoIterator<Item = S>,
    S: AsRef<OsStr>,
{
    if !lake_executable.is_absolute() {
        return Err(anyhow!(
            "audit Lake executable must be absolute: {}",
            lake_executable.display()
        ));
    }
    let args: Vec<OsString> = args
        .into_iter()
        .map(|arg| arg.as_ref().to_os_string())
        .collect();
    let command = args
        .iter()
        .map(|arg| arg.to_string_lossy())
        .collect::<Vec<_>>()
        .join(" ");
    let timeout_secs = command_timeout_secs();
    let mut cmd = Command::new(lake_executable);
    cmd.args(&args).current_dir(project_dir);
    sanitize_audit_environment(&mut cmd);
    output_with_timeout(cmd, Duration::from_secs(timeout_secs))
        .await
        .map_err(|error| anyhow!("failed to execute sanitized lake: {error}"))?
        .ok_or_else(|| anyhow!("lake {command} timed out after {timeout_secs} seconds"))
}

fn audit_lean_executable_from_prefix(stdout: &[u8]) -> Result<PathBuf> {
    let prefix = std::str::from_utf8(stdout)
        .context("project-selected `lean --print-prefix` returned non-UTF-8 output")?
        .trim();
    if prefix.is_empty() || prefix.lines().count() != 1 {
        return Err(anyhow!(
            "project-selected `lean --print-prefix` returned an invalid prefix"
        ));
    }
    let prefix = Path::new(prefix);
    if !prefix.is_absolute() {
        return Err(anyhow!(
            "project-selected Lean prefix is not absolute: {}",
            prefix.display()
        ));
    }
    let executable = prefix
        .join("bin")
        .join(if cfg!(windows) { "lean.exe" } else { "lean" });
    canonical_executable(&executable, "project-selected Lean")
}

pub async fn resolve_audit_lean_executable(
    lake_executable: &Path,
    project_dir: &Path,
) -> Result<PathBuf> {
    let output = run_audit_lake_command(
        lake_executable,
        project_dir,
        ["env", "lean", "--print-prefix"],
    )
    .await?;
    if !output.status.success() {
        return Err(anyhow!(
            "resolving the project-selected Lean executable failed:\n{}\n{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        ));
    }
    audit_lean_executable_from_prefix(&output.stdout)
}

pub async fn run_audit_lean_command<I, S>(
    lean_executable: &Path,
    working_dir: &Path,
    args: I,
) -> Result<Output>
where
    I: IntoIterator<Item = S>,
    S: AsRef<OsStr>,
{
    if !lean_executable.is_absolute() {
        return Err(anyhow!(
            "audit Lean executable must be absolute: {}",
            lean_executable.display()
        ));
    }
    let args: Vec<OsString> = args
        .into_iter()
        .map(|arg| arg.as_ref().to_os_string())
        .collect();
    let command = args
        .iter()
        .map(|arg| arg.to_string_lossy())
        .collect::<Vec<_>>()
        .join(" ");
    let timeout_secs = command_timeout_secs();
    let mut cmd = Command::new(lean_executable);
    cmd.args(&args).current_dir(working_dir);
    sanitize_audit_environment(&mut cmd);
    output_with_timeout(cmd, Duration::from_secs(timeout_secs))
        .await
        .map_err(|error| anyhow!("failed to execute sanitized lean: {error}"))?
        .ok_or_else(|| anyhow!("lean {command} timed out after {timeout_secs} seconds"))
}

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

    // 40 min default: large packages (cetus_clmm `Pool_tests.lean` ~3.5 MB)
    // routinely need several minutes per file. Anything shorter than ~10 min
    // causes mid-build aborts on the bigger packages, after which test drivers
    // fail to link with VM_INVARIANT_VIOLATION. Override with
    // `FOXY_LAKE_TIMEOUT_SECS` for heavy packages whose cumulative build (e.g.
    // sui-system's reward-math test modules) exceeds the default.
    let output = run_lake_command(
        Path::new(project_dir),
        std::iter::once("build").chain(targets.iter().map(String::as_str)),
    )
    .await?;

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

#[cfg(test)]
mod tests {
    use super::*;

    #[cfg(unix)]
    #[tokio::test]
    async fn output_with_timeout_captures_both_streams() {
        let mut cmd = Command::new("sh");
        cmd.args(["-c", "printf stdout; printf stderr >&2"]);

        let output = output_with_timeout(cmd, Duration::from_secs(5))
            .await
            .unwrap()
            .unwrap();

        assert!(output.status.success());
        assert_eq!(output.stdout, b"stdout");
        assert_eq!(output.stderr, b"stderr");
    }

    #[cfg(unix)]
    #[tokio::test]
    async fn timeout_kills_the_child_process_group() {
        let temp = tempfile::tempdir().unwrap();
        let marker = temp.path().join("grandchild-survived");
        let mut cmd = Command::new("sh");
        cmd.arg("-c")
            .arg("(sleep 1; printf survived > \"$1\") & wait")
            .arg("lake-timeout-test")
            .arg(&marker);

        let output = output_with_timeout(cmd, Duration::from_millis(100))
            .await
            .unwrap();

        assert!(output.is_none());
        tokio::time::sleep(Duration::from_millis(1200)).await;
        assert!(!marker.exists(), "grandchild survived the timeout");
    }

    #[test]
    fn audit_environment_is_fail_closed() {
        let mut cmd = Command::new("lean");
        for key in [
            "ELAN_HOME",
            "ELAN_TOOLCHAIN",
            "LEAN",
            "LEAN_PATH",
            "LEAN_SRC_PATH",
            "LEAN_GITHASH",
            "LEAN_SYSROOT",
            "LAKE_OVERRIDE_LEAN",
            "LAKE_CACHE_KEY",
            "LAKE_CACHE_ARTIFACT_ENDPOINT",
            "LAKE_CACHE_REVISION_ENDPOINT",
            "LAKE_CACHE_SERVICE",
            "LD_LIBRARY_PATH",
            "LD_PRELOAD",
            "LD_AUDIT",
            "DYLD_LIBRARY_PATH",
            "DYLD_FALLBACK_LIBRARY_PATH",
            "DYLD_INSERT_LIBRARIES",
            "DYLD_FRAMEWORK_PATH",
            "DYLD_FALLBACK_FRAMEWORK_PATH",
            "DYLD_ROOT_PATH",
            "LIBPATH",
            "SHLIB_PATH",
        ] {
            cmd.env(key, "attacker-controlled");
        }
        sanitize_audit_environment(&mut cmd);

        let env = cmd
            .as_std()
            .get_envs()
            .map(|(key, value)| {
                (
                    key.to_string_lossy().into_owned(),
                    value.map(|value| value.to_string_lossy().into_owned()),
                )
            })
            .collect::<std::collections::BTreeMap<_, _>>();
        for key in [
            "ELAN_HOME",
            "ELAN_TOOLCHAIN",
            "LEAN",
            "LEAN_PATH",
            "LEAN_SRC_PATH",
            "LEAN_GITHASH",
            "LEAN_SYSROOT",
            "LAKE_OVERRIDE_LEAN",
            "LAKE_CACHE_KEY",
            "LAKE_CACHE_ARTIFACT_ENDPOINT",
            "LAKE_CACHE_REVISION_ENDPOINT",
            "LAKE_CACHE_SERVICE",
            "LD_LIBRARY_PATH",
            "LD_PRELOAD",
            "LD_AUDIT",
            "DYLD_LIBRARY_PATH",
            "DYLD_FALLBACK_LIBRARY_PATH",
            "DYLD_INSERT_LIBRARIES",
            "DYLD_FRAMEWORK_PATH",
            "DYLD_FALLBACK_FRAMEWORK_PATH",
            "DYLD_ROOT_PATH",
            "LIBPATH",
            "SHLIB_PATH",
        ] {
            assert_eq!(env.get(key), Some(&None));
        }
        assert_eq!(env["LAKE_CACHE_DIR"], Some(String::new()));
        assert_eq!(env["LAKE_ARTIFACT_CACHE"], Some("false".to_string()));
        assert_eq!(env["LAKE_RESTORE_ARTIFACTS"], Some("false".to_string()));
        assert_eq!(env["LAKE_NO_CACHE"], Some("true".to_string()));
    }

    #[test]
    fn audit_lean_prefix_must_be_one_absolute_path() {
        assert!(audit_lean_executable_from_prefix(b"").is_err());
        assert!(audit_lean_executable_from_prefix(b"relative/toolchain").is_err());
        assert!(audit_lean_executable_from_prefix(b"/one\n/two\n").is_err());
    }

    #[cfg(unix)]
    #[tokio::test]
    async fn actual_toolchain_lake_alias_reselects_the_project_pin() {
        use std::os::unix::fs::symlink;

        const TOOLCHAIN: &str = "leanprover/lean4:v4.17.0-rc1";
        let available = std::process::Command::new("elan")
            .args(["run", TOOLCHAIN, "lake", "--version"])
            .output()
            .is_ok_and(|output| output.status.success());
        if !available {
            return;
        }
        let prefix_output = std::process::Command::new("lean")
            .arg("--print-prefix")
            .output()
            .unwrap();
        if !prefix_output.status.success() {
            return;
        }
        let prefix = Path::new(std::str::from_utf8(&prefix_output.stdout).unwrap().trim());
        let actual_lake = prefix.join("bin/lake").canonicalize().unwrap();
        let actual_version = std::process::Command::new(&actual_lake)
            .arg("--version")
            .output()
            .unwrap();
        if String::from_utf8_lossy(&actual_version.stdout).contains("4.17.0-rc1") {
            return;
        }

        let project = tempfile::tempdir().unwrap();
        std::fs::write(
            project.path().join("lean-toolchain"),
            format!("{TOOLCHAIN}\n"),
        )
        .unwrap();
        let alias_root = tempfile::tempdir().unwrap();
        let alias = alias_root.path().join("lake");
        symlink(&actual_lake, &alias).unwrap();

        let selected = resolve_audit_lake_from_candidate(project.path(), &alias)
            .await
            .unwrap();
        assert_ne!(selected, actual_lake);
        let selected_version = run_audit_lake_command(&selected, project.path(), ["--version"])
            .await
            .unwrap();

        assert!(selected_version.status.success());
        assert!(String::from_utf8_lossy(&selected_version.stdout).contains("4.17.0-rc1"));
    }

    #[cfg(unix)]
    #[tokio::test]
    async fn selected_lean_executable_runs_from_the_isolated_working_directory() {
        use std::os::unix::fs::PermissionsExt;

        let toolchain = tempfile::tempdir().unwrap();
        let bin = toolchain.path().join("bin");
        std::fs::create_dir(&bin).unwrap();
        let lean = bin.join("lean");
        std::fs::write(&lean, "#!/bin/sh\nprintf '%s' \"$PWD\"\n").unwrap();
        std::fs::set_permissions(&lean, std::fs::Permissions::from_mode(0o700)).unwrap();

        let selected =
            audit_lean_executable_from_prefix(toolchain.path().to_str().unwrap().as_bytes())
                .unwrap();
        assert_eq!(selected, lean.canonicalize().unwrap());

        let isolated = tempfile::tempdir().unwrap();
        let output = run_audit_lean_command(&selected, isolated.path(), std::iter::empty::<&str>())
            .await
            .unwrap();

        assert!(output.status.success());
        assert_eq!(
            Path::new(std::str::from_utf8(&output.stdout).unwrap())
                .canonicalize()
                .unwrap(),
            isolated.path().canonicalize().unwrap()
        );
    }
}
