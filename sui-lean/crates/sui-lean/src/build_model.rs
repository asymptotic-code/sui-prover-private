use move_core_types::account_address::AccountAddress;
use move_model::model::GlobalEnv;
use move_package::{
    package_lock::PackageLock, resolution::resolution_graph::ResolvedGraph,
    source_package::layout::SourcePackageLayout, BuildConfig as MoveBuildConfig,
};
use std::panic::{self, AssertUnwindSafe};
use std::path::{Path, PathBuf};
use std::str::FromStr;
use termcolor::Buffer;

use crate::{
    legacy_builder::ModelBuilderLegacy, prove::BuildConfig, system_dependencies::implicit_deps_for,
};

pub fn build_model(
    path: Option<&Path>,
    build_config: Option<BuildConfig>,
) -> Result<GlobalEnv, anyhow::Error> {
    let rerooted_path = reroot_path(path)?;
    let mut move_build_config = resolve_lock_file_path(
        build_config.unwrap_or_default().into(),
        Some(&rerooted_path),
    )?;

    move_build_config.implicit_dependencies = implicit_deps_for(&rerooted_path);

    move_model_for_package(move_build_config, &rerooted_path)
}

fn move_model_for_package(
    config: MoveBuildConfig,
    path: &Path,
) -> Result<GlobalEnv, anyhow::Error> {
    let flags = config.compiler_flags();
    let path_for_msg = path.to_path_buf();

    // The legacy model builder and the upstream resolution graph step
    // can panic on Move source incompatibilities (e.g. `module not
    // found: ghost`, missing methods on upstream types after a Sui
    // framework bump) before producing a structured error. Catch the
    // panic and surface it as an `anyhow::Error` so callers can report
    // which package failed rather than aborting the whole run with
    // `process::abort`.
    let outer = panic::catch_unwind(AssertUnwindSafe(move || {
        let mut resolved_graph =
            config.resolution_graph_for_package(path, None, &mut Buffer::no_color())?;
        apply_development_published_at(&mut resolved_graph, path)?;
        let _mutx = PackageLock::lock();
        ModelBuilderLegacy::create(resolved_graph).build_model(flags)
    }));
    match outer {
        Ok(r) => r,
        Err(panic_payload) => {
            let msg = panic_message(&panic_payload);
            Err(anyhow::anyhow!(
                "Move model builder panicked while building `{}`: {}",
                path_for_msg.display(),
                msg
            ))
        }
    }
}

fn panic_message(payload: &Box<dyn std::any::Any + Send>) -> String {
    if let Some(s) = payload.downcast_ref::<&'static str>() {
        return (*s).to_string();
    }
    if let Some(s) = payload.downcast_ref::<String>() {
        return s.clone();
    }
    "<non-string panic payload>".to_string()
}

fn resolve_lock_file_path(
    mut build_config: MoveBuildConfig,
    package_path: Option<&Path>,
) -> Result<MoveBuildConfig, anyhow::Error> {
    if build_config.lock_file.is_none() {
        let package_root = reroot_path(package_path)?;
        let lock_file_path = package_root.join(SourcePackageLayout::Lock.path());
        build_config.lock_file = Some(lock_file_path);
    }
    Ok(build_config)
}

pub(crate) fn apply_development_published_at(
    graph: &mut ResolvedGraph,
    package_path: &Path,
) -> Result<(), anyhow::Error> {
    let Some(package_name) = toml_string(package_path.join("Move.toml"), "package", "name")? else {
        return Ok(());
    };
    let development_manifest = package_path.join("Move.development.toml");
    if let Some(development_address) =
        toml_string(&development_manifest, "addresses", &package_name)?
    {
        let development_address =
            AccountAddress::from_str(&development_address).map_err(|err| {
                anyhow::anyhow!(
                    "invalid Move.development.toml address `{}` for `{}`: {}",
                    development_address,
                    package_name,
                    err
                )
            })?;
        if development_address != AccountAddress::ZERO {
            return Ok(());
        }
    }
    let Some(published_at) = toml_string(&development_manifest, "package", "published-at")? else {
        return Ok(());
    };
    let address = AccountAddress::from_str(&published_at).map_err(|err| {
        anyhow::anyhow!(
            "invalid Move.development.toml published-at address `{}`: {}",
            published_at,
            err
        )
    })?;
    let root = graph.root_package();
    if let Some(pkg) = graph.package_table.get_mut(&root) {
        let package_name = package_name.into();
        let should_apply = pkg
            .resolved_table
            .get(&package_name)
            .map_or(true, |current| current == &AccountAddress::ZERO);
        if should_apply {
            pkg.resolved_table.insert(package_name, address);
        }
    }
    Ok(())
}

fn toml_string(
    path: impl AsRef<Path>,
    section: &str,
    key: &str,
) -> Result<Option<String>, anyhow::Error> {
    let path = path.as_ref();
    let Ok(contents) = std::fs::read_to_string(path) else {
        return Ok(None);
    };
    let mut in_section = false;
    for line in contents.lines() {
        let line = line.split('#').next().unwrap_or("").trim();
        if line.is_empty() {
            continue;
        }
        if let Some(name) = line.strip_prefix('[').and_then(|s| s.strip_suffix(']')) {
            in_section = name.trim() == section;
            continue;
        }
        if !in_section {
            continue;
        }
        let Some((found_key, value)) = line.split_once('=') else {
            continue;
        };
        if found_key.trim() != key {
            continue;
        }
        let value = value.trim();
        if let Some(value) = value.strip_prefix('"').and_then(|s| s.strip_suffix('"')) {
            return Ok(Some(value.to_string()));
        }
        anyhow::bail!("expected string value for `{}` in {}", key, path.display());
    }
    Ok(None)
}

fn reroot_path(path: Option<&Path>) -> anyhow::Result<PathBuf> {
    let path = path
        .map(Path::canonicalize)
        .unwrap_or_else(|| PathBuf::from(".").canonicalize())?;
    let rooted_path = SourcePackageLayout::try_find_root(&path)?;
    std::env::set_current_dir(rooted_path)?;

    Ok(PathBuf::from("."))
}
