use std::collections::{BTreeMap, BTreeSet};
use std::io::Write as _;
use std::path::{Component, Path, PathBuf};

use serde::{Deserialize, Serialize};

use super::{RenderError, RenderResult};

pub(crate) const OWNED_MANIFEST_FILE: &str = ".sui-lean-generated-files.toml";
const PENDING_JOURNAL_FILE: &str = ".sui-lean-generation-pending.toml";
const FORMAT_VERSION: u32 = 1;
const PRESERVED_ROOTS: [&str; 4] = [".lake", "Drivers", "Proofs", "Correctness"];

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum BootstrapPolicy {
    RefuseExisting,
    AdoptExistingPlannedPaths,
}

#[derive(Clone)]
pub(crate) struct PlannedFile {
    contents: Vec<u8>,
    permissions: Option<std::fs::Permissions>,
}

#[derive(Default)]
pub(crate) struct RenderPlan {
    files: BTreeMap<PathBuf, PlannedFile>,
    removals: BTreeSet<PathBuf>,
    /// Removals of files the manifest does not own, which `publish` would
    /// otherwise refuse as unmanaged collisions. See [`RenderPlan::reclaim`].
    reclaimed: BTreeSet<PathBuf>,
}

impl RenderPlan {
    pub(crate) fn new() -> Self {
        Self::default()
    }

    pub(crate) fn from_staging_tree(staging_dir: &Path) -> RenderResult<Self> {
        require_directory(staging_dir, "render staging root")?;
        let mut plan = Self::new();
        collect_staging_files(staging_dir, staging_dir, &mut plan)?;
        Ok(plan)
    }

    pub(crate) fn insert(
        &mut self,
        relative_path: impl AsRef<Path>,
        contents: impl Into<Vec<u8>>,
    ) -> RenderResult<()> {
        self.insert_with_permissions(relative_path.as_ref(), contents.into(), None)
    }

    fn insert_with_permissions(
        &mut self,
        relative_path: &Path,
        contents: Vec<u8>,
        permissions: Option<std::fs::Permissions>,
    ) -> RenderResult<()> {
        let relative_path = validated_owned_path(relative_path)?;
        self.require_new_path(&relative_path)?;
        self.files.insert(
            relative_path,
            PlannedFile {
                contents,
                permissions,
            },
        );
        Ok(())
    }

    pub(crate) fn remove(&mut self, relative_path: impl AsRef<Path>) -> RenderResult<()> {
        let relative_path = validated_owned_path(relative_path.as_ref())?;
        self.require_new_path(&relative_path)?;
        self.removals.insert(relative_path);
        Ok(())
    }

    /// Delete a file the ownership manifest does NOT list.
    ///
    /// `publish` normally refuses to touch an existing unmanaged path -- the
    /// renderer must never destroy something another writer owns. The one
    /// exception is a file sitting inside a directory the renderer owns
    /// wholesale (a user package, a lemma library, `Generated/`,
    /// `proof_scaffolds/`), which a bootstrap render would already have
    /// deleted. The retired `move-prover-lean-backend` drops exactly such
    /// files there and keeps no manifest, so nothing else can ever reclaim
    /// them. Callers must have established that containment themselves;
    /// this is a narrower `remove`, not a general override.
    pub(crate) fn reclaim(&mut self, relative_path: impl AsRef<Path>) -> RenderResult<()> {
        let relative_path = validated_owned_path(relative_path.as_ref())?;
        self.require_new_path(&relative_path)?;
        self.reclaimed.insert(relative_path.clone());
        self.removals.insert(relative_path);
        Ok(())
    }

    fn require_new_path(&self, candidate: &Path) -> RenderResult<()> {
        if self.files.contains_key(candidate) || self.removals.contains(candidate) {
            return Err(materialize_error(format!(
                "render plan contains duplicate path {}",
                candidate.display()
            )));
        }
        if let Some(conflict) = self
            .files
            .keys()
            .chain(self.removals.iter())
            .find(|existing| paths_overlap(existing, candidate))
        {
            return Err(materialize_error(format!(
                "render plan paths overlap: {} and {}",
                conflict.display(),
                candidate.display()
            )));
        }
        Ok(())
    }

    pub(crate) fn files(&self) -> &BTreeMap<PathBuf, PlannedFile> {
        &self.files
    }

    pub(crate) fn removals(&self) -> &BTreeSet<PathBuf> {
        &self.removals
    }

    pub(crate) fn publish(&self, output_dir: &Path) -> RenderResult<RenderPublication> {
        self.publish_with_bootstrap(output_dir, BootstrapPolicy::RefuseExisting)
    }

    pub(crate) fn publish_with_bootstrap(
        &self,
        output_dir: &Path,
        bootstrap: BootstrapPolicy,
    ) -> RenderResult<RenderPublication> {
        publish_render_plan(self, output_dir, bootstrap, FailureHook::default())
    }

    #[cfg(test)]
    fn publish_failing_at(
        &self,
        output_dir: &Path,
        bootstrap: BootstrapPolicy,
        operation: usize,
    ) -> RenderResult<RenderPublication> {
        publish_render_plan(
            self,
            output_dir,
            bootstrap,
            FailureHook {
                fail_at: Some(operation),
                seen: 0,
                fail_after_mutation_at: None,
                mutations_seen: 0,
            },
        )
    }

    #[cfg(test)]
    fn publish_failing_after_mutation_at(
        &self,
        output_dir: &Path,
        bootstrap: BootstrapPolicy,
        mutation: usize,
    ) -> RenderResult<RenderPublication> {
        publish_render_plan(
            self,
            output_dir,
            bootstrap,
            FailureHook {
                fail_at: None,
                seen: 0,
                fail_after_mutation_at: Some(mutation),
                mutations_seen: 0,
            },
        )
    }
}

#[must_use = "commit the render publication or retain it as a rollback guard"]
pub(crate) struct RenderPublication {
    output_dir: PathBuf,
    applied: Vec<AppliedMutation>,
    created_directories: Vec<PathBuf>,
    journal_original: Option<FileSnapshot>,
    finalized: bool,
}

impl RenderPublication {
    pub(crate) fn commit(mut self) -> RenderResult<()> {
        self.finalized = true;
        remove_metadata_file(&self.output_dir, PENDING_JOURNAL_FILE)
    }

    pub(crate) fn rollback(mut self) -> RenderResult<()> {
        match rollback_changes(&self.output_dir, &self.applied, &self.created_directories) {
            Ok(()) => {
                restore_metadata_file(
                    &self.output_dir,
                    PENDING_JOURNAL_FILE,
                    self.journal_original.as_ref(),
                )?;
                self.finalized = true;
                Ok(())
            }
            Err(error) => {
                self.finalized = true;
                Err(error)
            }
        }
    }
}

impl Drop for RenderPublication {
    fn drop(&mut self) {
        if self.finalized {
            return;
        }
        self.finalized = true;
        let result = rollback_changes(&self.output_dir, &self.applied, &self.created_directories)
            .and_then(|()| {
                restore_metadata_file(
                    &self.output_dir,
                    PENDING_JOURNAL_FILE,
                    self.journal_original.as_ref(),
                )
            });
        if let Err(error) = result {
            eprintln!(
                "failed to roll back uncommitted render publication in {}: {error:?}; {} was retained for forward recovery",
                self.output_dir.display(),
                PENDING_JOURNAL_FILE
            );
        }
    }
}

#[derive(Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct OwnedManifest {
    version: u32,
    files: Vec<String>,
}

#[derive(Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct PendingJournal {
    version: u32,
    base_manifest: Option<Vec<String>>,
    target_manifest: Vec<String>,
    owned_during_transaction: Vec<String>,
}

#[derive(Clone)]
struct FileSnapshot {
    contents: Vec<u8>,
    permissions: std::fs::Permissions,
}

struct AppliedMutation {
    relative_path: PathBuf,
    original: Option<FileSnapshot>,
    replacement: Option<FileSnapshot>,
}

#[derive(Default)]
struct FailureHook {
    #[cfg(test)]
    fail_at: Option<usize>,
    #[cfg(test)]
    seen: usize,
    #[cfg(test)]
    fail_after_mutation_at: Option<usize>,
    #[cfg(test)]
    mutations_seen: usize,
}

impl FailureHook {
    fn before_operation(&mut self, relative_path: &Path) -> RenderResult<()> {
        #[cfg(test)]
        {
            self.seen += 1;
            if self.fail_at == Some(self.seen) {
                return Err(materialize_error(format!(
                    "injected materialization failure at operation {} ({})",
                    self.seen,
                    relative_path.display()
                )));
            }
        }
        #[cfg(not(test))]
        let _ = relative_path;
        Ok(())
    }

    fn after_mutation(&mut self, relative_path: &Path) -> RenderResult<()> {
        #[cfg(test)]
        {
            self.mutations_seen += 1;
            if self.fail_after_mutation_at == Some(self.mutations_seen) {
                return Err(materialize_error(format!(
                    "injected materialization failure after mutation {} ({})",
                    self.mutations_seen,
                    relative_path.display()
                )));
            }
        }
        #[cfg(not(test))]
        let _ = relative_path;
        Ok(())
    }
}

fn materialize_error(what: impl Into<String>) -> RenderError {
    RenderError::Io { what: what.into() }
}

fn paths_overlap(left: &Path, right: &Path) -> bool {
    left.starts_with(right) || right.starts_with(left)
}

fn validated_relative_path(path: &Path) -> RenderResult<PathBuf> {
    if path.as_os_str().is_empty() || path.is_absolute() {
        return Err(materialize_error(format!(
            "generated path must be non-empty and relative: {}",
            path.display()
        )));
    }
    let mut normalized = PathBuf::new();
    for component in path.components() {
        match component {
            Component::Normal(name) if !name.is_empty() => normalized.push(name),
            _ => {
                return Err(materialize_error(format!(
                    "generated path contains a non-normal component: {}",
                    path.display()
                )));
            }
        }
    }
    let Some(path_utf8) = path.to_str() else {
        return Err(materialize_error(format!(
            "generated path is not canonical UTF-8: {}",
            path.display()
        )));
    };
    let Some(normalized_utf8) = normalized.to_str() else {
        return Err(materialize_error(format!(
            "generated path is not canonical UTF-8: {}",
            path.display()
        )));
    };
    // Render plans use `/` as their portable manifest separator. `PathBuf`
    // materialization changes those separators to `\` on Windows, so compare
    // the normalized spelling rather than platform-specific OsStr bytes.
    if normalized_utf8.replace('\\', "/") != path_utf8.replace('\\', "/") {
        return Err(materialize_error(format!(
            "generated path is not canonical UTF-8: {}",
            path.display()
        )));
    }
    Ok(normalized)
}

pub(crate) fn is_preserved_root(name: &str) -> bool {
    PRESERVED_ROOTS.contains(&name)
}

fn validated_owned_path(path: &Path) -> RenderResult<PathBuf> {
    let path = validated_relative_path(path)?;
    let first = path
        .components()
        .next()
        .and_then(|component| component.as_os_str().to_str())
        .expect("validated path has a normal first component");
    if PRESERVED_ROOTS.contains(&first)
        || path == Path::new(OWNED_MANIFEST_FILE)
        || path == Path::new(PENDING_JOURNAL_FILE)
    {
        return Err(materialize_error(format!(
            "render plan may not own reserved path {}",
            path.display()
        )));
    }
    Ok(path)
}

fn require_directory(path: &Path, label: &str) -> RenderResult<()> {
    let metadata = std::fs::symlink_metadata(path).map_err(|error| {
        materialize_error(format!("inspect {label} {}: {error}", path.display()))
    })?;
    if metadata.file_type().is_symlink() || !metadata.is_dir() {
        return Err(materialize_error(format!(
            "{label} must be a non-symlink directory: {}",
            path.display()
        )));
    }
    Ok(())
}

fn collect_staging_files(root: &Path, directory: &Path, plan: &mut RenderPlan) -> RenderResult<()> {
    let mut entries = std::fs::read_dir(directory)
        .map_err(|error| {
            materialize_error(format!(
                "read render staging directory {}: {error}",
                directory.display()
            ))
        })?
        .collect::<Result<Vec<_>, _>>()
        .map_err(|error| {
            materialize_error(format!(
                "read entry under render staging directory {}: {error}",
                directory.display()
            ))
        })?;
    entries.sort_by_key(|entry| entry.file_name());
    for entry in entries {
        let path = entry.path();
        let relative = path
            .strip_prefix(root)
            .expect("staging entry remains beneath staging root");
        let metadata = std::fs::symlink_metadata(&path).map_err(|error| {
            materialize_error(format!("inspect staged path {}: {error}", path.display()))
        })?;
        if metadata.file_type().is_symlink() {
            return Err(materialize_error(format!(
                "render staging tree must not contain symlinks: {}",
                path.display()
            )));
        }
        let first = relative
            .components()
            .next()
            .and_then(|component| component.as_os_str().to_str());
        if first.is_some_and(|first| PRESERVED_ROOTS.contains(&first)) {
            if metadata.is_dir() {
                continue;
            }
            return Err(materialize_error(format!(
                "reserved render path must be a directory: {}",
                path.display()
            )));
        }
        if metadata.is_dir() {
            validated_owned_path(relative)?;
            collect_staging_files(root, &path, plan)?;
        } else if metadata.is_file() {
            let contents = std::fs::read(&path).map_err(|error| {
                materialize_error(format!("read staged file {}: {error}", path.display()))
            })?;
            plan.insert_with_permissions(relative, contents, Some(metadata.permissions()))?;
        } else {
            return Err(materialize_error(format!(
                "render staging tree contains a non-regular entry: {}",
                path.display()
            )));
        }
    }
    Ok(())
}

fn encode_paths(paths: &BTreeSet<PathBuf>) -> RenderResult<Vec<String>> {
    paths
        .iter()
        .map(|path| {
            path.to_str()
                .map(str::to_string)
                .ok_or_else(|| materialize_error("generated path is not UTF-8"))
        })
        .collect()
}

fn decode_paths(raw: Vec<String>, label: &str) -> RenderResult<BTreeSet<PathBuf>> {
    let mut paths = BTreeSet::new();
    for raw_path in raw {
        let path = validated_owned_path(Path::new(&raw_path))?;
        if !paths.insert(path.clone()) {
            return Err(materialize_error(format!(
                "{label} contains duplicate path {}",
                path.display()
            )));
        }
    }
    for path in &paths {
        if let Some(conflict) = paths
            .iter()
            .find(|other| *other != path && paths_overlap(other, path))
        {
            return Err(materialize_error(format!(
                "{label} paths overlap: {} and {}",
                path.display(),
                conflict.display()
            )));
        }
    }
    Ok(paths)
}

fn manifest_contents(paths: &BTreeSet<PathBuf>) -> RenderResult<Vec<u8>> {
    toml::to_string_pretty(&OwnedManifest {
        version: FORMAT_VERSION,
        files: encode_paths(paths)?,
    })
    .map(String::into_bytes)
    .map_err(|error| materialize_error(format!("serialize renderer-owned manifest: {error}")))
}

fn parse_manifest(path: &Path, contents: &[u8]) -> RenderResult<BTreeSet<PathBuf>> {
    let text = std::str::from_utf8(contents).map_err(|error| {
        materialize_error(format!(
            "renderer-owned manifest {} is not UTF-8: {error}",
            path.display()
        ))
    })?;
    let manifest: OwnedManifest = toml::from_str(text).map_err(|error| {
        materialize_error(format!(
            "parse renderer-owned manifest {}: {error}",
            path.display()
        ))
    })?;
    if manifest.version != FORMAT_VERSION {
        return Err(materialize_error(format!(
            "renderer-owned manifest {} has unsupported version {}",
            path.display(),
            manifest.version
        )));
    }
    decode_paths(manifest.files, "renderer-owned manifest")
}

fn journal_contents(
    base: Option<&BTreeSet<PathBuf>>,
    target: &BTreeSet<PathBuf>,
    owned_during_transaction: &BTreeSet<PathBuf>,
) -> RenderResult<Vec<u8>> {
    toml::to_string_pretty(&PendingJournal {
        version: FORMAT_VERSION,
        base_manifest: base.map(encode_paths).transpose()?,
        target_manifest: encode_paths(target)?,
        owned_during_transaction: encode_paths(owned_during_transaction)?,
    })
    .map(String::into_bytes)
    .map_err(|error| materialize_error(format!("serialize pending generation journal: {error}")))
}

struct ParsedJournal {
    base: Option<BTreeSet<PathBuf>>,
    target: BTreeSet<PathBuf>,
    owned: BTreeSet<PathBuf>,
}

fn parse_journal(path: &Path, contents: &[u8]) -> RenderResult<ParsedJournal> {
    let text = std::str::from_utf8(contents).map_err(|error| {
        materialize_error(format!(
            "pending generation journal {} is not UTF-8: {error}",
            path.display()
        ))
    })?;
    let journal: PendingJournal = toml::from_str(text).map_err(|error| {
        materialize_error(format!(
            "parse pending generation journal {}: {error}",
            path.display()
        ))
    })?;
    if journal.version != FORMAT_VERSION {
        return Err(materialize_error(format!(
            "pending generation journal {} has unsupported version {}",
            path.display(),
            journal.version
        )));
    }
    let parsed = ParsedJournal {
        base: journal
            .base_manifest
            .map(|paths| decode_paths(paths, "pending journal base manifest"))
            .transpose()?,
        target: decode_paths(journal.target_manifest, "pending journal target manifest")?,
        owned: decode_paths(
            journal.owned_during_transaction,
            "pending journal ownership",
        )?,
    };
    if parsed
        .base
        .as_ref()
        .is_some_and(|base| !base.is_subset(&parsed.owned))
        || !parsed.target.is_subset(&parsed.owned)
    {
        return Err(materialize_error(format!(
            "pending generation journal {} omits base or target ownership",
            path.display()
        )));
    }
    Ok(parsed)
}

fn permission_state(permissions: &std::fs::Permissions) -> u32 {
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt as _;
        permissions.mode()
    }
    #[cfg(not(unix))]
    {
        u32::from(permissions.readonly())
    }
}

fn inspect_relative_file(
    output_dir: &Path,
    relative_path: &Path,
) -> RenderResult<Option<FileSnapshot>> {
    let relative_path = validated_relative_path(relative_path)?;
    let components = relative_path.components().collect::<Vec<_>>();
    let mut current = output_dir.to_path_buf();
    for component in components.iter().take(components.len() - 1) {
        let Component::Normal(name) = component else {
            unreachable!("validated relative path has only normal components")
        };
        current.push(name);
        match std::fs::symlink_metadata(&current) {
            Ok(metadata) if metadata.file_type().is_symlink() || !metadata.is_dir() => {
                return Err(materialize_error(format!(
                    "unsupported generated file/directory layout transition at {}",
                    current.display()
                )));
            }
            Ok(_) => {}
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => return Ok(None),
            Err(error) => {
                return Err(materialize_error(format!(
                    "inspect managed output parent {}: {error}",
                    current.display()
                )));
            }
        }
    }
    let path = output_dir.join(&relative_path);
    let metadata = match std::fs::symlink_metadata(&path) {
        Ok(metadata) if metadata.file_type().is_symlink() || !metadata.is_file() => {
            return Err(materialize_error(format!(
                "unsupported generated file/directory layout transition at {}",
                path.display()
            )));
        }
        Ok(metadata) => metadata,
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => return Ok(None),
        Err(error) => {
            return Err(materialize_error(format!(
                "inspect managed output {}: {error}",
                path.display()
            )));
        }
    };
    let contents = std::fs::read(&path).map_err(|error| {
        materialize_error(format!("read managed output {}: {error}", path.display()))
    })?;
    Ok(Some(FileSnapshot {
        contents,
        permissions: metadata.permissions(),
    }))
}

fn same_state(left: &Option<FileSnapshot>, right: &Option<FileSnapshot>) -> bool {
    match (left, right) {
        (None, None) => true,
        (Some(left), Some(right)) => {
            left.contents == right.contents
                && permission_state(&left.permissions) == permission_state(&right.permissions)
        }
        _ => false,
    }
}

fn require_file_state(
    output_dir: &Path,
    relative_path: &Path,
    expected: &Option<FileSnapshot>,
) -> RenderResult<()> {
    let current = inspect_relative_file(output_dir, relative_path)?;
    if same_state(&current, expected) {
        Ok(())
    } else {
        Err(materialize_error(format!(
            "managed output changed during publication: {}",
            output_dir.join(relative_path).display()
        )))
    }
}

fn ensure_parent_directories(
    output_dir: &Path,
    relative_path: &Path,
    created: &mut Vec<PathBuf>,
) -> RenderResult<PathBuf> {
    let parent = relative_path
        .parent()
        .expect("validated relative file path has a parent");
    let mut current = output_dir.to_path_buf();
    for component in parent.components() {
        let Component::Normal(name) = component else {
            unreachable!("validated relative path has only normal components")
        };
        let containing = current.clone();
        current.push(name);
        match std::fs::symlink_metadata(&current) {
            Ok(metadata) if metadata.file_type().is_symlink() || !metadata.is_dir() => {
                return Err(materialize_error(format!(
                    "unsupported generated file/directory layout transition at {}",
                    current.display()
                )));
            }
            Ok(_) => {}
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => {
                std::fs::create_dir(&current).map_err(|error| {
                    materialize_error(format!(
                        "create managed output directory {}: {error}",
                        current.display()
                    ))
                })?;
                created.push(current.clone());
                sync_directory(&containing)?;
            }
            Err(error) => {
                return Err(materialize_error(format!(
                    "inspect managed output parent {}: {error}",
                    current.display()
                )));
            }
        }
    }
    Ok(output_dir.join(relative_path))
}

fn sync_directory(path: &Path) -> RenderResult<()> {
    #[cfg(windows)]
    {
        let _ = path;
        return Ok(());
    }
    #[cfg(not(windows))]
    let directory = std::fs::File::open(path).map_err(|error| {
        materialize_error(format!("open output directory {}: {error}", path.display()))
    })?;
    #[cfg(not(windows))]
    directory.sync_all().map_err(|error| {
        materialize_error(format!("sync output directory {}: {error}", path.display()))
    })
}

fn persist_file(
    path: &Path,
    contents: &[u8],
    permissions: Option<std::fs::Permissions>,
) -> RenderResult<()> {
    persist_file_without_parent_sync(path, contents, permissions)?;
    sync_directory(
        path.parent()
            .expect("managed output file has a parent directory"),
    )
}

fn persist_file_without_parent_sync(
    path: &Path,
    contents: &[u8],
    permissions: Option<std::fs::Permissions>,
) -> RenderResult<FileSnapshot> {
    let parent = path
        .parent()
        .expect("managed output file has a parent directory");
    #[allow(unused_mut)]
    let mut builder = tempfile::Builder::new();
    #[cfg(unix)]
    if permissions.is_none() {
        use std::os::unix::fs::PermissionsExt as _;
        builder.permissions(std::fs::Permissions::from_mode(0o666));
    }
    let mut temporary = builder.tempfile_in(parent).map_err(|error| {
        materialize_error(format!(
            "create temporary managed output under {}: {error}",
            parent.display()
        ))
    })?;
    temporary.write_all(contents).map_err(|error| {
        materialize_error(format!(
            "write temporary managed output for {}: {error}",
            path.display()
        ))
    })?;
    temporary.flush().map_err(|error| {
        materialize_error(format!(
            "flush temporary managed output for {}: {error}",
            path.display()
        ))
    })?;
    if let Some(permissions) = permissions {
        temporary
            .as_file()
            .set_permissions(permissions)
            .map_err(|error| {
                materialize_error(format!(
                    "set temporary managed output permissions for {}: {error}",
                    path.display()
                ))
            })?;
    }
    temporary.as_file().sync_all().map_err(|error| {
        materialize_error(format!(
            "sync temporary managed output for {}: {error}",
            path.display()
        ))
    })?;
    let replacement_permissions = temporary
        .as_file()
        .metadata()
        .map_err(|error| {
            materialize_error(format!(
                "inspect temporary managed output for {}: {error}",
                path.display()
            ))
        })?
        .permissions();
    temporary.persist(path).map_err(|error| {
        materialize_error(format!(
            "publish managed output {}: {}",
            path.display(),
            error.error
        ))
    })?;
    Ok(FileSnapshot {
        contents: contents.to_vec(),
        permissions: replacement_permissions,
    })
}

fn apply_write(
    output_dir: &Path,
    relative_path: &Path,
    contents: &[u8],
    new_permissions: Option<std::fs::Permissions>,
    original: Option<FileSnapshot>,
    created_directories: &mut Vec<PathBuf>,
    applied: &mut Vec<AppliedMutation>,
    failure_hook: &mut FailureHook,
) -> RenderResult<()> {
    require_file_state(output_dir, relative_path, &original)?;
    let path = ensure_parent_directories(output_dir, relative_path, created_directories)?;
    let permissions = original
        .as_ref()
        .map(|snapshot| snapshot.permissions.clone())
        .or(new_permissions);
    let replacement = persist_file_without_parent_sync(&path, contents, permissions)?;
    applied.push(AppliedMutation {
        relative_path: relative_path.to_path_buf(),
        original,
        replacement: Some(replacement),
    });
    failure_hook.after_mutation(relative_path)?;
    sync_directory(path.parent().expect("managed output file has a parent"))
}

fn apply_delete(
    output_dir: &Path,
    relative_path: &Path,
    original: FileSnapshot,
    applied: &mut Vec<AppliedMutation>,
    failure_hook: &mut FailureHook,
) -> RenderResult<()> {
    require_file_state(output_dir, relative_path, &Some(original.clone()))?;
    let path = output_dir.join(relative_path);
    std::fs::remove_file(&path).map_err(|error| {
        materialize_error(format!(
            "remove stale managed output {}: {error}",
            path.display()
        ))
    })?;
    applied.push(AppliedMutation {
        relative_path: relative_path.to_path_buf(),
        original: Some(original),
        replacement: None,
    });
    failure_hook.after_mutation(relative_path)?;
    sync_directory(path.parent().expect("managed output file has a parent"))
}

fn rollback_mutation(output_dir: &Path, mutation: &AppliedMutation) -> RenderResult<()> {
    let current = inspect_relative_file(output_dir, &mutation.relative_path)?;
    if !same_state(&current, &mutation.replacement) {
        return Err(materialize_error(format!(
            "managed output changed before rollback: {}",
            output_dir.join(&mutation.relative_path).display()
        )));
    }
    let path = output_dir.join(&mutation.relative_path);
    if let Some(original) = &mutation.original {
        persist_file(
            &path,
            &original.contents,
            Some(original.permissions.clone()),
        )?;
    } else {
        std::fs::remove_file(&path).map_err(|error| {
            materialize_error(format!(
                "remove added managed output during rollback {}: {error}",
                path.display()
            ))
        })?;
        sync_directory(path.parent().expect("managed output file has a parent"))?;
    }
    Ok(())
}

fn rollback_changes(
    output_dir: &Path,
    applied: &[AppliedMutation],
    created_directories: &[PathBuf],
) -> RenderResult<()> {
    let mut failures = Vec::new();
    for mutation in applied.iter().rev() {
        if let Err(error) = rollback_mutation(output_dir, mutation) {
            failures.push(format!("{error:?}"));
        }
    }
    for directory in created_directories.iter().rev() {
        match std::fs::remove_dir(directory) {
            Ok(()) => {
                if let Some(parent) = directory.parent() {
                    if let Err(error) = sync_directory(parent) {
                        failures.push(format!("{error:?}"));
                    }
                }
            }
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => {}
            Err(error) => failures.push(format!(
                "remove created output directory {}: {error}",
                directory.display()
            )),
        }
    }
    if failures.is_empty() {
        Ok(())
    } else {
        Err(materialize_error(format!(
            "render publication rollback failed: {}",
            failures.join("; ")
        )))
    }
}

fn restore_metadata_file(
    output_dir: &Path,
    name: &str,
    original: Option<&FileSnapshot>,
) -> RenderResult<()> {
    let path = output_dir.join(name);
    if let Some(original) = original {
        persist_file(
            &path,
            &original.contents,
            Some(original.permissions.clone()),
        )
    } else {
        remove_metadata_file(output_dir, name)
    }
}

fn remove_metadata_file(output_dir: &Path, name: &str) -> RenderResult<()> {
    let path = output_dir.join(name);
    match std::fs::remove_file(&path) {
        Ok(()) => sync_directory(output_dir),
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => Ok(()),
        Err(error) => Err(materialize_error(format!(
            "remove generation metadata {}: {error}",
            path.display()
        ))),
    }
}

fn rollback_after_failure(
    output_dir: &Path,
    applied: &[AppliedMutation],
    created_directories: &[PathBuf],
    journal_original: Option<&FileSnapshot>,
    primary: RenderError,
) -> RenderError {
    match rollback_changes(output_dir, applied, created_directories) {
        Ok(()) => match restore_metadata_file(output_dir, PENDING_JOURNAL_FILE, journal_original) {
            Ok(()) => primary,
            Err(rollback) => materialize_error(format!(
                "materialization failed ({primary:?}); journal rollback also failed ({rollback:?})"
            )),
        },
        Err(rollback) => materialize_error(format!(
            "materialization failed ({primary:?}); rollback also failed ({rollback:?}); {} was retained for forward recovery",
            PENDING_JOURNAL_FILE
        )),
    }
}

fn publish_render_plan(
    plan: &RenderPlan,
    output_dir: &Path,
    bootstrap: BootstrapPolicy,
    mut failure_hook: FailureHook,
) -> RenderResult<RenderPublication> {
    require_directory(output_dir, "render output")?;
    let manifest_relative = Path::new(OWNED_MANIFEST_FILE);
    let journal_relative = Path::new(PENDING_JOURNAL_FILE);
    let manifest_path = output_dir.join(manifest_relative);
    let journal_path = output_dir.join(journal_relative);
    let manifest_snapshot = inspect_relative_file(output_dir, manifest_relative)?;
    let journal_snapshot = inspect_relative_file(output_dir, journal_relative)?;
    let current_manifest = manifest_snapshot
        .as_ref()
        .map(|snapshot| parse_manifest(&manifest_path, &snapshot.contents))
        .transpose()?;
    let recovered = journal_snapshot
        .as_ref()
        .map(|snapshot| parse_journal(&journal_path, &snapshot.contents))
        .transpose()?;
    if let Some(journal) = &recovered {
        let current_matches_base = current_manifest == journal.base;
        let current_matches_target = current_manifest.as_ref() == Some(&journal.target);
        if !current_matches_base && !current_matches_target {
            return Err(materialize_error(format!(
                "pending generation journal does not match the current ownership manifest in {}",
                output_dir.display()
            )));
        }
    }

    let planned_paths: BTreeSet<PathBuf> = plan.files.keys().cloned().collect();
    let mut effective_owned = current_manifest.clone().unwrap_or_default();
    if let Some(journal) = &recovered {
        effective_owned.extend(journal.owned.iter().cloned());
    }
    let mut owned_during_transaction = effective_owned.clone();
    owned_during_transaction.extend(planned_paths.iter().cloned());
    owned_during_transaction.extend(plan.removals.iter().cloned());
    for path in &owned_during_transaction {
        if let Some(conflict) = owned_during_transaction
            .iter()
            .find(|other| *other != path && paths_overlap(other, path))
        {
            return Err(materialize_error(format!(
                "unsupported generated file/directory layout transition between {} and {}",
                path.display(),
                conflict.display()
            )));
        }
    }

    let mut stale_paths: BTreeSet<PathBuf> = effective_owned
        .difference(&planned_paths)
        .cloned()
        .collect();
    stale_paths.extend(plan.removals.iter().cloned());
    let mut paths_to_snapshot = owned_during_transaction.clone();
    paths_to_snapshot.extend(stale_paths.iter().cloned());
    let mut snapshots = BTreeMap::new();
    for path in &paths_to_snapshot {
        let snapshot = inspect_relative_file(output_dir, path)?;
        let collision =
            snapshot.is_some() && !effective_owned.contains(path) && !plan.reclaimed.contains(path);
        if collision
            && !(bootstrap == BootstrapPolicy::AdoptExistingPlannedPaths
                && current_manifest.is_none()
                && recovered.is_none())
        {
            return Err(materialize_error(format!(
                "generated path collides with an unmanaged file: {}",
                output_dir.join(path).display()
            )));
        }
        snapshots.insert(path.clone(), snapshot);
    }

    let new_manifest = manifest_contents(&planned_paths)?;
    let new_journal = journal_contents(
        current_manifest.as_ref(),
        &planned_paths,
        &owned_during_transaction,
    )?;
    persist_file(
        &journal_path,
        &new_journal,
        journal_snapshot
            .as_ref()
            .map(|snapshot| snapshot.permissions.clone()),
    )?;

    let mut applied = Vec::new();
    let mut created_directories = Vec::new();
    let result = (|| {
        for (path, planned) in &plan.files {
            let original = snapshots
                .get(path)
                .expect("every planned path was snapshotted")
                .clone();
            require_file_state(output_dir, path, &original)?;
            if original
                .as_ref()
                .is_some_and(|snapshot| snapshot.contents == planned.contents)
            {
                continue;
            }
            failure_hook.before_operation(path)?;
            apply_write(
                output_dir,
                path,
                &planned.contents,
                planned.permissions.clone(),
                original,
                &mut created_directories,
                &mut applied,
                &mut failure_hook,
            )?;
        }
        for path in &stale_paths {
            let original = snapshots
                .get(path)
                .expect("every stale path was snapshotted")
                .clone();
            let Some(original) = original else {
                continue;
            };
            failure_hook.before_operation(path)?;
            apply_delete(output_dir, path, original, &mut applied, &mut failure_hook)?;
        }
        require_file_state(output_dir, manifest_relative, &manifest_snapshot)?;
        if manifest_snapshot
            .as_ref()
            .is_none_or(|snapshot| snapshot.contents != new_manifest)
        {
            failure_hook.before_operation(manifest_relative)?;
            apply_write(
                output_dir,
                manifest_relative,
                &new_manifest,
                manifest_snapshot
                    .as_ref()
                    .map(|snapshot| snapshot.permissions.clone()),
                manifest_snapshot,
                &mut created_directories,
                &mut applied,
                &mut failure_hook,
            )?;
        }
        Ok(())
    })();
    match result {
        Ok(()) => Ok(RenderPublication {
            output_dir: output_dir.to_path_buf(),
            applied,
            created_directories,
            journal_original: journal_snapshot,
            finalized: false,
        }),
        Err(error) => Err(rollback_after_failure(
            output_dir,
            &applied,
            &created_directories,
            journal_snapshot.as_ref(),
            error,
        )),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn write(path: &Path, contents: &str) {
        std::fs::create_dir_all(path.parent().unwrap()).unwrap();
        std::fs::write(path, contents).unwrap();
    }

    fn publish(plan: &RenderPlan, output: &Path) {
        plan.publish_with_bootstrap(output, BootstrapPolicy::AdoptExistingPlannedPaths)
            .unwrap()
            .commit()
            .unwrap();
    }

    fn tree_snapshot(root: &Path) -> BTreeMap<PathBuf, Vec<u8>> {
        fn walk(root: &Path, directory: &Path, snapshot: &mut BTreeMap<PathBuf, Vec<u8>>) {
            let mut entries = std::fs::read_dir(directory)
                .unwrap()
                .collect::<Result<Vec<_>, _>>()
                .unwrap();
            entries.sort_by_key(|entry| entry.file_name());
            for entry in entries {
                let path = entry.path();
                if path.is_dir() {
                    walk(root, &path, snapshot);
                } else {
                    snapshot.insert(
                        path.strip_prefix(root).unwrap().to_path_buf(),
                        std::fs::read(path).unwrap(),
                    );
                }
            }
        }
        let mut snapshot = BTreeMap::new();
        walk(root, root, &mut snapshot);
        snapshot
    }

    #[test]
    fn plan_rejects_unsafe_reserved_duplicate_and_overlapping_paths() {
        let mut plan = RenderPlan::new();
        for path in [
            "",
            "/absolute",
            "../escape",
            "a/../escape",
            "./relative",
            "a//b",
            ".lake/cache",
            "Drivers/Test.lean",
            "Proofs/Proof.lean",
            "Correctness/Proof.lean",
            OWNED_MANIFEST_FILE,
            PENDING_JOURNAL_FILE,
        ] {
            assert!(plan.insert(path, b"x".to_vec()).is_err(), "accepted {path}");
        }
        plan.insert("Pkg/Module.lean", b"x".to_vec()).unwrap();
        assert!(plan.insert("Pkg/Module.lean", b"x".to_vec()).is_err());
        assert!(plan.remove("Pkg/Module.lean").is_err());
        assert!(plan.insert("Pkg", b"x".to_vec()).is_err());
    }

    #[cfg(unix)]
    #[test]
    fn staging_rejects_symlinks_and_carries_permissions() {
        use std::os::unix::fs::{symlink, PermissionsExt as _};

        let temp = tempfile::tempdir().unwrap();
        let staging = temp.path().join("staging");
        let output = temp.path().join("output");
        std::fs::create_dir(&staging).unwrap();
        std::fs::create_dir(&output).unwrap();
        write(&output.join("control.txt"), "control");
        write(&staging.join("real.lean"), "def real := 1\n");
        symlink(staging.join("real.lean"), staging.join("linked.lean")).unwrap();
        assert!(RenderPlan::from_staging_tree(&staging).is_err());
        std::fs::remove_file(staging.join("linked.lean")).unwrap();
        std::fs::set_permissions(
            staging.join("real.lean"),
            std::fs::Permissions::from_mode(0o600),
        )
        .unwrap();
        let mut plan = RenderPlan::from_staging_tree(&staging).unwrap();
        plan.insert("sidecar.toml", b"value = true\n".to_vec())
            .unwrap();
        publish(&plan, &output);
        assert_eq!(
            std::fs::metadata(output.join("real.lean"))
                .unwrap()
                .permissions()
                .mode()
                & 0o777,
            0o600
        );
        assert_eq!(
            std::fs::metadata(output.join("sidecar.toml"))
                .unwrap()
                .permissions()
                .mode()
                & 0o777,
            std::fs::metadata(output.join("control.txt"))
                .unwrap()
                .permissions()
                .mode()
                & 0o777
        );
    }

    #[test]
    fn staging_ignores_preserved_runtime_directories() {
        let temp = tempfile::tempdir().unwrap();
        let staging = temp.path().join("staging");
        std::fs::create_dir_all(staging.join(".lake/build/lib")).unwrap();
        write(&staging.join(".lake/build/lib/cache.olean"), "cache");
        write(&staging.join("Pkg/Module.lean"), "def value := 1\n");

        let plan = RenderPlan::from_staging_tree(&staging).unwrap();

        assert_eq!(plan.files.len(), 1);
        assert!(plan.files.contains_key(Path::new("Pkg/Module.lean")));
    }

    #[test]
    fn strict_bootstrap_refuses_existing_collision_and_adoption_is_explicit() {
        let temp = tempfile::tempdir().unwrap();
        let output = temp.path().join("output");
        std::fs::create_dir(&output).unwrap();
        write(&output.join("Pkg/Module.lean"), "old");
        let before = tree_snapshot(&output);
        let mut plan = RenderPlan::new();
        plan.insert("Pkg/Module.lean", b"new".to_vec()).unwrap();

        assert!(plan.publish(&output).is_err());
        assert_eq!(tree_snapshot(&output), before);
        publish(&plan, &output);
        assert_eq!(
            std::fs::read(output.join("Pkg/Module.lean")).unwrap(),
            b"new"
        );
    }

    #[test]
    fn publication_preserves_unmanaged_roots_and_rolls_back_until_commit() {
        let temp = tempfile::tempdir().unwrap();
        let output = temp.path().join("output");
        std::fs::create_dir(&output).unwrap();
        write(&output.join(".lake/cache"), "cache");
        write(&output.join("scratch.txt"), "scratch");
        let mut initial = RenderPlan::new();
        initial.insert("old.lean", b"old".to_vec()).unwrap();
        publish(&initial, &output);
        let before = tree_snapshot(&output);

        let mut next = RenderPlan::new();
        next.insert("new.lean", b"new".to_vec()).unwrap();
        let publication = next.publish(&output).unwrap();
        assert!(!output.join("old.lean").exists());
        drop(publication);
        assert_eq!(tree_snapshot(&output), before);

        next.publish(&output).unwrap().commit().unwrap();
        assert_eq!(std::fs::read(output.join(".lake/cache")).unwrap(), b"cache");
        assert_eq!(
            std::fs::read(output.join("scratch.txt")).unwrap(),
            b"scratch"
        );
        assert!(output.join("new.lean").is_file());
    }

    #[test]
    fn every_injected_failure_restores_files_and_journal() {
        for operation in 1..=4 {
            let temp = tempfile::tempdir().unwrap();
            let output = temp.path().join("output");
            std::fs::create_dir(&output).unwrap();
            let mut initial = RenderPlan::new();
            initial.insert("replace.lean", b"old".to_vec()).unwrap();
            initial.insert("delete.lean", b"delete".to_vec()).unwrap();
            publish(&initial, &output);
            let before = tree_snapshot(&output);
            let mut next = RenderPlan::new();
            next.insert("replace.lean", b"new".to_vec()).unwrap();
            next.insert("add.lean", b"add".to_vec()).unwrap();
            let error = next
                .publish_failing_at(&output, BootstrapPolicy::RefuseExisting, operation)
                .err()
                .expect("injected operation must fail");
            assert!(matches!(error, RenderError::Io { .. }));
            assert_eq!(tree_snapshot(&output), before, "operation {operation}");
        }
    }

    #[test]
    fn every_post_mutation_failure_restores_files_and_journal() {
        for mutation in 1..=4 {
            let temp = tempfile::tempdir().unwrap();
            let output = temp.path().join("output");
            std::fs::create_dir(&output).unwrap();
            let mut initial = RenderPlan::new();
            initial.insert("replace.lean", b"old".to_vec()).unwrap();
            initial.insert("delete.lean", b"delete".to_vec()).unwrap();
            publish(&initial, &output);
            let before = tree_snapshot(&output);
            let mut next = RenderPlan::new();
            next.insert("replace.lean", b"new".to_vec()).unwrap();
            next.insert("add.lean", b"add".to_vec()).unwrap();

            let error = next
                .publish_failing_after_mutation_at(
                    &output,
                    BootstrapPolicy::RefuseExisting,
                    mutation,
                )
                .err()
                .expect("injected post-mutation operation must fail");

            assert!(matches!(error, RenderError::Io { .. }));
            assert_eq!(tree_snapshot(&output), before, "mutation {mutation}");
        }
    }

    #[test]
    fn interrupted_publication_recovers_forward_without_collision() {
        let temp = tempfile::tempdir().unwrap();
        let output = temp.path().join("output");
        std::fs::create_dir(&output).unwrap();
        let mut initial = RenderPlan::new();
        initial.insert("old.lean", b"old".to_vec()).unwrap();
        publish(&initial, &output);
        let base = BTreeSet::from([PathBuf::from("old.lean")]);
        let target = BTreeSet::from([PathBuf::from("new.lean")]);
        let owned = BTreeSet::from([PathBuf::from("old.lean"), PathBuf::from("new.lean")]);
        std::fs::write(
            output.join(PENDING_JOURNAL_FILE),
            journal_contents(Some(&base), &target, &owned).unwrap(),
        )
        .unwrap();
        write(&output.join("new.lean"), "partially published");

        let mut recovery = RenderPlan::new();
        recovery.insert("new.lean", b"complete".to_vec()).unwrap();
        recovery.publish(&output).unwrap().commit().unwrap();

        assert!(!output.join("old.lean").exists());
        assert_eq!(std::fs::read(output.join("new.lean")).unwrap(), b"complete");
        assert!(!output.join(PENDING_JOURNAL_FILE).exists());
    }

    #[test]
    fn failed_rollback_retains_journal_and_next_publish_recovers() {
        let temp = tempfile::tempdir().unwrap();
        let output = temp.path().join("output");
        std::fs::create_dir(&output).unwrap();
        let mut initial = RenderPlan::new();
        initial.insert("state.lean", b"old".to_vec()).unwrap();
        publish(&initial, &output);

        let mut next = RenderPlan::new();
        next.insert("state.lean", b"new".to_vec()).unwrap();
        let publication = next.publish(&output).unwrap();
        std::fs::write(output.join("state.lean"), "concurrent change").unwrap();
        assert!(publication.rollback().is_err());
        assert!(output.join(PENDING_JOURNAL_FILE).is_file());

        let mut recovery = RenderPlan::new();
        recovery
            .insert("state.lean", b"recovered".to_vec())
            .unwrap();
        recovery.publish(&output).unwrap().commit().unwrap();
        assert_eq!(
            std::fs::read(output.join("state.lean")).unwrap(),
            b"recovered"
        );
        assert!(!output.join(PENDING_JOURNAL_FILE).exists());
    }

    #[test]
    fn corrupt_journal_and_unsupported_manifest_fail_closed() {
        let temp = tempfile::tempdir().unwrap();
        let output = temp.path().join("output");
        std::fs::create_dir(&output).unwrap();
        std::fs::write(output.join(PENDING_JOURNAL_FILE), "not toml = [").unwrap();
        assert!(RenderPlan::new().publish(&output).is_err());
        std::fs::remove_file(output.join(PENDING_JOURNAL_FILE)).unwrap();
        std::fs::write(
            output.join(OWNED_MANIFEST_FILE),
            "version = 999\nfiles = []\n",
        )
        .unwrap();
        assert!(RenderPlan::new().publish(&output).is_err());
    }

    #[test]
    fn explicit_removal_and_empty_plan_clean_owned_files() {
        let temp = tempfile::tempdir().unwrap();
        let output = temp.path().join("output");
        std::fs::create_dir(&output).unwrap();
        write(&output.join("known-sidecar.toml"), "stale");
        let mut tombstone = RenderPlan::new();
        tombstone.remove("known-sidecar.toml").unwrap();
        assert!(tombstone.publish(&output).is_err());
        publish(&tombstone, &output);
        assert!(!output.join("known-sidecar.toml").exists());

        let mut populated = RenderPlan::new();
        populated.insert("owned.lean", b"owned".to_vec()).unwrap();
        populated.publish(&output).unwrap().commit().unwrap();
        RenderPlan::new()
            .publish(&output)
            .unwrap()
            .commit()
            .unwrap();
        assert!(!output.join("owned.lean").exists());
    }

    #[test]
    fn file_directory_layout_transition_fails_with_a_specific_diagnostic() {
        let temp = tempfile::tempdir().unwrap();
        let output = temp.path().join("output");
        std::fs::create_dir(&output).unwrap();
        let mut initial = RenderPlan::new();
        initial.insert("Pkg", b"old file".to_vec()).unwrap();
        publish(&initial, &output);

        let mut next = RenderPlan::new();
        next.insert("Pkg/Module.lean", b"new file".to_vec())
            .unwrap();
        let error = next.publish(&output).err().unwrap();
        assert!(matches!(
            error,
            RenderError::Io { what }
                if what.contains("unsupported generated file/directory layout transition")
        ));
    }

    #[test]
    fn missing_owned_file_cannot_create_an_unrecoverable_layout_journal() {
        let temp = tempfile::tempdir().unwrap();
        let output = temp.path().join("output");
        std::fs::create_dir(&output).unwrap();
        let mut initial = RenderPlan::new();
        initial.insert("Pkg", b"old file".to_vec()).unwrap();
        publish(&initial, &output);
        std::fs::remove_file(output.join("Pkg")).unwrap();

        let mut transition = RenderPlan::new();
        transition
            .insert("Pkg/Module.lean", b"new file".to_vec())
            .unwrap();
        let error = transition.publish(&output).err().unwrap();

        assert!(matches!(
            error,
            RenderError::Io { what }
                if what.contains("unsupported generated file/directory layout transition")
        ));
        assert!(!output.join(PENDING_JOURNAL_FILE).exists());

        let mut recovery = RenderPlan::new();
        recovery.insert("Pkg", b"restored".to_vec()).unwrap();
        recovery.publish(&output).unwrap().commit().unwrap();
        assert_eq!(std::fs::read(output.join("Pkg")).unwrap(), b"restored");
    }
}
