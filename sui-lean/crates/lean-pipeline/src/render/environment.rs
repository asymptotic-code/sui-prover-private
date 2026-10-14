use std::collections::{hash_map::RandomState, BTreeMap, BTreeSet};
use std::hash::{BuildHasher, Hasher};
use std::io::{Read, Write};
use std::path::{Path, PathBuf};
use std::process::{Command, Output, Stdio};
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};

use sha2::{Digest, Sha256};

use super::{RenderError, RenderResult};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum DeclarationKind {
    Missing,
    Definition,
    Abbreviation,
    Opaque,
    Theorem,
    Axiom,
    Other,
}

impl DeclarationKind {
    pub(super) fn as_str(self) -> &'static str {
        match self {
            Self::Missing => "missing",
            Self::Definition => "def",
            Self::Abbreviation => "abbrev",
            Self::Opaque => "opaque",
            Self::Theorem => "theorem",
            Self::Axiom => "axiom",
            Self::Other => "other",
        }
    }

    pub(super) fn is_definition(self) -> bool {
        matches!(self, Self::Definition | Self::Abbreviation | Self::Opaque)
    }

    pub(super) fn is_native_model(self) -> bool {
        self.is_definition() || matches!(self, Self::Theorem | Self::Axiom)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct DeclarationObservation {
    pub(super) kind: DeclarationKind,
    pub(super) declared_in_expected_module: bool,
}

#[derive(Debug, Clone)]
pub(super) struct DeclarationQuery {
    pub(super) name: String,
}

impl DeclarationQuery {
    pub(super) fn untyped(name: impl Into<String>) -> Self {
        Self { name: name.into() }
    }
}

#[derive(Debug, Clone)]
pub(super) struct DeclarationQueryGroup {
    pub(super) module: String,
    pub(super) declarations: Vec<DeclarationQuery>,
}

static NONCE_COUNTER: AtomicU64 = AtomicU64::new(0);

fn query_error(what: impl Into<String>) -> RenderError {
    RenderError::LeanEnvironmentQuery { what: what.into() }
}

fn command_timeout() -> Duration {
    Duration::from_secs(
        std::env::var("FOXY_LAKE_TIMEOUT_SECS")
            .ok()
            .and_then(|value| value.parse().ok())
            .unwrap_or(2400),
    )
}

#[cfg(unix)]
fn kill_process_group(pid: u32) {
    // SAFETY: the child was placed in a new process group whose id is its pid.
    unsafe {
        libc::kill(-(pid as i32), libc::SIGKILL);
    }
}

fn run_bounded_command(
    command: &mut Command,
    stdin: Option<&[u8]>,
    context: &str,
) -> RenderResult<Output> {
    run_command_with_timeout(command, stdin, context, command_timeout())
}

fn run_command_with_timeout(
    command: &mut Command,
    stdin: Option<&[u8]>,
    context: &str,
    timeout: Duration,
) -> RenderResult<Output> {
    enum PipeResult {
        Stdin(Result<(), String>),
        Stdout(Vec<u8>),
        Stderr(Vec<u8>),
    }

    #[cfg(unix)]
    {
        use std::os::unix::process::CommandExt;
        command.process_group(0);
    }
    command.stdout(Stdio::piped()).stderr(Stdio::piped());
    if stdin.is_some() {
        command.stdin(Stdio::piped());
    }
    let mut child = command
        .spawn()
        .map_err(|error| query_error(format!("{context}: {error}")))?;
    let pid = child.id();
    let started = Instant::now();
    let (pipe_sender, pipe_receiver) = std::sync::mpsc::channel();
    let stdin_writer = if let Some(input) = stdin {
        let mut pipe = child
            .stdin
            .take()
            .ok_or_else(|| query_error(format!("{context}: child stdin unavailable")))?;
        let input = input.to_vec();
        let sender = pipe_sender.clone();
        Some(std::thread::spawn(move || {
            let result = pipe.write_all(&input).map_err(|error| error.to_string());
            let _ = sender.send(PipeResult::Stdin(result));
        }))
    } else {
        None
    };
    let mut stdout = child
        .stdout
        .take()
        .ok_or_else(|| query_error(format!("{context}: child stdout unavailable")))?;
    let mut stderr = child
        .stderr
        .take()
        .ok_or_else(|| query_error(format!("{context}: child stderr unavailable")))?;
    let stdout_sender = pipe_sender.clone();
    let stdout_reader = std::thread::spawn(move || {
        let mut bytes = Vec::new();
        let _ = stdout.read_to_end(&mut bytes);
        let _ = stdout_sender.send(PipeResult::Stdout(bytes));
    });
    let stderr_reader = std::thread::spawn(move || {
        let mut bytes = Vec::new();
        let _ = stderr.read_to_end(&mut bytes);
        let _ = pipe_sender.send(PipeResult::Stderr(bytes));
    });
    let status = loop {
        match child.try_wait() {
            Ok(Some(status)) => break status,
            Ok(None) if started.elapsed() < timeout => {
                std::thread::sleep(Duration::from_millis(100));
            }
            Ok(None) => {
                #[cfg(unix)]
                kill_process_group(pid);
                #[cfg(not(unix))]
                let _ = child.kill();
                let _ = child.wait();
                return Err(query_error(format!(
                    "{context}: timed out after {} seconds",
                    timeout.as_secs()
                )));
            }
            Err(error) => {
                #[cfg(unix)]
                kill_process_group(pid);
                #[cfg(not(unix))]
                let _ = child.kill();
                let _ = child.wait();
                return Err(query_error(format!("{context}: poll child: {error}")));
            }
        }
    };
    let mut stdout = None;
    let mut stderr = None;
    let mut stdin_result = stdin.is_none().then_some(Ok(()));
    while stdout.is_none() || stderr.is_none() || stdin_result.is_none() {
        let Some(remaining) = timeout.checked_sub(started.elapsed()) else {
            #[cfg(unix)]
            kill_process_group(pid);
            return Err(query_error(format!(
                "{context}: output pipes remained open after {} seconds",
                timeout.as_secs()
            )));
        };
        match pipe_receiver.recv_timeout(remaining) {
            Ok(PipeResult::Stdin(result)) => stdin_result = Some(result),
            Ok(PipeResult::Stdout(bytes)) => stdout = Some(bytes),
            Ok(PipeResult::Stderr(bytes)) => stderr = Some(bytes),
            Err(std::sync::mpsc::RecvTimeoutError::Timeout) => {
                #[cfg(unix)]
                kill_process_group(pid);
                return Err(query_error(format!(
                    "{context}: output pipes remained open after {} seconds",
                    timeout.as_secs()
                )));
            }
            Err(std::sync::mpsc::RecvTimeoutError::Disconnected) => {
                let _ = stdout_reader.join();
                let _ = stderr_reader.join();
                return Err(query_error(format!(
                    "{context}: output reader disconnected"
                )));
            }
        }
    }
    if let Some(writer) = stdin_writer {
        let _ = writer.join();
    }
    let _ = stdout_reader.join();
    let _ = stderr_reader.join();
    if let Err(error) = stdin_result.unwrap_or(Ok(())) {
        return Err(query_error(format!(
            "{context}: write child stdin: {error}"
        )));
    }
    Ok(Output {
        status,
        stdout: stdout.unwrap_or_default(),
        stderr: stderr.unwrap_or_default(),
    })
}

fn nonce() -> String {
    let counter = NONCE_COUNTER.fetch_add(1, Ordering::Relaxed);
    let nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|duration| duration.as_nanos())
        .unwrap_or(0);
    let mut first = RandomState::new().build_hasher();
    first.write_u32(std::process::id());
    first.write_u64(counter);
    first.write_u128(nanos);
    let mut second = RandomState::new().build_hasher();
    second.write_u64(first.finish());
    second.write_u128(nanos.rotate_left(31));
    format!("LEAN_ENV_{:016x}{:016x}", first.finish(), second.finish())
}

fn lean_string(value: &str) -> String {
    let mut escaped = String::with_capacity(value.len() + 2);
    escaped.push('"');
    for ch in value.chars() {
        match ch {
            '\\' => escaped.push_str("\\\\"),
            '"' => escaped.push_str("\\\""),
            '\n' => escaped.push_str("\\n"),
            '\r' => escaped.push_str("\\r"),
            '\t' => escaped.push_str("\\t"),
            ch if ch.is_control() => escaped.push_str(&format!("\\u{{{:x}}}", ch as u32)),
            ch => escaped.push(ch),
        }
    }
    escaped.push('"');
    escaped
}

fn lean_name_components(name: &str) -> Vec<String> {
    name.split('.')
        .map(|component| component.replace(['«', '»'], ""))
        .collect()
}

fn lean_string_array(name: &str) -> String {
    let components = lean_name_components(name)
        .iter()
        .map(|component| lean_string(component))
        .collect::<Vec<_>>()
        .join(", ");
    format!("#[{components}]")
}

fn build_query_source(
    nonce: &str,
    artifact_dir: &Path,
    groups: &[DeclarationQueryGroup],
) -> String {
    let expected_total: usize = groups.iter().map(|group| group.declarations.len()).sum();
    // The query table below is emitted as ONE array literal with an entry per
    // queried declaration. At full-corpus scale (~600 declarations in a fresh
    // seed) elaborating that literal exceeds Lean's default maxRecDepth (512),
    // which kills `runSuiLeanEnvironmentQuery` at codegen and cascades into a
    // bogus "depends on noncomputable" error on `run_cmd`. Raise the limit up
    // front; the option must come after the import.
    let mut source = String::from(
        "import Lean\nset_option maxRecDepth 100000\n\nunsafe def runSuiLeanEnvironmentQuery : IO Unit := do\n",
    );
    source.push_str(&format!(
        "  Lean.searchPathRef.modify fun paths => paths ++ [System.FilePath.mk {}]\n",
        lean_string(&artifact_dir.to_string_lossy())
    ));
    source.push_str(&format!("  let nonce := {}\n", lean_string(nonce)));
    source.push_str(&format!("  let expectedTotal : Nat := {expected_total}\n"));
    source
        .push_str("  let groups : Array (Nat × Array String × Array (Nat × Array String)) := #[\n");
    for (group_index, group) in groups.iter().enumerate() {
        source.push_str(&format!(
            "    ({group_index}, {}, #[",
            lean_string_array(&group.module)
        ));
        for (declaration_index, declaration) in group.declarations.iter().enumerate() {
            if declaration_index > 0 {
                source.push_str(", ");
            }
            source.push_str(&format!(
                "({declaration_index}, {})",
                lean_string_array(&declaration.name)
            ));
        }
        source.push_str("])");
        if group_index + 1 < groups.len() {
            source.push(',');
        }
        source.push('\n');
    }
    // ONE `withImportModules` over the union of every queried module, not one
    // per group. The per-declaration work below is `env.find?`, a hash lookup;
    // the import is the entire cost. A native-model file imports the corpus
    // module whose types it models, and those OLeans are large (12.3 MB for
    // sui-system's `SuiSystem.Validator_set`, ~1.0 GB of OLeans across the
    // query workspace), while the groups' closures overlap almost entirely --
    // so importing per group deserialized and re-registered the same tens of
    // MB once per module. Measured on sui-system's real artifact directory,
    // 15 model modules: 21.56s per-module vs 3.02s union.
    //
    // Provenance is resolved against the QUERIED MODULE'S OWN `ModuleData`,
    // not `env.getModuleIdxFor?`: a single environment's name map holds only
    // one entry per name, so asking it "who declares this?" cannot answer
    // per-module. Reading the module's own `constNames`/`constants` restores
    // the answer that one-import-per-group used to give, and it supplies the
    // kind from the right declaration too.
    //
    // The union import CARRIES A PRECONDITION that one-per-group did not: the
    // queried modules must not declare the same name twice, because Lean
    // refuses the second import outright (`import Sui.HashNatives failed,
    // environment already contains 'Hash.sha3_256' from
    // MoveStdlib.HashNatives`) and the client's render dies. Rendered user
    // modules are package-qualified by `escape::module_render_namespace`, so
    // the exposure is the hand-written lemma bundle, whose packages share one
    // flat namespace on purpose; `lemma_bundle_declares_no_qualified_name_twice`
    // (stage_02_ir_cfg::natives tests) pins that it stays disjoint. Do NOT
    // relax this by importing per group again -- that hides a real bundle
    // defect behind a 12x slower query.
    //
    // Deviation, deliberate and inert: a name outside the queried module's own
    // import closure but present in another queried module's now reports that
    // declaration's kind instead of "missing". `originOk` is false either way,
    // and both consumers require the kind AND `declared_in_expected_module`,
    // so no model decision changes -- only the `declaration_kind` string in
    // the emitted native-model report.
    source.push_str(
        r#"  ]
  let nameOf := fun (comps : Array String) =>
    comps.foldl (fun name component => Lean.Name.mkStr name component) Lean.Name.anonymous
  let importedModules := (groups.map (fun (_, moduleComps, _) => nameOf moduleComps)).toList.eraseDups.toArray
  Lean.withImportModules (importedModules.map (fun m => { module := m })) {} fun env => do
    let moduleData := env.header.moduleData
    let kindOf := fun (info : Lean.ConstantInfo) =>
      match info with
      | .defnInfo value => if value.hints.isAbbrev then "abbrev" else "def"
      | .opaqueInfo _ => "opaque"
      | .thmInfo _ => "theorem"
      | .axiomInfo _ => "axiom"
      | _ => "other"
    for (groupId, moduleComps, declarations) in groups do
      let moduleName := nameOf moduleComps
      let ownIdx := env.allImportedModuleNames.findIdx? (fun n => n == moduleName)
      for (declarationId, declarationComps) in declarations do
        let declarationName := nameOf declarationComps
        let ownInfo : Option Lean.ConstantInfo :=
          match ownIdx with
          | some i =>
            let md := moduleData[i]!
            match md.constNames.findIdx? (fun n => n == declarationName) with
            | some j => some md.constants[j]!
            | none => none
          | none => none
        let (kind, originOk) := match ownInfo with
          | some info => (kindOf info, true)
          | none =>
            match env.find? declarationName with
            | none => ("missing", false)
            | some info => (kindOf info, false)
        IO.println s!"{nonce}|D|{groupId}|{declarationId}|{kind}|{if originOk then 1 else 0}"
  IO.println s!"{nonce}|END|{groups.size}|{expectedTotal}"

run_cmd runSuiLeanEnvironmentQuery
"#,
    );
    source
}

#[derive(Debug)]
struct SourceTreeSnapshot {
    root: PathBuf,
    files: BTreeMap<PathBuf, [u8; 32]>,
}

impl SourceTreeSnapshot {
    fn capture(root: &Path, context: &str) -> RenderResult<Self> {
        let metadata = std::fs::symlink_metadata(root).map_err(|error| {
            query_error(format!(
                "{context}: inspect source root {}: {error}",
                root.display()
            ))
        })?;
        if metadata.file_type().is_symlink() || !metadata.is_dir() {
            return Err(query_error(format!(
                "{context}: source root must be a non-symlink directory: {}",
                root.display()
            )));
        }
        let root = root.canonicalize().map_err(|error| {
            query_error(format!(
                "{context}: canonicalize source root {}: {error}",
                root.display()
            ))
        })?;
        let mut files = BTreeMap::new();
        let mut pending = vec![root.clone()];
        while let Some(directory) = pending.pop() {
            let mut entries = std::fs::read_dir(&directory)
                .map_err(|error| {
                    query_error(format!(
                        "{context}: read source directory {}: {error}",
                        directory.display()
                    ))
                })?
                .collect::<Result<Vec<_>, _>>()
                .map_err(|error| {
                    query_error(format!(
                        "{context}: read source entry under {}: {error}",
                        directory.display()
                    ))
                })?;
            entries.sort_by_key(|entry| entry.file_name());
            for entry in entries {
                let path = entry.path();
                let relative = path.strip_prefix(&root).expect("entry remains below root");
                if relative.components().any(|component| {
                    component == std::path::Component::Normal(std::ffi::OsStr::new(".lake"))
                }) {
                    continue;
                }
                let metadata = std::fs::symlink_metadata(&path).map_err(|error| {
                    query_error(format!(
                        "{context}: inspect source path {}: {error}",
                        path.display()
                    ))
                })?;
                if metadata.file_type().is_symlink() {
                    return Err(query_error(format!(
                        "{context}: source snapshot refuses symlink {}",
                        path.display()
                    )));
                }
                if metadata.is_dir() {
                    pending.push(path);
                } else if metadata.is_file()
                    && (path.extension().and_then(|ext| ext.to_str()) == Some("lean")
                        || path.file_name().and_then(|name| name.to_str())
                            == Some("lean-toolchain"))
                {
                    let bytes = std::fs::read(&path).map_err(|error| {
                        query_error(format!(
                            "{context}: read source {}: {error}",
                            path.display()
                        ))
                    })?;
                    files.insert(relative.to_path_buf(), Sha256::digest(&bytes).into());
                }
            }
        }
        Ok(Self { root, files })
    }

    fn copy_into(&self, destination: &Path, context: &str) -> RenderResult<()> {
        for (relative, expected_digest) in &self.files {
            let source = self.root.join(relative);
            let bytes = std::fs::read(&source).map_err(|error| {
                query_error(format!(
                    "{context}: read snapshotted source {}: {error}",
                    source.display()
                ))
            })?;
            if &<[u8; 32]>::from(Sha256::digest(&bytes)) != expected_digest {
                return Err(query_error(format!(
                    "{context}: source changed while creating immutable query snapshot: {}",
                    source.display()
                )));
            }
            let target = destination.join(relative);
            if let Some(parent) = target.parent() {
                std::fs::create_dir_all(parent).map_err(|error| {
                    query_error(format!(
                        "{context}: create snapshot directory {}: {error}",
                        parent.display()
                    ))
                })?;
            }
            if target.exists() {
                let existing = std::fs::read(&target).map_err(|error| {
                    query_error(format!(
                        "{context}: read colliding snapshot source {}: {error}",
                        target.display()
                    ))
                })?;
                if existing != bytes {
                    return Err(query_error(format!(
                        "{context}: source roots disagree on module path {}",
                        relative.display()
                    )));
                }
            } else {
                std::fs::write(&target, bytes).map_err(|error| {
                    query_error(format!(
                        "{context}: write immutable source snapshot {}: {error}",
                        target.display()
                    ))
                })?;
            }
        }
        Ok(())
    }

    fn verify_unchanged(&self, context: &str) -> RenderResult<()> {
        let current = Self::capture(&self.root, context)?;
        if current.files == self.files {
            Ok(())
        } else {
            Err(query_error(format!(
                "{context}: source tree changed while its immutable snapshot was queried: {}",
                self.root.display()
            )))
        }
    }

    fn cache_key(&self) -> String {
        let mut hasher = Sha256::new();
        for (relative, digest) in &self.files {
            hasher.update(relative.to_string_lossy().replace('\\', "/").as_bytes());
            hasher.update([0]);
            hasher.update(digest);
        }
        hasher.finalize()[..12]
            .iter()
            .map(|byte| format!("{byte:02x}"))
            .collect()
    }
}

struct QueryProjectSnapshot {
    _temp: tempfile::TempDir,
    project_dir: PathBuf,
    source: SourceTreeSnapshot,
    query_sources: SourceTreeSnapshot,
}

impl QueryProjectSnapshot {
    fn create(
        project_dir: &Path,
        workspace_dir: Option<&Path>,
        context: &str,
    ) -> RenderResult<Self> {
        let source = SourceTreeSnapshot::capture(project_dir, context)?;
        let project_root = source.root.clone();
        let temp = match workspace_dir {
            Some(workspace_dir) => tempfile::Builder::new()
                .prefix("query-")
                .tempdir_in(workspace_dir),
            None => tempfile::tempdir(),
        }
        .map_err(|error| {
            query_error(format!(
                "{context}: create immutable query project: {error}"
            ))
        })?;
        let mut temp = temp;
        if std::env::var_os("SUI_LEAN_KEEP_QUERY_WORKSPACE").is_some() {
            // Debugging aid: keep the generated query project (the rendered
            // `.lean` files Lean rejected) instead of deleting it on drop.
            temp.disable_cleanup(true);
            eprintln!(
                "sui-lean: keeping query workspace {}",
                temp.path().display()
            );
        }
        let destination = mirrored_source_root(temp.path(), &source.root, context)?;
        source.copy_into(&destination, context)?;
        let project_dir = mirrored_source_root(temp.path(), &project_root, context)?;
        let lakefile = project_dir.join("lakefile.lean");
        if !lakefile.is_file() {
            return Err(query_error(format!(
                "{context}: immutable query project has no lakefile.lean: {}",
                lakefile.display()
            )));
        }
        let query_sources = SourceTreeSnapshot::capture(temp.path(), context)?;
        Ok(Self {
            project_dir,
            _temp: temp,
            source,
            query_sources,
        })
    }

    fn verify_sources_unchanged(&self, context: &str) -> RenderResult<()> {
        self.query_sources.verify_unchanged(context)?;
        self.source.verify_unchanged(context)
    }
}

fn mirrored_source_root(temp: &Path, root: &Path, context: &str) -> RenderResult<PathBuf> {
    // Preserving every absolute path component makes the immutable workspace
    // exceed Win32's effective path budget once Lake appends
    // `.lake/config/0/lakefile.olean.trace`.  The snapshot only requires a
    // collision-free root, not the original hierarchy, so use a digest there.
    #[cfg(windows)]
    {
        let digest = Sha256::digest(root.to_string_lossy().as_bytes());
        let label = digest[..12]
            .iter()
            .map(|byte| format!("{byte:02x}"))
            .collect::<String>();
        let _ = context;
        return Ok(temp.join("filesystem").join(format!("root-{label}")));
    }
    #[cfg(not(windows))]
    let mut destination = temp.join("filesystem");
    #[cfg(not(windows))]
    for component in root.components() {
        match component {
            std::path::Component::Prefix(prefix) => {
                let digest = Sha256::digest(prefix.as_os_str().to_string_lossy().as_bytes());
                let label = digest[..8]
                    .iter()
                    .map(|byte| format!("{byte:02x}"))
                    .collect::<String>();
                destination.push(format!("prefix-{label}"));
            }
            std::path::Component::RootDir | std::path::Component::CurDir => {}
            std::path::Component::Normal(component) => destination.push(component),
            std::path::Component::ParentDir => {
                return Err(query_error(format!(
                    "{context}: canonical source root contains a parent component: {}",
                    root.display()
                )));
            }
        }
    }
    #[cfg(not(windows))]
    Ok(destination)
}

struct LeanToolchain {
    directory: PathBuf,
    lake_executable: PathBuf,
    lean_executable: PathBuf,
    library_dir: PathBuf,
}

fn resolve_toolchain(project_dir: &Path, context: &str) -> RenderResult<LeanToolchain> {
    let mut prefix_command = Command::new("lake");
    prefix_command
        .args(["env", "lean", "--print-prefix"])
        .current_dir(project_dir);
    let prefix_output = run_bounded_command(
        &mut prefix_command,
        None,
        &format!("{context}: resolve Lean toolchain"),
    )?;
    if !prefix_output.status.success() {
        return Err(query_error(format!(
            "{context}: resolve Lean toolchain failed with {}:\n{}\n{}",
            prefix_output.status,
            String::from_utf8_lossy(&prefix_output.stdout),
            String::from_utf8_lossy(&prefix_output.stderr)
        )));
    }
    let prefix_stdout = String::from_utf8(prefix_output.stdout).map_err(|error| {
        query_error(format!(
            "{context}: Lean toolchain prefix was not UTF-8: {error}"
        ))
    })?;
    let prefix_lines: Vec<_> = prefix_stdout
        .lines()
        .map(str::trim)
        .filter(|line| !line.is_empty())
        .collect();
    if prefix_lines.len() != 1 {
        return Err(query_error(format!(
            "{context}: Lean toolchain query returned {} non-empty lines",
            prefix_lines.len()
        )));
    }
    let toolchain_dir = PathBuf::from(prefix_lines[0])
        .canonicalize()
        .map_err(|error| query_error(format!("{context}: canonicalize toolchain: {error}")))?;
    let executable = |name: &str| {
        #[cfg(windows)]
        let name = format!("{name}.exe");
        toolchain_dir
            .join("bin")
            .join(&name)
            .canonicalize()
            .map_err(|error| {
                query_error(format!(
                    "{context}: locate trusted `{name}` under toolchain: {error}"
                ))
            })
    };
    let library_dir = toolchain_dir
        .join("lib/lean")
        .canonicalize()
        .map_err(|error| {
            query_error(format!(
                "{context}: locate trusted Lean library under toolchain: {error}"
            ))
        })?;
    Ok(LeanToolchain {
        directory: toolchain_dir.clone(),
        lake_executable: executable("lake")?,
        lean_executable: executable("lean")?,
        library_dir,
    })
}

#[derive(Debug)]
struct QueryCacheLayout {
    root_dir: PathBuf,
    lake_cache_dir: PathBuf,
    workspace_dir: PathBuf,
}

impl QueryCacheLayout {
    fn configured(toolchain: &LeanToolchain, context: &str) -> RenderResult<Option<Self>> {
        let (base, explicit) = match std::env::var_os("SUI_LEAN_QUERY_CACHE_DIR") {
            Some(value) if value.is_empty() => return Ok(None),
            Some(value) => {
                let path = PathBuf::from(value);
                if !path.is_absolute() {
                    return Err(query_error(format!(
                        "{context}: SUI_LEAN_QUERY_CACHE_DIR must be absolute: {}",
                        path.display()
                    )));
                }
                (path, true)
            }
            None => {
                let base = std::env::var_os("XDG_CACHE_HOME")
                    .filter(|value| !value.is_empty())
                    .map(PathBuf::from)
                    .filter(|path| path.is_absolute())
                    .or_else(|| {
                        std::env::var_os("HOME")
                            .filter(|value| !value.is_empty())
                            .map(PathBuf::from)
                            .filter(|path| path.is_absolute())
                            .map(|path| path.join(".cache"))
                    })
                    .or_else(|| {
                        std::env::var_os("USERPROFILE")
                            .filter(|value| !value.is_empty())
                            .map(PathBuf::from)
                            .filter(|path| path.is_absolute())
                            .map(|path| path.join(".cache"))
                    });
                let Some(base) = base else {
                    return Ok(None);
                };
                (base, false)
            }
        };
        match Self::at_base(&base, toolchain, context) {
            Ok(cache) => Ok(Some(cache)),
            Err(error) if !explicit => {
                eprintln!(
                    "warning: {context}: persistent Lean query cache unavailable; \
                     falling back to cold isolated builds: {error:?}"
                );
                Ok(None)
            }
            Err(error) => Err(error),
        }
    }

    fn at_base(base: &Path, toolchain: &LeanToolchain, context: &str) -> RenderResult<Self> {
        std::fs::create_dir_all(base).map_err(|error| {
            query_error(format!(
                "{context}: create Lean query cache base {}: {error}",
                base.display()
            ))
        })?;
        let metadata = std::fs::metadata(base).map_err(|error| {
            query_error(format!(
                "{context}: inspect Lean query cache base {}: {error}",
                base.display()
            ))
        })?;
        if !metadata.is_dir() {
            return Err(query_error(format!(
                "{context}: Lean query cache base must be a directory: {}",
                base.display()
            )));
        }
        let base = base.canonicalize().map_err(|error| {
            query_error(format!(
                "{context}: canonicalize Lean query cache base {}: {error}",
                base.display()
            ))
        })?;
        let root = create_private_cache_directory(
            &base.join("sui-lean").join("environment-query"),
            context,
        )?;
        let schema_dir = create_private_cache_directory(&root.join("v1"), context)?;
        let mut hasher = Sha256::new();
        #[cfg(unix)]
        {
            use std::os::unix::ffi::OsStrExt;
            hasher.update(toolchain.directory.as_os_str().as_bytes());
        }
        #[cfg(not(unix))]
        hasher.update(toolchain.directory.to_string_lossy().as_bytes());
        let digest = hasher.finalize();
        let toolchain_key = digest[..12]
            .iter()
            .map(|byte| format!("{byte:02x}"))
            .collect::<String>();
        let toolchain_dir =
            create_private_cache_directory(&schema_dir.join(toolchain_key), context)?;
        Ok(Self {
            root_dir: toolchain_dir.clone(),
            lake_cache_dir: create_private_cache_directory(
                &toolchain_dir.join("artifacts"),
                context,
            )?,
            workspace_dir: create_private_cache_directory(
                &toolchain_dir.join("workspaces"),
                context,
            )?,
        })
    }

    fn overlaps(&self, source: &Path) -> bool {
        self.root_dir.starts_with(source) || source.starts_with(&self.root_dir)
    }
}

fn create_private_cache_directory(path: &Path, context: &str) -> RenderResult<PathBuf> {
    std::fs::create_dir_all(path).map_err(|error| {
        query_error(format!(
            "{context}: create Lean query cache directory {}: {error}",
            path.display()
        ))
    })?;
    let metadata = std::fs::symlink_metadata(path).map_err(|error| {
        query_error(format!(
            "{context}: inspect Lean query cache directory {}: {error}",
            path.display()
        ))
    })?;
    if metadata.file_type().is_symlink() || !metadata.is_dir() {
        return Err(query_error(format!(
            "{context}: Lean query cache path must be a non-symlink directory: {}",
            path.display()
        )));
    }
    #[cfg(unix)]
    {
        use std::os::unix::fs::{MetadataExt, PermissionsExt};
        // SAFETY: `geteuid` has no preconditions.
        if metadata.uid() != unsafe { libc::geteuid() } {
            return Err(query_error(format!(
                "{context}: Lean query cache directory is not owned by the current user: {}",
                path.display()
            )));
        }
        std::fs::set_permissions(path, std::fs::Permissions::from_mode(0o700)).map_err(
            |error| {
                query_error(format!(
                    "{context}: secure Lean query cache directory {}: {error}",
                    path.display()
                ))
            },
        )?;
    }
    path.canonicalize().map_err(|error| {
        query_error(format!(
            "{context}: canonicalize Lean query cache directory {}: {error}",
            path.display()
        ))
    })
}

fn prepare_modules(
    project_dir: &Path,
    groups: &[DeclarationQueryGroup],
    toolchain: &LeanToolchain,
    cache: Option<&QueryCacheLayout>,
    context: &str,
) -> RenderResult<PathBuf> {
    let modules: BTreeSet<&str> = groups.iter().map(|group| group.module.as_str()).collect();
    if modules.is_empty() {
        return Err(query_error(format!("{context}: no modules to query")));
    }
    // Lake 5.0 on Windows can attempt to create a configuration trace under
    // `.lake/config/0/` before creating that numeric parent itself.  The same
    // command creates it on Unix.  Pre-creating the private snapshot-local
    // directory is harmless and prevents the Windows `ENOENT` race.
    #[cfg(windows)]
    std::fs::create_dir_all(project_dir.join(".lake/config/0")).map_err(|error| {
        query_error(format!(
            "{context}: create Windows Lake configuration directory: {error}"
        ))
    })?;
    let mut command = Command::new(&toolchain.lake_executable);
    // The snapshot is freshly materialized and has no stale build graph. On
    // Windows `--rehash` removes `.lake/config/0` and Lake 5.0 races its own
    // recreation before opening `lakefile.olean.trace`; omit the redundant
    // rehash there. Unix keeps the stronger explicit refresh.
    #[cfg(not(windows))]
    command.arg("--rehash");
    // A fresh Windows snapshot has no reusable configuration OLean. Asking
    // Lake to elaborate it explicitly avoids its broken attempt to consume a
    // not-yet-created `.lake/config/0/lakefile.olean.trace`.
    #[cfg(windows)]
    command.arg("--reconfigure");
    command.args(["--no-cache", "build"]);
    for module in &modules {
        command.arg(format!("+{module}"));
    }
    command
        .current_dir(project_dir)
        .env_remove("LEAN_PATH")
        .env_remove("LEAN_SRC_PATH")
        .env_remove("LEAN_GITHASH")
        .env_remove("LAKE_CACHE_KEY")
        .env_remove("LAKE_CACHE_ARTIFACT_ENDPOINT")
        .env_remove("LAKE_CACHE_REVISION_ENDPOINT")
        .env_remove("LAKE_CACHE_SERVICE");
    // Lake's Windows artifact cache can report a successful restore while
    // omitting module `.olean` files for ephemeral query projects. The query
    // workspace remains isolated/persistent; only unsafe artifact restoration
    // is disabled on Windows.
    #[cfg(not(windows))]
    if let Some(cache) = cache {
        command
            .env("LAKE_CACHE_DIR", &cache.lake_cache_dir)
            .env("LAKE_ARTIFACT_CACHE", "true")
            .env("LAKE_RESTORE_ARTIFACTS", "true");
    }
    #[cfg(not(windows))]
    if cache.is_none() {
        command
            .env("LAKE_CACHE_DIR", "")
            .env("LAKE_ARTIFACT_CACHE", "false")
            .env("LAKE_RESTORE_ARTIFACTS", "false");
    }
    #[cfg(windows)]
    {
        let _ = cache;
        command
            .env("LAKE_CACHE_DIR", "")
            .env("LAKE_ARTIFACT_CACHE", "false")
            .env("LAKE_RESTORE_ARTIFACTS", "false");
    }
    let output = run_bounded_command(
        &mut command,
        None,
        &format!("{context}: execute `lake build`"),
    )?;
    if !output.status.success() {
        return Err(query_error(format!(
            "{context}: module build failed with {}:\n{}\n{}",
            output.status,
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        )));
    }
    let artifact_dir = project_dir
        .join(".lake/build/lib/lean")
        .canonicalize()
        .map_err(|error| {
            query_error(format!(
                "{context}: locate Lake artifact directory after build: {error}"
            ))
        })?;
    for module in modules {
        let mut builtin = toolchain.library_dir.clone();
        for component in lean_name_components(module) {
            builtin.push(component);
        }
        builtin.set_extension("olean");
        if builtin.exists() {
            return Err(query_error(format!(
                "{context}: refusing to query project module `{module}` because it collides with trusted toolchain module {}",
                builtin.display()
            )));
        }
    }
    Ok(artifact_dir)
}

fn parse_query_output(
    nonce: &str,
    groups: &[DeclarationQueryGroup],
    stdout: &str,
    context: &str,
) -> RenderResult<Vec<Vec<DeclarationObservation>>> {
    let prefix = format!("{nonce}|");
    let expected_total: usize = groups.iter().map(|group| group.declarations.len()).sum();
    let mut rows = BTreeMap::new();
    let mut end = None;
    for line in stdout.lines() {
        let Some(payload) = line.strip_prefix(&prefix) else {
            continue;
        };
        if let Some(payload) = payload.strip_prefix("D|") {
            let fields: Vec<&str> = payload.split('|').collect();
            if fields.len() != 4 {
                return Err(query_error(format!(
                    "{context}: malformed declaration row `{line}`"
                )));
            }
            let group_index: usize = fields[0]
                .parse()
                .map_err(|_| query_error(format!("{context}: invalid group index in `{line}`")))?;
            let declaration_index: usize = fields[1].parse().map_err(|_| {
                query_error(format!("{context}: invalid declaration index in `{line}`"))
            })?;
            if group_index >= groups.len()
                || declaration_index >= groups[group_index].declarations.len()
            {
                return Err(query_error(format!("{context}: out-of-range row `{line}`")));
            }
            let kind = match fields[2] {
                "missing" => DeclarationKind::Missing,
                "def" => DeclarationKind::Definition,
                "abbrev" => DeclarationKind::Abbreviation,
                "opaque" => DeclarationKind::Opaque,
                "theorem" => DeclarationKind::Theorem,
                "axiom" => DeclarationKind::Axiom,
                "other" => DeclarationKind::Other,
                other => {
                    return Err(query_error(format!(
                        "{context}: unknown declaration kind `{other}`"
                    )));
                }
            };
            let declared_in_expected_module = match fields[3] {
                "0" => false,
                "1" => true,
                other => {
                    return Err(query_error(format!(
                        "{context}: invalid origin flag `{other}`"
                    )));
                }
            };
            if rows
                .insert(
                    (group_index, declaration_index),
                    DeclarationObservation {
                        kind,
                        declared_in_expected_module,
                    },
                )
                .is_some()
            {
                return Err(query_error(format!("{context}: duplicate row `{line}`")));
            }
        } else if let Some(payload) = payload.strip_prefix("END|") {
            let fields: Vec<&str> = payload.split('|').collect();
            if fields.len() != 2 || end.is_some() {
                return Err(query_error(format!(
                    "{context}: malformed or duplicate END row"
                )));
            }
            let group_count: usize = fields[0]
                .parse()
                .map_err(|_| query_error(format!("{context}: invalid END group count")))?;
            let row_count: usize = fields[1]
                .parse()
                .map_err(|_| query_error(format!("{context}: invalid END row count")))?;
            end = Some((group_count, row_count));
        } else {
            return Err(query_error(format!(
                "{context}: unknown protocol row `{line}`"
            )));
        }
    }
    if end != Some((groups.len(), expected_total)) {
        return Err(query_error(format!(
            "{context}: missing or incorrect completion sentinel"
        )));
    }
    if rows.len() != expected_total {
        return Err(query_error(format!(
            "{context}: received {} declaration rows, expected {expected_total}",
            rows.len()
        )));
    }
    let mut result = Vec::with_capacity(groups.len());
    for (group_index, group) in groups.iter().enumerate() {
        let mut observations = Vec::with_capacity(group.declarations.len());
        for declaration_index in 0..group.declarations.len() {
            observations.push(
                rows.remove(&(group_index, declaration_index))
                    .ok_or_else(|| {
                        query_error(format!(
                            "{context}: missing row {group_index}/{declaration_index}"
                        ))
                    })?,
            );
        }
        result.push(observations);
    }
    Ok(result)
}

pub(super) fn query_declarations(
    project_dir: &Path,
    groups: &[DeclarationQueryGroup],
    context: &str,
) -> RenderResult<Vec<Vec<DeclarationObservation>>> {
    if groups.is_empty() {
        return Ok(Vec::new());
    }
    let total_started = Instant::now();
    let setup_started = Instant::now();
    let toolchain = resolve_toolchain(project_dir, context)?;
    let mut cache = QueryCacheLayout::configured(&toolchain, context)?;
    if let Some(active_cache) = cache.as_ref() {
        let source = project_dir.canonicalize().map_err(|error| {
            query_error(format!(
                "{context}: canonicalize source root {}: {error}",
                project_dir.display()
            ))
        })?;
        if active_cache.overlaps(&source) {
            eprintln!(
                "warning: {context}: Lean query cache overlaps source root {}; \
                 falling back to cold isolated builds",
                source.display()
            );
            cache = None;
        }
    }
    let setup_elapsed = setup_started.elapsed();
    let snapshot_started = Instant::now();
    let snapshot = QueryProjectSnapshot::create(
        project_dir,
        cache.as_ref().map(|cache| cache.workspace_dir.as_path()),
        context,
    )?;
    // Lake's artifact cache keys do not distinguish unrelated temporary
    // projects that reuse the same package/module names. Keep persistent
    // reuse, but scope it to the immutable source snapshot so one query can
    // never restore another query's `.olean` files.
    let build_cache = match cache.as_ref() {
        Some(cache) => Some(QueryCacheLayout {
            root_dir: cache.root_dir.clone(),
            lake_cache_dir: create_private_cache_directory(
                &cache.lake_cache_dir.join(snapshot.source.cache_key()),
                context,
            )?,
            workspace_dir: cache.workspace_dir.clone(),
        }),
        None => None,
    };
    let snapshot_elapsed = snapshot_started.elapsed();
    let module_count = groups
        .iter()
        .map(|group| group.module.as_str())
        .collect::<BTreeSet<_>>()
        .len();
    let declaration_count: usize = groups.iter().map(|group| group.declarations.len()).sum();
    let build_started = Instant::now();
    let artifact_dir = match prepare_modules(
        &snapshot.project_dir,
        groups,
        &toolchain,
        build_cache.as_ref(),
        context,
    ) {
        Ok(artifact_dir) => artifact_dir,
        Err(error) => {
            eprintln!(
                "[timing] Lean environment query `{context}` failed during lake_build after {}ms \
                 (setup={}ms snapshot={}ms lake_build={}ms; \
                 modules={} declarations={} cache={})",
                total_started.elapsed().as_millis(),
                setup_elapsed.as_millis(),
                snapshot_elapsed.as_millis(),
                build_started.elapsed().as_millis(),
                module_count,
                declaration_count,
                if cache.is_some() {
                    "persistent"
                } else {
                    "disabled"
                },
            );
            return Err(error);
        }
    };
    let build_elapsed = build_started.elapsed();
    let nonce = nonce();
    let source = build_query_source(&nonce, &artifact_dir, groups);
    let query_dir = tempfile::tempdir().map_err(|error| {
        query_error(format!(
            "{context}: create isolated query directory: {error}"
        ))
    })?;
    let query_started = Instant::now();
    let mut command = Command::new(&toolchain.lean_executable);
    command
        .arg("--stdin")
        .current_dir(query_dir.path())
        .env_remove("LEAN_PATH")
        .env_remove("LEAN_SRC_PATH");
    let output = run_bounded_command(
        &mut command,
        Some(source.as_bytes()),
        &format!("{context}: execute isolated Lean query"),
    )?;
    let query_elapsed = query_started.elapsed();
    let verification_started = Instant::now();
    snapshot.verify_sources_unchanged(context)?;
    let verification_elapsed = verification_started.elapsed();
    let stdout = String::from_utf8_lossy(&output.stdout).to_string();
    if !output.status.success() {
        return Err(query_error(format!(
            "{context}: Lean environment query failed with {}:\n{}\n{}",
            output.status,
            stdout,
            String::from_utf8_lossy(&output.stderr)
        )));
    }
    let observations = parse_query_output(&nonce, groups, &stdout, context)?;
    eprintln!(
        "[timing] Lean environment query `{context}` took: {}ms \
         (setup={}ms snapshot={}ms lake_build={}ms query={}ms verify={}ms; \
         modules={} declarations={} cache={})",
        total_started.elapsed().as_millis(),
        setup_elapsed.as_millis(),
        snapshot_elapsed.as_millis(),
        build_elapsed.as_millis(),
        query_elapsed.as_millis(),
        verification_elapsed.as_millis(),
        module_count,
        declaration_count,
        if cache.is_some() {
            "persistent"
        } else {
            "disabled"
        },
    );
    Ok(observations)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn query_source_uses_structured_names_and_isolated_imports() {
        let source = build_query_source(
            "NONCE",
            Path::new("/isolated/artifacts"),
            &[DeclarationQueryGroup {
                module: "Pkg.«matches»_Proofs".to_string(),
                declarations: vec![DeclarationQuery::untyped("«exists_».aborts")],
            }],
        );
        assert!(source.contains("#[\"Pkg\", \"matches_Proofs\"]"));
        assert!(source.contains("#[\"exists_\", \"aborts\"]"));
        assert!(source.contains("Lean.withImportModules"));
        assert!(!source.contains("qualifiedName"));
        assert!(!source.contains("Lean.Meta.isDefEq"));
        assert!(!source.contains("import Pkg"));
    }

    #[test]
    fn immutable_query_snapshot_preserves_the_toolchain_pin() {
        let project = tempfile::tempdir().unwrap();
        std::fs::write(
            project.path().join("lakefile.lean"),
            "import Lake\nopen Lake DSL\npackage pinned_query\n",
        )
        .unwrap();
        std::fs::write(
            project.path().join("lean-toolchain"),
            super::super::GENERATED_LEAN_TOOLCHAIN,
        )
        .unwrap();

        let snapshot =
            QueryProjectSnapshot::create(project.path(), None, "toolchain snapshot test").unwrap();

        assert_eq!(
            std::fs::read_to_string(snapshot.project_dir.join("lean-toolchain")).unwrap(),
            super::super::GENERATED_LEAN_TOOLCHAIN
        );
        std::fs::write(project.path().join("lean-toolchain"), "changed\n").unwrap();
        assert!(snapshot
            .verify_sources_unchanged("toolchain snapshot test")
            .is_err());
    }

    #[test]
    fn protocol_rejects_duplicate_and_truncated_results() {
        let groups = [DeclarationQueryGroup {
            module: "Pkg.M".to_string(),
            declarations: vec![DeclarationQuery::untyped("Pkg.M.f")],
        }];
        let duplicate = "N|D|0|0|def|1\nN|D|0|0|def|1\nN|END|1|1\n";
        assert!(parse_query_output("N", &groups, duplicate, "test").is_err());
        assert!(parse_query_output("N", &groups, "N|D|0|0|def|1\n", "test").is_err());
    }

    #[cfg(unix)]
    #[test]
    fn timeout_covers_descendants_that_keep_output_pipes_open() {
        let mut command = Command::new("sh");
        command.args(["-c", "(sleep 30) & exit 0"]);
        let started = Instant::now();

        let error = run_command_with_timeout(
            &mut command,
            None,
            "descendant timeout test",
            Duration::from_millis(200),
        )
        .unwrap_err();

        assert!(matches!(
            error,
            RenderError::LeanEnvironmentQuery { what }
                if what.contains("output pipes remained open")
        ));
        assert!(started.elapsed() < Duration::from_secs(2));
    }

    #[cfg(unix)]
    #[test]
    fn cache_layout_preserves_base_permissions_and_rejects_managed_symlinks() {
        use std::os::unix::fs::{symlink, PermissionsExt};

        let project = tempfile::tempdir().unwrap();
        std::fs::write(
            project.path().join("lakefile.lean"),
            "import Lake\nopen Lake DSL\npackage cache_layout_test\n",
        )
        .unwrap();
        let toolchain = resolve_toolchain(project.path(), "test").unwrap();
        let base = tempfile::tempdir().unwrap();
        std::fs::set_permissions(base.path(), std::fs::Permissions::from_mode(0o755)).unwrap();
        let layout = QueryCacheLayout::at_base(base.path(), &toolchain, "test").unwrap();
        assert_eq!(
            std::fs::metadata(base.path()).unwrap().permissions().mode() & 0o777,
            0o755
        );
        assert_eq!(
            std::fs::metadata(&layout.root_dir)
                .unwrap()
                .permissions()
                .mode()
                & 0o777,
            0o700
        );
        assert!(!layout.overlaps(project.path()));
        assert!(layout.overlaps(&layout.root_dir.join("source")));

        let link = base.path().join("link");
        symlink(&layout.root_dir, &link).unwrap();
        assert!(create_private_cache_directory(&link, "test").is_err());
    }

    #[cfg(unix)]
    #[test]
    fn lake_artifacts_are_reused_across_fresh_query_snapshots() {
        let project = tempfile::tempdir().unwrap();
        let cache_root = tempfile::tempdir().unwrap();
        let marker_dir = tempfile::tempdir().unwrap();
        let marker = marker_dir.path().join("compiled");
        std::fs::write(
            project.path().join("lakefile.lean"),
            r#"import Lake
open Lake DSL

package environment_query_cache_test

lean_lib CacheFixtures where
  roots := #[`Cached]
"#,
        )
        .unwrap();
        std::fs::write(
            project.path().join("Cached.lean"),
            format!(
                r#"import Lake

run_cmd do
  let marker : System.FilePath := "{}"
  let previous ← if ← marker.pathExists then IO.FS.readFile marker else pure ""
  IO.FS.writeFile marker (previous ++ "compiled\n")

def cachedValue : Nat := 1
"#,
                marker.display()
            ),
        )
        .unwrap();
        let groups = [DeclarationQueryGroup {
            module: "Cached".to_string(),
            declarations: vec![DeclarationQuery::untyped("cachedValue")],
        }];
        let toolchain = resolve_toolchain(project.path(), "cache reuse test").unwrap();
        let cache =
            QueryCacheLayout::at_base(cache_root.path(), &toolchain, "cache reuse test").unwrap();

        for _ in 0..2 {
            let snapshot = QueryProjectSnapshot::create(
                project.path(),
                Some(&cache.workspace_dir),
                "cache reuse test",
            )
            .unwrap();
            let artifact_dir = prepare_modules(
                &snapshot.project_dir,
                &groups,
                &toolchain,
                Some(&cache),
                "cache reuse test",
            )
            .unwrap();
            assert!(artifact_dir.join("Cached.olean").is_file());
        }
        assert_eq!(std::fs::read_to_string(marker).unwrap(), "compiled\n");

        let changed_marker = marker_dir.path().join("changed");
        std::fs::write(
            project.path().join("Cached.lean"),
            format!(
                r#"import Lake

run_cmd do
  IO.FS.writeFile "{}" "changed"

def cachedValue : Nat := 2
"#,
                changed_marker.display()
            ),
        )
        .unwrap();
        let changed_snapshot = QueryProjectSnapshot::create(
            project.path(),
            Some(&cache.workspace_dir),
            "cache invalidation test",
        )
        .unwrap();
        prepare_modules(
            &changed_snapshot.project_dir,
            &groups,
            &toolchain,
            Some(&cache),
            "cache invalidation test",
        )
        .unwrap();
        assert_eq!(std::fs::read_to_string(changed_marker).unwrap(), "changed");

        std::fs::remove_file(project.path().join("Cached.lean")).unwrap();
        let missing_snapshot = QueryProjectSnapshot::create(
            project.path(),
            Some(&cache.workspace_dir),
            "stale cache rejection test",
        )
        .unwrap();
        assert!(prepare_modules(
            &missing_snapshot.project_dir,
            &groups,
            &toolchain,
            Some(&cache),
            "stale cache rejection test",
        )
        .is_err());
    }

    #[test]
    fn real_lean_query_classifies_kinds_and_origins() {
        let project = tempfile::tempdir().unwrap();
        std::fs::write(
            project.path().join("lakefile.lean"),
            r#"import Lake
open Lake DSL

package environment_query_test

lean_lib QueryFixtures where
  roots := #[`Foreign, `Kinds, `SameA, `SameB]
"#,
        )
        .unwrap();
        std::fs::write(
            project.path().join("Foreign.lean"),
            "theorem importedOnly : True := by trivial\n",
        )
        .unwrap();
        std::fs::write(
            project.path().join("Kinds.lean"),
            r#"import Foreign

def localDef : Nat := 0
abbrev localAbbrev : Type := Nat
opaque localOpaque : Nat := 0
theorem localTheorem : True := by trivial
axiom localAxiom : True
macro "declareMacroTheorem" name:ident : command => `(theorem $name : True := by trivial)
declareMacroTheorem macroTheorem
"#,
        )
        .unwrap();
        std::fs::write(
            project.path().join("SameA.lean"),
            "theorem repeated : True := by trivial\n",
        )
        .unwrap();
        std::fs::write(
            project.path().join("SameB.lean"),
            "theorem repeated : True := by trivial\n",
        )
        .unwrap();
        std::fs::write(
            project.path().join("BrokenUnrelated.lean"),
            "this unrelated module must not be built\n",
        )
        .unwrap();

        let groups = vec![
            DeclarationQueryGroup {
                module: "Kinds".to_string(),
                declarations: vec![
                    DeclarationQuery::untyped("localDef"),
                    DeclarationQuery::untyped("localAbbrev"),
                    DeclarationQuery::untyped("localOpaque"),
                    DeclarationQuery::untyped("localTheorem"),
                    DeclarationQuery::untyped("localAxiom"),
                    DeclarationQuery::untyped("macroTheorem"),
                    DeclarationQuery::untyped("missingDeclaration"),
                    DeclarationQuery::untyped("importedOnly"),
                ],
            },
            DeclarationQueryGroup {
                module: "SameA".to_string(),
                declarations: vec![DeclarationQuery::untyped("repeated")],
            },
            DeclarationQueryGroup {
                module: "SameB".to_string(),
                declarations: vec![DeclarationQuery::untyped("repeated")],
            },
        ];

        let observed = query_declarations(project.path(), &groups, "real Lean test").unwrap();
        let local = |kind| DeclarationObservation {
            kind,
            declared_in_expected_module: true,
        };
        assert_eq!(
            observed[0],
            vec![
                local(DeclarationKind::Definition),
                local(DeclarationKind::Abbreviation),
                local(DeclarationKind::Opaque),
                local(DeclarationKind::Theorem),
                local(DeclarationKind::Axiom),
                local(DeclarationKind::Theorem),
                DeclarationObservation {
                    kind: DeclarationKind::Missing,
                    declared_in_expected_module: false,
                },
                DeclarationObservation {
                    kind: DeclarationKind::Theorem,
                    declared_in_expected_module: false,
                },
            ]
        );
        assert_eq!(observed[1], vec![local(DeclarationKind::Theorem)]);
        assert_eq!(observed[2], vec![local(DeclarationKind::Theorem)]);
    }
}
