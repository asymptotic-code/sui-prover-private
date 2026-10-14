//! Render the normalized pipeline IR to Lean source.
//!
//! The default pipeline has already lowered jumps and finalized loops before
//! this boundary. Residual control-flow forms are explicit post-stage
//! invariant failures. Mutable references render through the
//! `Prover.Mutation.Mutation` prelude model.

mod bag_universe;
mod bounded_nat;
mod conjunct_projection;
mod context;
mod dyn_type_universe;
mod environment;
pub(crate) mod escape;
mod expr;
pub(crate) mod function;
mod globals;
pub mod lemma_companions;
pub mod loop_termination;
mod materialize;
mod mutation;
mod native_models;
mod obj_type_universe;
pub mod olean_seed;
mod struct_def;
pub mod struct_idx;
mod ty;
mod world;
mod writer;

#[cfg(test)]
mod tests;

use std::collections::{BTreeMap, BTreeSet, HashSet};
use std::fmt::Write;
use std::path::{Path, PathBuf};

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

use crate::ir::{FunId, GlobalId, ModId, Program, StructId, VarId};

use self::function::render_function;
use self::struct_def::render_struct;
use self::writer::LeanWriter;

pub(crate) use self::expr::types::RenderedBranchType as EffectiveBranchType;

#[derive(Debug)]
struct LakePathDependency {
    name: String,
    config_file: String,
    directory: PathBuf,
}

const RESERVED_LEAN_MODULE_ROOTS: [&str; 7] =
    ["Aesop", "Auto", "Batteries", "Init", "Lake", "Lean", "Std"];
pub const GENERATED_LEAN_TOOLCHAIN: &str = "leanprover/lean4:v4.32.2\n";
const AUTOMATION_DEPENDENCIES: [AutomationDependency<'static>; 3] = [
    AutomationDependency {
        name: "batteries",
        folder: "batteries",
        config_file: "lakefile.toml",
        source_digest: "89cee974f9d29c2d69ae06213486eb6bfb22759c8d59d4a24baffcd2e2dfb720",
    },
    AutomationDependency {
        name: "aesop",
        folder: "aesop",
        config_file: "lakefile.toml",
        source_digest: "dd0cbd5eeded70f9d95998a48fa906a3460f8b40cd8d7b21a15503af756bf09f",
    },
    AutomationDependency {
        name: "auto",
        folder: "lean-auto",
        config_file: "lakefile.lean",
        source_digest: "987229cd4ff1f32413ed9b903bcacaa19b560b89768bbbc7acb6ba6e40fcf19d",
    },
];

#[derive(Clone, Copy)]
struct AutomationDependency<'a> {
    name: &'a str,
    folder: &'a str,
    config_file: &'a str,
    source_digest: &'a str,
}

#[derive(Serialize)]
#[serde(rename_all = "camelCase")]
struct LakeManifest<'a> {
    version: &'static str,
    packages_dir: &'static str,
    packages: Vec<LakeManifestPathDependency<'a>>,
    name: &'static str,
    lake_dir: &'static str,
    fixed_toolchain: bool,
}

#[derive(Serialize)]
#[serde(rename_all = "camelCase")]
struct LakeManifestPathDependency<'a> {
    #[serde(rename = "type")]
    dependency_type: &'static str,
    scope: &'static str,
    name: &'a str,
    manifest_file: &'static str,
    inherited: bool,
    dir: &'a Path,
    config_file: &'a str,
}

pub(crate) fn rendered_var_target_types(
    body: &crate::ir::Block,
    return_type: &crate::ir::Type,
) -> BTreeMap<VarId, crate::ir::Type> {
    self::expr::compute_var_target_types(body, return_type)
}

pub(crate) fn effective_type_of(
    expression: &crate::ir::Expr,
    program: &Program,
    var_types: &BTreeMap<VarId, crate::ir::Type>,
) -> Option<crate::ir::Type> {
    self::expr::rendered_type_of(expression, program, var_types)
}

pub(crate) fn effective_block_branch_type(
    block: &crate::ir::Block,
    program: &Program,
    var_types: &BTreeMap<VarId, crate::ir::Type>,
) -> EffectiveBranchType {
    self::expr::rendered_block_branch_type(block, program, var_types)
}

pub(crate) fn unify_effective_branch_types(
    arms: &[EffectiveBranchType],
) -> Result<Option<crate::ir::Type>, ()> {
    self::expr::unify_branch_value_types(arms)
}

pub(crate) fn effective_block_can_render_as_type(
    block: &crate::ir::Block,
    target: &crate::ir::Type,
    program: &Program,
    var_types: &BTreeMap<VarId, crate::ir::Type>,
) -> bool {
    self::expr::block_can_render_as_type(block, target, program, var_types)
}

/// Whether `expression` can be emitted at an expected Lean value type using
/// the renderer's supported value/`Mutation` coercions.
pub(crate) fn effective_expr_can_render_as_type(
    expression: &crate::ir::Expr,
    target: &crate::ir::Type,
    program: &crate::ir::Program,
    var_types: &std::collections::BTreeMap<crate::ir::VarId, crate::ir::Type>,
) -> bool {
    self::expr::expr_can_render_as_type(
        expression,
        crate::ir::analysis::type_of::strip_singleton_tuple(target),
        program,
        var_types,
    )
}

pub(crate) fn rendered_inner_statement_is_erased(statement: &crate::ir::Stmt) -> bool {
    self::expr::is_erased_inner_discard(statement)
}

pub(crate) fn rendered_let_target_type(
    pattern: &[Option<VarId>],
    value: &crate::ir::Expr,
    var_target_types: &BTreeMap<VarId, crate::ir::Type>,
    program: &Program,
    var_types: &BTreeMap<VarId, crate::ir::Type>,
) -> Option<crate::ir::Type> {
    self::expr::let_target_type(pattern, value, var_target_types, program, var_types)
}

pub(crate) fn rendered_let_bindings(
    pattern: &[Option<VarId>],
    value: &crate::ir::Expr,
    target: Option<&crate::ir::Type>,
    program: &Program,
    var_types: &BTreeMap<VarId, crate::ir::Type>,
) -> Vec<(VarId, crate::ir::Type)> {
    self::expr::rendered_let_bindings(pattern, value, target, program, var_types)
}

pub(crate) fn rendered_match_selector_type_args(
    struct_id: StructId,
    selector: &crate::ir::Expr,
    program: &Program,
    var_types: &BTreeMap<VarId, crate::ir::Type>,
) -> Vec<crate::ir::Type> {
    self::expr::rendered_match_selector_type_args(struct_id, selector, program, var_types)
}

pub use self::mutation::{
    any_key_ctor_name, any_key_payload_ty, collect_any_key, render_any_key_file, AnyKeyVariant,
};

pub use self::world::{
    any_ctor_name as any_event_object_ctor_name, any_payload_ty as any_event_object_payload_ty,
    collect_any_event_object, render_any_event_file, render_any_object_file,
    render_shared_world_file, AnyVariant,
};

pub const TEST_DECLARATIONS_MANIFEST: &str = "test_declarations.toml";

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ModuleRenderLocation {
    pub package: String,
    pub file_stem: String,
    pub import_path: String,
    pub namespace: String,
}

pub fn module_render_location(package: &str, module: &str) -> ModuleRenderLocation {
    let namespace = self::escape::module_render_namespace(package, module);
    let package = if package.is_empty() {
        "NewPipeline".to_string()
    } else {
        package.to_string()
    };
    let file_stem = self::escape::module_name_to_namespace(module);
    ModuleRenderLocation {
        import_path: format!("{package}.{file_stem}"),
        namespace,
        package,
        file_stem,
    }
}

#[derive(Clone, Debug, Deserialize, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct TestDeclaration {
    pub addressed_module: String,
    pub function: String,
    pub import_path: String,
    pub lean_declaration: String,
    pub needs_world: bool,
    pub ghost_param_count: usize,
}

#[derive(Clone, Debug, Deserialize, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct TestDeclarations {
    pub schema_version: u32,
    #[serde(rename = "declaration")]
    pub declarations: Vec<TestDeclaration>,
}

pub fn read_test_declarations(output_dir: &Path) -> RenderResult<TestDeclarations> {
    let path = output_dir.join(TEST_DECLARATIONS_MANIFEST);
    let input = std::fs::read_to_string(&path).map_err(|error| RenderError::Io {
        what: format!("read({}): {error}", path.display()),
    })?;
    let manifest: TestDeclarations = toml::from_str(&input).map_err(|error| RenderError::Io {
        what: format!("parse({}): {error}", path.display()),
    })?;
    if manifest.schema_version != 1 {
        return Err(RenderError::Io {
            what: format!(
                "unsupported {} schema version {}",
                path.display(),
                manifest.schema_version
            ),
        });
    }
    validate_test_declarations(&manifest, &path)?;
    Ok(manifest)
}

fn validate_test_declarations(manifest: &TestDeclarations, path: &Path) -> RenderResult<()> {
    let mut keys = BTreeSet::new();
    let mut import_owners = BTreeMap::new();
    let mut lean_targets = BTreeMap::new();
    for declaration in &manifest.declarations {
        if !crate::ir::is_canonical_addressed_module(&declaration.addressed_module) {
            return Err(RenderError::Io {
                what: format!(
                    "{} contains non-canonical addressed module `{}`",
                    path.display(),
                    declaration.addressed_module
                ),
            });
        }
        for (label, value) in [
            ("function", declaration.function.as_str()),
            ("import_path", declaration.import_path.as_str()),
            ("lean_declaration", declaration.lean_declaration.as_str()),
        ] {
            if value.is_empty() || value.trim() != value {
                return Err(RenderError::Io {
                    what: format!("{} contains invalid {label} `{value}`", path.display()),
                });
            }
        }
        let key = (
            declaration.addressed_module.as_str(),
            declaration.function.as_str(),
        );
        if !keys.insert(key) {
            return Err(RenderError::Io {
                what: format!(
                    "{} contains duplicate declaration `{}::{}`",
                    path.display(),
                    declaration.addressed_module,
                    declaration.function
                ),
            });
        }
        if let Some(owner) = import_owners.insert(
            declaration.import_path.as_str(),
            declaration.addressed_module.as_str(),
        ) {
            if owner != declaration.addressed_module {
                return Err(RenderError::Io {
                    what: format!(
                        "{} aliases addressed modules `{}` and `{}` to import `{}`",
                        path.display(),
                        owner,
                        declaration.addressed_module,
                        declaration.import_path
                    ),
                });
            }
        }
        if let Some(owner) = lean_targets.insert(
            (
                declaration.import_path.as_str(),
                declaration.lean_declaration.as_str(),
            ),
            (
                declaration.addressed_module.as_str(),
                declaration.function.as_str(),
            ),
        ) {
            if owner
                != (
                    declaration.addressed_module.as_str(),
                    declaration.function.as_str(),
                )
            {
                return Err(RenderError::Io {
                    what: format!(
                        "{} aliases multiple addressed declarations to Lean target `{}` in `{}`",
                        path.display(),
                        declaration.lean_declaration,
                        declaration.import_path
                    ),
                });
            }
        }
    }
    Ok(())
}

/// Errors produced by the renderer.
///
/// Unsupported or unlowered IR surfaces as `UnsupportedConstruct`.
/// Missing registry entries surface as the `UnknownXxx` variants and
/// should be impossible if the validator passed.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RenderError {
    /// The renderer encountered an unsupported or unlowered IR construct.
    /// `what` is a short human-readable tag.
    UnsupportedConstruct {
        what: &'static str,
    },
    /// Global borrows/writebacks must be converted to hidden reference
    /// parameters by `thread_globals` before rendering. Rendering one
    /// directly could silently lose a threaded global read or update.
    UnthreadedGlobal {
        operation: &'static str,
        id: GlobalId,
    },
    UnknownFunId {
        id: FunId,
    },
    UnknownStructId {
        id: StructId,
    },
    /// A closed global type applies a known struct at the wrong arity.
    InvalidGlobalStructTypeArity {
        global: GlobalId,
        struct_id: StructId,
        expected: usize,
        actual: usize,
    },
    InvalidGlobalStorageType {
        global: GlobalId,
        kind: &'static str,
    },
    UnknownModId {
        id: ModId,
    },
    PackVariantOnNonEnum {
        id: StructId,
    },
    UnknownVariant {
        struct_id: StructId,
        variant: usize,
    },
    MatchOnNonEnum {
        id: StructId,
    },
    EmptyParamName {
        func: String,
    },
    InvalidStructFieldType {
        struct_name: String,
        field_name: String,
        reason: &'static str,
    },
    /// A proof obligation must be a closed value expression. Rendering
    /// control-flow tails as a proposition would change the statement.
    MalformedTheoremBody {
        module: String,
        function: String,
        tail: &'static str,
    },
    /// Native calls in proof output must resolve to a renderer intrinsic, an
    /// exact root-package spec-native definition, or an explicitly classified
    /// semantic model. The generated `native_models.toml` records every
    /// referenced native and its status.
    NativeModelPolicy {
        what: String,
    },
    LeanEnvironmentQuery {
        what: String,
    },
    ProofStatementDrift {
        path: String,
        obligation: String,
        recorded_fingerprint: String,
        generated_fingerprint: String,
        generated_prop: String,
        generated_statement: String,
        replacement_marker: String,
    },
    Io {
        what: String,
    },
    /// A user module declares a `native fun` but its required regular,
    /// non-symlink Lean model file is missing. Root-package models use
    /// `<package-root>/lean/natives/<Module>Natives.lean`; dependency
    /// models use
    /// `<package-root>/lean/natives/<Package>/<Module>Natives.lean`.
    /// The pipeline never synthesizes a fallback body for these natives.
    /// `looked_up` is the absolute path the pipeline searched.
    ///
    /// Import DAG contract for the natives file: it may import the
    /// module's `<Module>_Types` file, its generated CODE modules, and
    /// the `Prelude`; the generated Funcs file imports it in turn.
    MissingNativesFile {
        module: String,
        looked_up: String,
    },
    /// Legacy compatibility variant. Referenced non-spec user natives are now
    /// handled by the native-model policy and rejected as unclassified unless
    /// an exact reviewed rule trusts their handwritten runtime model.
    NonSpecOnlyNative {
        module: String,
        function: String,
    },
    /// A user module declares a `native fun`, but no package root was
    /// available to look up its Lean model file (`loop_termination_path`
    /// was `None`). Production always supplies one; this guards the tests /
    /// programmatic-caller path.
    MissingPackageRoot {
        module: String,
    },
    /// A user module declares a `native fun`, but the caller did not identify
    /// the root package. Without that identity the renderer cannot safely
    /// choose between the flat root overlay and a package-qualified dependency
    /// overlay.
    MissingRootPackage {
        module: String,
    },
}

pub type RenderResult<T> = Result<T, RenderError>;

/// Render `program` to a single Lean string.
///
/// First-slice output shape:
///
/// ```text
/// import Prelude.BoundedNat
/// import Prelude.ProgramState
///
/// namespace <ModuleNamespace>
///
/// -- struct definitions ...
/// -- function definitions ...
///
/// end <ModuleNamespace>
/// ```
///
/// One file per `Program`, one namespace per module. Multi-module
/// programs concatenate the namespace blocks in module-id order.
pub fn render_program(program: &Program) -> RenderResult<String> {
    render_program_filtered(program, None)
}

/// Like [`render_program`] but only emits namespaces for modules
/// whose `package_name` equals `user_package` (when `Some`).
/// `None` includes every non-native module (same as
/// [`render_program`]).
pub fn render_program_filtered(
    program: &Program,
    user_package: Option<&str>,
) -> RenderResult<String> {
    let context = self::context::RenderContext::new(
        program,
        self::loop_termination::LoopRenderContext::default(),
    );
    let mut writer = LeanWriter::new(String::new());
    render_program_into_filtered(&context, user_package, &mut writer)?;
    Ok(writer.into_inner())
}

fn render_program_into<W: Write>(program: &Program, w: &mut LeanWriter<W>) -> RenderResult<()> {
    let context = self::context::RenderContext::new(
        program,
        self::loop_termination::LoopRenderContext::default(),
    );
    render_program_into_filtered(&context, None, w)
}

fn render_program_into_filtered<W: Write>(
    context: &self::context::RenderContext<'_>,
    user_package: Option<&str>,
    w: &mut LeanWriter<W>,
) -> RenderResult<()> {
    let program = context.program;
    self::globals::ensure_threaded(program)?;
    // Imports.
    w.line("import Prelude.BoundedNat");
    w.line("import Prelude.ProgramState");
    w.line("import Prelude.Mutation");
    w.line("import Prelude.TypedMap");
    w.line("import Prelude.World");
    // Same condition as the per-module disk render: a registered alias `.val`
    // fact carries `@[move_effect]`, whose syntax needs this import.
    if program.modules.keys().any(|mid| {
        user_package.is_none_or(|pkg| {
            program
                .modules
                .get(mid)
                .is_some_and(|module| module.package_name == pkg)
        }) && module_registers_alias_val_facts(&module_opaque_const_aliases(program, *mid))
    }) {
        w.line(&format!("import {}", MOVE_AUTO_ATTR_MODULE));
    }
    w.newline();
    // Inline the per-program `AnyKey` so the `Mutation` abbreviation
    // resolves in this self-contained single-string output.
    // (Real disk render via `render_program_to_dir` reads this from
    // each user package's `Generated/AnyKey.lean` instead.)
    let any_key_variants = self::mutation::collect_any_key_in(context);
    let empty_lemma_set: std::collections::BTreeSet<String> = std::collections::BTreeSet::new();
    let any_key_body =
        self::mutation::render_any_key_file_in(&any_key_variants, context, &empty_lemma_set);
    for line in any_key_body
        .lines()
        .skip_while(|l| l.starts_with("--") || l.starts_with("import") || l.is_empty())
    {
        w.line(line);
    }
    w.newline();

    // Inline per-program `AnyEvent`, `AnyObject`, and the `World`
    // abbreviation so stage-4-emitted Impure signatures resolve.
    // (Real disk render emits these as separate `Generated/*.lean`
    // files per user package.)
    let (any_event_variants, any_object_variants) = self::world::collect_any_event_object(program);
    let any_event_body = self::world::render_any_event_file(&any_event_variants);
    for line in any_event_body
        .lines()
        .skip_while(|l| l.starts_with("--") || l.starts_with("import") || l.is_empty())
    {
        w.line(line);
    }
    w.newline();
    let any_object_body = self::world::render_any_object_file(&any_object_variants);
    for line in any_object_body
        .lines()
        .skip_while(|l| l.starts_with("--") || l.starts_with("import") || l.is_empty())
    {
        w.line(line);
    }
    w.newline();
    w.line("abbrev World := Prover.World.World AnyEvent AnyObject Unit Unit");
    w.newline();

    // One namespace block per module, in deterministic id order
    // (`Program::modules` is a `BTreeMap`). Native modules are
    // emitted as standalone stub files by `render_program_to_dir`
    // (so imports like `MoveStdlib.MoveOption` resolve); they're
    // skipped here in the in-memory single-string form.
    for (mid, module) in &program.modules {
        if let Some(pkg) = user_package {
            if module.package_name != pkg {
                continue;
            }
        }
        let namespace = self::escape::module_render_namespace(&module.package_name, &module.name);

        w.write("namespace ");
        w.line(&namespace);
        w.newline();

        let opaque_const_aliases = module_opaque_const_aliases(program, *mid);
        if !opaque_const_aliases.is_empty() {
            emit_opaque_const_aliases(w, &opaque_const_aliases);
        }

        // Structs in this module, topologically sorted so a struct's
        // dependencies (other structs it embeds) are defined before
        // it. Lean rejects forward references between non-mutual
        // structures, so a deterministic id-order emission breaks for
        // packages that define `Box127 { x: Box63 ... }` before
        // `Box63`.
        let mut module_structs: Vec<(&StructId, &crate::ir::Struct)> = program
            .structs
            .iter()
            .filter(|(_, s)| s.module_id == *mid)
            .collect();
        topo_sort_structs(&mut module_structs, program);
        for (_, s) in module_structs {
            render_struct(s, context, Some(&namespace), w)?;
        }

        // First-class globals are state-threaded before this boundary. Emit
        // only deterministic metadata/root constructors for external callers;
        // the function bodies below consume the hidden reference parameters
        // introduced by that lowering (Mutation for writable globals, erased
        // immutable references for readonly globals).
        self::globals::render_module_globals(program, *mid, &namespace, w)?;

        // Opaque ghost-output declarations (ensures-published ghosts,
        // ghost-support.md Part 4) -- after structs (a param type may be
        // module-local), before the functions that call them.
        self::function::render_ghost_opaque_decls(program, *mid, Some(&namespace), w);

        // Functions in this module, topologically sorted by call
        // dependency so a callee comes before its callers. Lean
        // requires definitions to be visible at the point of use; a
        // forward reference like `def borrow ... := is_some ...; ...`
        // where `is_some` is defined later in the same namespace
        // fails with "Unknown identifier `is_some`".
        let module_funcs: Vec<(&FunId, &crate::ir::Function)> = program
            .functions
            .iter()
            .filter(|(_, f)| f.module == *mid)
            .collect();
        let sccs = compute_function_sccs(&module_funcs, program);
        emit_function_sccs(&sccs, context, &namespace, w)?;

        w.write("end ");
        w.line(&namespace);
        w.newline();
    }
    Ok(())
}

fn lake_path_literal(path: &Path) -> String {
    path.to_string_lossy()
        .chars()
        .flat_map(|c| match c {
            '\\' => "/".chars().collect::<Vec<_>>(),
            '"' => "\\\"".chars().collect::<Vec<_>>(),
            c => vec![c],
        })
        .collect()
}

fn dependency_source_digest(root: &Path) -> RenderResult<String> {
    fn collect(root: &Path, directory: &Path, paths: &mut Vec<PathBuf>) -> RenderResult<()> {
        let mut entries = std::fs::read_dir(directory)
            .map_err(|error| RenderError::Io {
                what: format!("read dependency directory {}: {error}", directory.display()),
            })?
            .collect::<Result<Vec<_>, _>>()
            .map_err(|error| RenderError::Io {
                what: format!(
                    "read dependency entry under {}: {error}",
                    directory.display()
                ),
            })?;
        entries.sort_by_key(std::fs::DirEntry::file_name);
        for entry in entries {
            let path = entry.path();
            let relative = path
                .strip_prefix(root)
                .expect("dependency entry is beneath its root");
            if relative
                .components()
                .any(|component| matches!(component.as_os_str().to_str(), Some(".git" | ".lake")))
            {
                continue;
            }
            let metadata = std::fs::symlink_metadata(&path).map_err(|error| RenderError::Io {
                what: format!("inspect dependency entry {}: {error}", path.display()),
            })?;
            if metadata.is_dir() {
                collect(root, &path, paths)?;
            } else if metadata.is_file() || metadata.file_type().is_symlink() {
                paths.push(path);
            } else {
                return Err(RenderError::Io {
                    what: format!("unsupported dependency entry {}", path.display()),
                });
            }
        }
        Ok(())
    }

    let mut paths = Vec::new();
    collect(root, root, &mut paths)?;
    paths.sort_by_key(|path| {
        path.strip_prefix(root)
            .expect("dependency entry is beneath its root")
            .to_string_lossy()
            .replace('\\', "/")
    });
    let mut digest = Sha256::new();
    for path in paths {
        let relative = path
            .strip_prefix(root)
            .expect("dependency entry is beneath its root")
            .to_string_lossy()
            .replace('\\', "/")
            .into_bytes();
        let metadata = std::fs::symlink_metadata(&path).map_err(|error| RenderError::Io {
            what: format!("inspect dependency entry {}: {error}", path.display()),
        })?;
        let (kind, payload) = if metadata.file_type().is_symlink() {
            (
                b'L',
                std::fs::read_link(&path)
                    .map_err(|error| RenderError::Io {
                        what: format!("read dependency symlink {}: {error}", path.display()),
                    })?
                    .to_string_lossy()
                    .replace('\\', "/")
                    .into_bytes(),
            )
        } else {
            (
                b'F',
                std::fs::read(&path).map_err(|error| RenderError::Io {
                    what: format!("read dependency source {}: {error}", path.display()),
                })?,
            )
        };
        digest.update([kind]);
        digest.update((relative.len() as u64).to_be_bytes());
        digest.update(relative);
        digest.update((payload.len() as u64).to_be_bytes());
        digest.update(payload);
    }
    Ok(format!("{:x}", digest.finalize()))
}

fn verify_dependency_source_digest(
    name: &str,
    directory: &Path,
    expected: &str,
) -> RenderResult<()> {
    static VERIFIED: std::sync::OnceLock<std::sync::Mutex<BTreeSet<(PathBuf, String)>>> =
        std::sync::OnceLock::new();
    let verified = VERIFIED.get_or_init(|| std::sync::Mutex::new(BTreeSet::new()));
    let key = (directory.to_path_buf(), expected.to_string());
    let mut verified = verified.lock().map_err(|_| RenderError::Io {
        what: "proof-automation dependency digest cache is poisoned".to_string(),
    })?;
    if verified.contains(&key) {
        return Ok(());
    }
    let actual = dependency_source_digest(directory)?;
    if actual != expected {
        return Err(RenderError::Io {
            what: format!(
                "vendored proof-automation dependency `{name}` at {} has source digest \
                 `{actual}`, expected `{expected}`",
                directory.display()
            ),
        });
    }
    // The final proof audit hashes the isolated dependency copies again. This
    // process-local cache avoids rereading every vendored source for each
    // module-mode renderer invocation before that authoritative audit.
    verified.insert(key);
    Ok(())
}

fn proof_automation_dependencies(
    lemmas_dir: Option<&Path>,
) -> RenderResult<Vec<LakePathDependency>> {
    proof_automation_dependencies_with_specs(lemmas_dir, &AUTOMATION_DEPENDENCIES)
}

fn proof_automation_dependencies_with_specs(
    lemmas_dir: Option<&Path>,
    dependency_specs: &[AutomationDependency<'_>],
) -> RenderResult<Vec<LakePathDependency>> {
    let Some(lemmas_dir) = lemmas_dir else {
        return Ok(Vec::new());
    };
    if ![
        lemmas_dir.join("natives/Prover/MoveAuto.lean"),
        lemmas_dir.join("Prover/MoveAuto.lean"),
    ]
    .into_iter()
    .any(|path| path.is_file())
    {
        return Ok(Vec::new());
    }
    let lemmas_dir = lemmas_dir.canonicalize().map_err(|error| RenderError::Io {
        what: format!(
            "canonicalize runtime Lean lemmas directory {}: {error}",
            lemmas_dir.display()
        ),
    })?;
    let vendor = lemmas_dir
        .ancestors()
        .map(|ancestor| ancestor.join("vendor"))
        .find(|candidate| {
            candidate.join("VERSIONS.md").is_file()
                && dependency_specs.iter().all(|dependency| {
                    let directory = candidate.join(dependency.folder);
                    directory.join(dependency.config_file).is_file()
                        && directory.join("lake-manifest.json").is_file()
                        && directory.join("lean-toolchain").is_file()
                })
        })
        .ok_or_else(|| RenderError::Io {
            what: format!(
                "locate complete proof-automation vendor tree from runtime lemmas directory {}",
                lemmas_dir.display()
            ),
        })?;
    dependency_specs
        .iter()
        .map(|dependency| {
            let directory = vendor.join(dependency.folder);
            if !directory.join(dependency.config_file).is_file()
                || !directory.join("lake-manifest.json").is_file()
                || !directory.join("lean-toolchain").is_file()
            {
                return Err(RenderError::Io {
                    what: format!(
                        "vendored proof-automation dependency `{}` is incomplete at {}",
                        dependency.name,
                        directory.display()
                    ),
                });
            }
            let toolchain_path = directory.join("lean-toolchain");
            let toolchain =
                std::fs::read_to_string(&toolchain_path).map_err(|error| RenderError::Io {
                    what: format!(
                        "read proof-automation toolchain {}: {error}",
                        toolchain_path.display()
                    ),
                })?;
            if toolchain != GENERATED_LEAN_TOOLCHAIN {
                return Err(RenderError::Io {
                    what: format!(
                        "proof-automation dependency `{}` uses toolchain `{}`, expected `{}`",
                        dependency.name,
                        toolchain.trim(),
                        GENERATED_LEAN_TOOLCHAIN.trim()
                    ),
                });
            }
            let directory = directory.canonicalize().map_err(|error| RenderError::Io {
                what: format!(
                    "canonicalize vendored proof-automation dependency {}: {error}",
                    directory.display()
                ),
            })?;
            verify_dependency_source_digest(dependency.name, &directory, dependency.source_digest)?;
            Ok(LakePathDependency {
                name: dependency.name.to_string(),
                config_file: dependency.config_file.to_string(),
                directory,
            })
        })
        .collect()
}

fn path_parts(path: &Path) -> Option<(String, Vec<std::ffi::OsString>)> {
    let mut root = String::new();
    let mut parts = Vec::new();
    for component in path.components() {
        match component {
            std::path::Component::Prefix(prefix) => {
                root.push_str(&prefix.as_os_str().to_string_lossy());
            }
            std::path::Component::RootDir => root.push('/'),
            std::path::Component::CurDir => {}
            std::path::Component::ParentDir => return None,
            std::path::Component::Normal(part) => parts.push(part.to_os_string()),
        }
    }
    Some((root, parts))
}

fn path_relative_to(from_dir: &Path, target: &Path) -> PathBuf {
    let from = from_dir
        .canonicalize()
        .unwrap_or_else(|_| from_dir.to_path_buf());
    let target = target
        .canonicalize()
        .unwrap_or_else(|_| target.to_path_buf());
    let Some((from_root, from_parts)) = path_parts(&from) else {
        return target;
    };
    let Some((target_root, target_parts)) = path_parts(&target) else {
        return target;
    };
    if from_root != target_root {
        return target;
    }

    let mut common = 0;
    while common < from_parts.len()
        && common < target_parts.len()
        && from_parts[common] == target_parts[common]
    {
        common += 1;
    }

    let mut rel = PathBuf::new();
    for _ in common..from_parts.len() {
        rel.push("..");
    }
    for part in target_parts.iter().skip(common) {
        rel.push(part);
    }
    if rel.as_os_str().is_empty() {
        rel.push(".");
    }
    rel
}

fn absolute_path(path: &Path) -> RenderResult<PathBuf> {
    Ok(if path.is_absolute() {
        path.to_path_buf()
    } else {
        std::env::current_dir()
            .map_err(|error| RenderError::Io {
                what: format!("resolve current directory: {error}"),
            })?
            .join(path)
    })
}

fn resolved_location(path: &Path) -> RenderResult<PathBuf> {
    let absolute = absolute_path(path)?;
    enum MissingComponent {
        Normal(std::ffi::OsString),
        Parent,
        Current,
    }
    let mut cursor = absolute.as_path();
    let mut suffix = Vec::new();
    loop {
        match std::fs::canonicalize(cursor) {
            Ok(mut resolved) => {
                for component in suffix.iter().rev() {
                    match component {
                        MissingComponent::Normal(name) => resolved.push(name),
                        MissingComponent::Parent => {
                            if !resolved.pop() {
                                return Err(RenderError::Io {
                                    what: format!(
                                        "path escapes its filesystem root: {}",
                                        path.display()
                                    ),
                                });
                            }
                        }
                        MissingComponent::Current => {}
                    }
                }
                return Ok(resolved);
            }
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => {
                let component = cursor
                    .components()
                    .next_back()
                    .ok_or_else(|| RenderError::Io {
                        what: format!(
                            "could not resolve an existing ancestor for {}",
                            path.display()
                        ),
                    })?;
                suffix.push(match component {
                    std::path::Component::Normal(name) => {
                        MissingComponent::Normal(name.to_os_string())
                    }
                    std::path::Component::ParentDir => MissingComponent::Parent,
                    std::path::Component::CurDir => MissingComponent::Current,
                    std::path::Component::Prefix(_) | std::path::Component::RootDir => {
                        return Err(RenderError::Io {
                            what: format!(
                                "could not resolve an existing ancestor for {}",
                                path.display()
                            ),
                        });
                    }
                });
                cursor = cursor.parent().ok_or_else(|| RenderError::Io {
                    what: format!(
                        "could not resolve an existing ancestor for {}",
                        path.display()
                    ),
                })?;
            }
            Err(error) => {
                return Err(RenderError::Io {
                    what: format!("canonicalize({}): {error}", cursor.display()),
                });
            }
        }
    }
}

fn require_render_paths_disjoint(
    output_dir: &Path,
    proof_sources_dir: Option<&Path>,
    native_policy_dir: Option<&Path>,
) -> RenderResult<()> {
    let output = resolved_location(output_dir)?;
    let mut package_dirs = BTreeSet::new();
    package_dirs.extend(proof_sources_dir);
    package_dirs.extend(native_policy_dir);
    for package_dir in package_dirs {
        let package_dir = resolved_location(package_dir)?;
        if output.starts_with(&package_dir) || package_dir.starts_with(&output) {
            return Err(RenderError::Io {
                what: format!(
                    "render output and package Lean directories must be disjoint: {} and {}",
                    output.display(),
                    package_dir.display()
                ),
            });
        }
    }
    Ok(())
}

fn collect_source_proof_roots(
    dir: &Path,
    prefix: Vec<String>,
    require_proofs_suffix: bool,
    roots: &mut std::collections::BTreeSet<String>,
) -> RenderResult<()> {
    let mut entries = std::fs::read_dir(dir)
        .map_err(|e| RenderError::Io {
            what: format!("read_dir({}): {}", dir.display(), e),
        })?
        .collect::<Result<Vec<_>, _>>()
        .map_err(|e| RenderError::Io {
            what: format!("read_dir entry under {}: {}", dir.display(), e),
        })?;
    entries.sort_by_key(|entry| entry.file_name());
    for entry in entries {
        let path = entry.path();
        let name = entry.file_name().to_string_lossy().to_string();
        let metadata = std::fs::symlink_metadata(&path).map_err(|error| RenderError::Io {
            what: format!("metadata({}): {error}", path.display()),
        })?;
        if metadata.file_type().is_symlink() {
            return Err(RenderError::Io {
                what: format!(
                    "proof overlay entries must not be symlinks: {}",
                    path.display()
                ),
            });
        }
        if metadata.is_dir() {
            let mut nested = prefix.clone();
            nested.push(name);
            collect_source_proof_roots(&path, nested, require_proofs_suffix, roots)?;
            continue;
        }
        if !metadata.is_file() {
            continue;
        }
        if path.extension().and_then(|e| e.to_str()) != Some("lean") {
            continue;
        }
        let Some(stem) = path.file_stem().and_then(|s| s.to_str()) else {
            continue;
        };
        if require_proofs_suffix && !stem.ends_with("_Proofs") {
            continue;
        }
        let mut module = prefix.clone();
        module.push(stem.to_string());
        roots.insert(module.join("."));
    }
    Ok(())
}
/// Write `obligations.toml` at the output root: one `[[obligation]]`
/// entry per stage-12 obligation -- the machine-readable index that
/// `sui-lean --audit-proofs` joins against the built Lean environment
/// (`lean_decl` names the declaration whose axiom footprint gets
/// checked: a proof-module theorem for prove obligations, with legacy
/// top-level declarations still accepted, or the namespaced
/// `<name>_holds` axiom for trusted ones). Sorted by (module, name) for
/// deterministic diffs; regenerated every render.
fn write_obligations_manifest(
    program: &Program,
    output_dir: &Path,
    proof_declaration_fingerprints: &BTreeMap<(String, String), String>,
) -> RenderResult<()> {
    use std::fs;
    let namespace_of = |mid: crate::ir::ModId| -> String {
        let module = program.modules.get(&mid).expect("obligation module");
        let pkg = if module.package_name.is_empty() {
            "NewPipeline"
        } else {
            module.package_name.as_str()
        };
        self::escape::module_render_namespace(pkg, &module.name)
    };
    let mut obligations: Vec<&crate::ir::Function> = program
        .functions
        .values()
        .filter(|f| {
            matches!(
                f.kind,
                crate::ir::FunctionKind::Theorem { .. } | crate::ir::FunctionKind::Axiom { .. }
            )
        })
        .collect();
    obligations.sort_by_key(|f| (namespace_of(f.module), f.name.clone()));

    // Declared `#[spec(prove)]` wrappers that produced NO obligation at
    // all. Every one is verification someone asked for that nothing in
    // the corpus proves, and until this list existed the class was
    // invisible: `proof_status.toml` had no column that could be
    // non-zero for it, so seven sui-system declarations (four of them
    // carrying a manual verification stamp) hid under a `0 missing`
    // header. Derived here rather than plumbed: the manifest is the one
    // place that sees both the prove roster and everything stage 12
    // emitted.
    //
    // THE RECONCILIATION IS TOTAL. The roster is
    // `spec_to_impl + targetless_prove_specs + unmapped_prove_specs`,
    // which stage 2 fills as a partition of the declared prove targets,
    // so every request either appears above as an `[[obligation]]` or
    // here as a `[[spec_no_obligation]]` -- never neither. The two
    // fallbacks below are what closes the last routes: a wrapper stage 2
    // paired but that never grew a translated body is named from
    // `prove_spec_names` instead of being skipped, and a wrapper with no
    // `FunId` at all arrives pre-named in `unmapped_prove_specs`. Both
    // used to be stderr lines, and a stderr line inside a 25-minute gate
    // log is not a record.
    let mut sourced: std::collections::BTreeSet<crate::ir::FunId> = Default::default();
    for f in program.functions.values() {
        if let crate::ir::FunctionKind::Theorem { source, .. } = f.kind {
            sourced.insert(source);
        }
    }
    let mut no_obligation: Vec<(String, String)> = program
        .unmapped_prove_specs
        .iter()
        .cloned()
        .collect::<Vec<_>>();
    for spec_fid in program
        .spec_to_impl
        .keys()
        .copied()
        .chain(program.targetless_prove_specs.iter().copied())
    {
        if sourced.contains(&spec_fid) {
            continue;
        }
        let source = match program.functions.get(&spec_fid) {
            Some(spec) => {
                let module = &program.modules[&spec.module];
                format!("{}::{}::{}", module.package_name, module.name, spec.name)
            }
            None => match program.prove_spec_names.get(&spec_fid) {
                Some(name) => name.clone(),
                None => format!("<untranslated prove spec fid {spec_fid}>"),
            },
        };
        let reason = if program.targetless_prove_specs.contains(&spec_fid) {
            "no_target_and_no_ensures"
        } else {
            "no_ensures"
        };
        no_obligation.push((source, reason.to_string()));
    }
    no_obligation.sort();
    no_obligation.dedup();

    let mut out = String::from(
        "# Generated by sui-lean --new-pipeline. One [[obligation]] per stage-12\n\
         # proof obligation; `lean_decl` names the Lean declaration whose axiom\n\
         # footprint `sui-lean --audit-proofs` checks. Regenerated every render.\n\
         # A spec_no_obligation entry names a declared `#[spec(prove)]` wrapper\n\
         # that emitted NO obligation -- verification that was asked for and\n\
         # that nothing proves. Those entries feed the `spec_no_obligation`\n\
         # counter in proof_status.toml; its value being 0 is the point.\n",
    );
    for (source, reason) in &no_obligation {
        out.push_str("\n[[spec_no_obligation]]\n");
        out.push_str(&format!("source = \"{}\"\n", toml_basic_string(source)));
        out.push_str(&format!("reason = \"{}\"\n", reason));
    }
    for f in obligations {
        let namespace = namespace_of(f.module);
        let escaped = self::escape::escape_identifier(&f.name);
        let (target_fid, source_fid, kind, reason) = match f.kind {
            crate::ir::FunctionKind::Theorem { target, source } => {
                (target, source, "theorem", None)
            }
            crate::ir::FunctionKind::Axiom {
                target,
                source,
                reason,
            } => (
                target,
                source,
                "trusted_axiom",
                Some(match reason {
                    crate::ir::TrustReason::NonProve => "non_prove",
                    crate::ir::TrustReason::Skip => "skip",
                    crate::ir::TrustReason::Boogie => "run_on_boogie",
                }),
            ),
            _ => unreachable!("filtered to Theorem | Axiom above"),
        };
        let lean_decl = if kind == "theorem" {
            escaped.clone()
        } else {
            format!(
                "{}.{}",
                namespace,
                self::escape::escape_identifier(&crate::ir::names::axiom_holds_name(&f.name))
            )
        };
        let callee = program
            .lookup_callee(target_fid)
            .expect("obligation target must resolve to a function or native");
        let target = format!(
            "{}.{}",
            namespace_of(callee.module()),
            self::escape::escape_identifier(callee.name())
        );
        let target_module =
            program
                .modules
                .get(&callee.module())
                .ok_or(RenderError::UnknownModId {
                    id: callee.module(),
                })?;
        let target_source = format!(
            "{}::{}::{}",
            target_module.package_name,
            target_module.name,
            callee.name()
        );
        let source = program
            .functions
            .get(&source_fid)
            .map(|source| {
                let module = &program.modules[&source.module];
                format!("{}::{}::{}", module.package_name, module.name, source.name)
            })
            .ok_or(RenderError::UnknownFunId { id: source_fid })?;
        out.push_str("\n[[obligation]]\n");
        out.push_str(&format!("name = \"{}\"\n", toml_basic_string(&escaped)));
        out.push_str(&format!("ir_name = \"{}\"\n", toml_basic_string(&f.name)));
        out.push_str(&format!("kind = \"{}\"\n", kind));
        if let Some(reason) = reason {
            out.push_str(&format!("reason = \"{}\"\n", reason));
        }
        out.push_str(&format!("module = \"{}\"\n", toml_basic_string(&namespace)));
        out.push_str(&format!(
            "prop = \"{}.{}\"\n",
            toml_basic_string(&namespace),
            toml_basic_string(&escaped)
        ));
        out.push_str(&format!(
            "lean_decl = \"{}\"\n",
            toml_basic_string(&lean_decl)
        ));
        if kind == "theorem" {
            let declaration_fingerprint = proof_declaration_fingerprints
                .get(&(namespace.clone(), escaped.clone()))
                .ok_or_else(|| RenderError::Io {
                    what: format!(
                        "missing proof declaration fingerprint for {namespace}.{escaped}"
                    ),
                })?;
            out.push_str(&format!(
                "proof_declaration_sha256 = \"{}\"\n",
                toml_basic_string(declaration_fingerprint)
            ));
        }
        out.push_str(&format!("target = \"{}\"\n", toml_basic_string(&target)));
        out.push_str(&format!(
            "target_source = \"{}\"\n",
            toml_basic_string(&target_source)
        ));
        out.push_str(&format!("source = \"{}\"\n", toml_basic_string(&source)));
    }
    let path = output_dir.join("obligations.toml");
    fs::write(&path, &out).map_err(|e| RenderError::Io {
        what: format!("write({}): {}", path.display(), e),
    })?;
    Ok(())
}

fn write_test_declarations_manifest(program: &Program, output_dir: &Path) -> RenderResult<()> {
    let world_id =
        program.struct_id_by_qualified_name(crate::stage_04_effects::WORLD_QUALIFIED_NAME);
    let mut declarations = Vec::new();
    for function in program.functions.values() {
        let crate::ir::FunctionKind::Spec {
            kind: crate::ir::SpecKind::Aborts,
            target,
        } = function.kind
        else {
            continue;
        };
        let target_function = program
            .functions
            .get(&target)
            .ok_or_else(|| RenderError::Io {
                what: format!(
                    "cannot index test declaration `{}`: aborts target {target} is missing",
                    function.name
                ),
            })?;
        if target_function.module != function.module
            || function.name != format!("{}.aborts", target_function.name)
        {
            return Err(RenderError::Io {
                what: format!(
                    "cannot index test declaration `{}`: it is not the canonical aborts companion for target `{}`",
                    function.name, target_function.name
                ),
            });
        }
        let module = program
            .modules
            .get(&function.module)
            .ok_or(RenderError::UnknownModId {
                id: function.module,
            })?;
        let addressed_module =
            crate::ir::canonical_addressed_module(module).ok_or_else(|| RenderError::Io {
                what: format!(
                    "cannot index test declaration `{}`: module `{}` has no valid address",
                    target_function.name, module.name
                ),
            })?;
        let location = module_render_location(&module.package_name, &module.name);
        let needs_world = world_id.is_some_and(|world_id| {
            function.signature.params.iter().any(|param| {
                matches!(
                    &param.ty,
                    crate::ir::Type::Struct { struct_id, .. } if *struct_id == world_id
                )
            })
        });
        declarations.push(TestDeclaration {
            addressed_module,
            function: target_function.name.clone(),
            import_path: location.import_path,
            lean_declaration: format!(
                "{}.{}",
                location.namespace,
                self::escape::escape_identifier(&function.name)
            ),
            needs_world,
            ghost_param_count: program.ghost_vars.get(&target).map_or(0, Vec::len),
        });
    }
    declarations.sort_by(|left, right| {
        (&left.addressed_module, &left.function).cmp(&(&right.addressed_module, &right.function))
    });
    let manifest = TestDeclarations {
        schema_version: 1,
        declarations,
    };
    let path = output_dir.join(TEST_DECLARATIONS_MANIFEST);
    validate_test_declarations(&manifest, &path)?;
    let contents = toml::to_string_pretty(&manifest).map_err(|error| RenderError::Io {
        what: format!("serialize {TEST_DECLARATIONS_MANIFEST}: {error}"),
    })?;
    std::fs::write(&path, contents).map_err(|error| RenderError::Io {
        what: format!("write({}): {error}", path.display()),
    })
}

/// Escape for a TOML basic string. Lean identifiers are quote-free in
/// practice; escape defensively so the writer can never emit bad TOML.
fn toml_basic_string(s: &str) -> String {
    s.replace('\\', "\\\\").replace('"', "\\\"")
}

/// Discover lakefile roots in the proof overlay (`<package-root>/lean/`).
/// Top-level `.lean` files and files under ordinary subdirs are roots only
/// with the `_Proofs` suffix (other files build as imports of those roots);
/// under `Proofs/` -- the conventional shared-helper dir committed seeds
/// import as `Proofs.*` -- every `.lean` file is a root. The overlay root
/// contains ONLY new-pipeline files (the legacy backend's tree stays at
/// `sources/lean/`, never scanned here; `check_new_pipeline_layout` in
/// sui-lean rejects unmigrated packages before rendering).
fn discover_source_proof_roots(source_dir: &Path) -> RenderResult<Vec<String>> {
    match std::fs::symlink_metadata(source_dir) {
        Ok(metadata) if metadata.file_type().is_symlink() || !metadata.is_dir() => {
            return Err(RenderError::Io {
                what: format!(
                    "proof overlay directory must be a non-symlink directory: {}",
                    source_dir.display()
                ),
            });
        }
        Ok(_) => {}
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => return Ok(vec![]),
        Err(error) => {
            return Err(RenderError::Io {
                what: format!("metadata({}): {error}", source_dir.display()),
            });
        }
    }

    let mut roots = std::collections::BTreeSet::new();
    let mut entries = std::fs::read_dir(source_dir)
        .map_err(|e| RenderError::Io {
            what: format!("read_dir({}): {}", source_dir.display(), e),
        })?
        .collect::<Result<Vec<_>, _>>()
        .map_err(|e| RenderError::Io {
            what: format!("read_dir entry under {}: {}", source_dir.display(), e),
        })?;
    entries.sort_by_key(|entry| entry.file_name());
    for entry in entries {
        let path = entry.path();
        let name = entry.file_name().to_string_lossy().to_string();
        let metadata = std::fs::symlink_metadata(&path).map_err(|error| RenderError::Io {
            what: format!("metadata({}): {error}", path.display()),
        })?;
        if metadata.file_type().is_symlink() {
            return Err(RenderError::Io {
                what: format!(
                    "proof overlay entries must not be symlinks: {}",
                    path.display()
                ),
            });
        }
        if metadata.is_dir() {
            // `lean/natives/` holds user-declared-native definition files
            // consumed by the natives-copy step in
            // `render_program_to_dir`, not proof roots.
            if name == "natives" {
                continue;
            }
            let require_suffix = name != "Proofs";
            collect_source_proof_roots(&path, vec![name.clone()], require_suffix, &mut roots)?;
            continue;
        }
        if !metadata.is_file() {
            continue;
        }
        if path.extension().and_then(|e| e.to_str()) != Some("lean") {
            continue;
        }
        let Some(stem) = path.file_stem().and_then(|s| s.to_str()) else {
            continue;
        };
        if stem.ends_with("_Proofs") {
            roots.insert(stem.to_string());
        }
    }

    Ok(roots.into_iter().collect())
}

const PROOF_FINGERPRINT_MARKER: &str = "sui-lean:obligation-fingerprint";
const PROOF_FINGERPRINT_VERSION: &str = "v1";
const PROOF_SOURCE_MARKER: &str = "sui-lean:proof-source";
const PROOF_SOURCE_VERSION: &str = "v1";

#[derive(Clone)]
struct ProofStub {
    name: String,
    source: String,
    fingerprint: String,
    generated_prop: String,
    generated_statement: String,
    proof_declaration_sha256: String,
}

struct ProofFilePlan {
    body: String,
    required_import: String,
    stubs: Vec<ProofStub>,
}

struct SourceProofUpdate {
    path: PathBuf,
    root: String,
    plan: ProofFilePlan,
}

fn proof_shard_stem(name: &str) -> String {
    let mut stem = String::with_capacity(name.len());
    for ch in name.chars() {
        if ch.is_ascii_alphanumeric() || ch == '_' || ch == '\'' {
            stem.push(ch);
        } else {
            stem.push('_');
        }
    }
    if stem
        .chars()
        .next()
        .is_none_or(|ch| !ch.is_ascii_alphabetic() && ch != '_')
    {
        stem.insert(0, '_');
    }
    stem
}

fn render_proof_stub(
    fid: FunId,
    function: &crate::ir::Function,
    context: &self::context::RenderContext<'_>,
) -> RenderResult<String> {
    let mut writer = LeanWriter::new(String::new());
    self::function::render_function(
        function,
        fid,
        context,
        None,
        &mut writer,
        false,
        true,
        false,
        None,
    )?;
    Ok(writer.into_inner())
}

fn render_obligation_definition(
    fid: FunId,
    function: &crate::ir::Function,
    context: &self::context::RenderContext<'_>,
    module_namespace: &str,
) -> RenderResult<String> {
    let mut writer = LeanWriter::new(String::new());
    self::function::render_function(
        function,
        fid,
        context,
        Some(module_namespace),
        &mut writer,
        false,
        false,
        false,
        None,
    )?;
    Ok(writer.into_inner())
}

fn obligation_statement_fingerprint(generated_prop: &str, declaration: &str) -> String {
    let mut hasher = Sha256::new();
    hasher.update(b"sui-lean-obligation-statement\0");
    hasher.update(PROOF_FINGERPRINT_VERSION.as_bytes());
    hasher.update(b"\0");
    hasher.update(generated_prop.as_bytes());
    hasher.update(b"\0");
    hasher.update(declaration.as_bytes());
    let mut fingerprint = String::with_capacity(64);
    for byte in hasher.finalize() {
        write!(&mut fingerprint, "{byte:02x}").expect("writing SHA-256 hex to String");
    }
    fingerprint
}

fn proof_declaration_fingerprint(name: &str, proof: &str) -> RenderResult<String> {
    let prefix = format!("theorem _root_.{name}");
    let suffix = proof.strip_prefix(&prefix).ok_or_else(|| RenderError::Io {
        what: format!("generated proof stub for `{name}` did not begin with `{prefix}`"),
    })?;
    let assignment_end =
        suffix
            .rfind(":=")
            .map(|offset| offset + 2)
            .ok_or_else(|| RenderError::Io {
                what: format!("generated proof stub for `{name}` has no theorem assignment"),
            })?;
    let mut hasher = Sha256::new();
    hasher.update(b"sui-lean-proof-declaration-v1\0");
    hasher.update(&suffix.as_bytes()[..assignment_end]);
    let mut fingerprint = String::with_capacity(64);
    for byte in hasher.finalize() {
        write!(&mut fingerprint, "{byte:02x}").expect("writing SHA-256 hex to String");
    }
    Ok(fingerprint)
}

fn proof_fingerprint_marker(name: &str, fingerprint: &str) -> String {
    format!(
        "-- {PROOF_FINGERPRINT_MARKER} {PROOF_FINGERPRINT_VERSION} name={name} sha256={fingerprint}"
    )
}

fn durable_proof_stub_source(
    name: &str,
    fingerprint: &str,
    proof_namespace: &str,
    proof: &str,
) -> RenderResult<String> {
    let unqualified = format!("theorem _root_.{name}");
    let suffix = proof
        .strip_prefix(&unqualified)
        .ok_or_else(|| RenderError::Io {
            what: format!("generated proof stub for `{name}` did not begin with `{unqualified}`"),
        })?;
    Ok(format!(
        "{}\nnamespace {proof_namespace}\nset_option maxRecDepth 4096 in\nset_option maxHeartbeats 8000000 in\nset_option synthInstance.maxHeartbeats 4000000 in\nset_option linter.unusedVariables false in\ntheorem {name}{suffix}end {proof_namespace}\nexport {proof_namespace} ({name})\n\n",
        proof_fingerprint_marker(name, fingerprint)
    ))
}

fn proof_file_plan(
    package: &str,
    namespace: &str,
    module_namespace: &str,
    proof_namespace: Option<&str>,
    theorem_fns: &[(&FunId, &crate::ir::Function)],
    context: &self::context::RenderContext<'_>,
) -> RenderResult<ProofFilePlan> {
    let required_import = format!("{package}.{namespace}");
    let mut body = match proof_namespace {
        Some(_) => {
            format!("-- {PROOF_SOURCE_MARKER} {PROOF_SOURCE_VERSION}\nimport {required_import}\n\n")
        }
        None => format!(
            "import {required_import}\n\nset_option maxRecDepth 4096\nset_option maxHeartbeats 8000000\nset_option synthInstance.maxHeartbeats 4000000\nset_option linter.unusedVariables false\n\n"
        ),
    };
    let mut stubs = Vec::with_capacity(theorem_fns.len());
    for (fid, function) in theorem_fns {
        let name = escape::escape_identifier(&function.name);
        let generated_prop = format!("{module_namespace}.{name}");
        let declaration = render_obligation_definition(**fid, function, context, module_namespace)?;
        let fingerprint = obligation_statement_fingerprint(&generated_prop, &declaration);
        let proof = render_proof_stub(**fid, function, context)?;
        let proof_declaration_sha256 = proof_declaration_fingerprint(&name, &proof)?;
        let source = match proof_namespace {
            Some(proof_namespace) => {
                durable_proof_stub_source(&name, &fingerprint, proof_namespace, &proof)?
            }
            None => format!("{}\n{proof}", proof_fingerprint_marker(&name, &fingerprint)),
        };
        body.push_str(&source);
        stubs.push(ProofStub {
            name,
            source,
            fingerprint,
            generated_prop,
            generated_statement: declaration,
            proof_declaration_sha256,
        });
    }
    Ok(ProofFilePlan {
        body,
        required_import,
        stubs,
    })
}

fn standalone_proof_metadata_lines(input: &str) -> impl Iterator<Item = &str> {
    input
        .lines()
        .filter_map(|line| line.trim_start().strip_prefix("--"))
}

fn proof_metadata_error(path: &Path, what: impl AsRef<str>) -> RenderError {
    RenderError::Io {
        what: format!(
            "invalid proof metadata in {}: {}",
            path.display(),
            what.as_ref()
        ),
    }
}

struct ProofMetadata {
    fingerprints: BTreeMap<String, String>,
    managed: bool,
}

fn proof_metadata(path: &Path, source: &str) -> RenderResult<ProofMetadata> {
    let mut fingerprints = BTreeMap::new();
    let mut managed = false;
    for comment in standalone_proof_metadata_lines(source) {
        let comment = comment.trim();
        if let Some(after_marker) = comment.strip_prefix(PROOF_SOURCE_MARKER) {
            if after_marker.strip_prefix(' ') != Some(PROOF_SOURCE_VERSION) {
                return Err(proof_metadata_error(
                    path,
                    format!("malformed proof-source marker `{comment}`"),
                ));
            }
            if managed {
                return Err(proof_metadata_error(path, "duplicate proof-source marker"));
            }
            managed = true;
            continue;
        }
        let Some(after_marker) = comment.strip_prefix(PROOF_FINGERPRINT_MARKER) else {
            continue;
        };
        let Some(payload) = after_marker.strip_prefix(' ') else {
            return Err(proof_metadata_error(
                path,
                format!("malformed marker `{comment}`"),
            ));
        };
        if payload.chars().next().is_none_or(|ch| ch.is_whitespace()) {
            return Err(proof_metadata_error(
                path,
                format!("malformed marker `{comment}`"),
            ));
        }
        let mut fields = payload.split_whitespace();
        let version = fields.next();
        let name = fields.next().and_then(|field| field.strip_prefix("name="));
        let fingerprint = fields
            .next()
            .and_then(|field| field.strip_prefix("sha256="));
        if version != Some(PROOF_FINGERPRINT_VERSION)
            || name.is_none()
            || fingerprint.is_none()
            || fields.next().is_some()
        {
            return Err(proof_metadata_error(
                path,
                format!("malformed marker `{comment}`"),
            ));
        }
        let name = native_models::normalize_lean_name(name.unwrap());
        if name.is_empty() {
            return Err(proof_metadata_error(
                path,
                "marker has an empty obligation name",
            ));
        }
        let fingerprint = fingerprint.unwrap();
        if fingerprint.len() != 64
            || !fingerprint
                .bytes()
                .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
        {
            return Err(proof_metadata_error(
                path,
                format!("marker for `{name}` has a non-canonical SHA-256 digest"),
            ));
        }
        if fingerprints
            .insert(name.clone(), fingerprint.to_string())
            .is_some()
        {
            return Err(proof_metadata_error(
                path,
                format!("duplicate marker for `{name}`"),
            ));
        }
    }
    Ok(ProofMetadata {
        fingerprints,
        managed,
    })
}

/// Bytes Lean will keep reading as part of the same identifier. Twin of
/// `is_lean_identifier_byte` in `sui-lean::audit`; the two crates cannot share
/// it (sui-lean depends on lean-pipeline, not the other way round), so the rule
/// genuinely exists twice and must be changed in both places.
fn is_lean_identifier_byte(byte: u8) -> bool {
    byte.is_ascii_alphanumeric() || matches!(byte, b'_' | b'\'' | b'?' | b'!') || !byte.is_ascii()
}

/// True when `name` occurs in `line` as a WHOLE Lean identifier rather than as
/// a substring of a longer one. A namespace prefix still counts -- `.` is not
/// an identifier byte, so `Pkg.Mod.swap_correct` is an occurrence of
/// `swap_correct` -- which is the intent: that line does reference the
/// obligation.
fn line_references_lean_name(line: &str, name: &str) -> bool {
    let quoted = format!("«{name}»");
    if line.contains(&quoted) {
        return true;
    }
    line.match_indices(name).any(|(index, _)| {
        let bytes = line.as_bytes();
        let before = index.checked_sub(1).map(|offset| bytes[offset]);
        let after = bytes.get(index + name.len()).copied();
        !before.is_some_and(is_lean_identifier_byte) && !after.is_some_and(is_lean_identifier_byte)
    })
}

/// Conservative "is this obligation already spoken for?" scan over an UNMANAGED
/// legacy proof file, which carries no fingerprint markers to consult. It
/// deliberately reads comments and strings too: over-suppressing is safe
/// because `--audit-proofs` then reports the declaration as `missing`.
///
/// The match must nonetheless be a whole-identifier one. A plain
/// `line.contains(name)` makes every obligation whose name is a proper
/// SUBSTRING of a surviving proof's name permanently unstubbable: on bluefin a
/// single live `theorem repay_flash_swap_correct` suppressed both
/// `flash_swap_correct` and `swap_correct` for good, and 22 of that corpus's
/// 608 theorem obligations sit on the same latent trap. And the failure is not
/// the safe direction it looks like -- `missing` is an audit INTEGRITY failure
/// that only surfaces when someone runs `--audit-proofs`, so in between the
/// obligation is simply unanswered and silent.
fn proof_name_occurs_outside_metadata(source: &str, name: &str) -> bool {
    source.lines().any(|line| {
        let is_metadata = line
            .trim_start()
            .strip_prefix("--")
            .map(str::trim_start)
            .is_some_and(|comment| {
                comment.starts_with(PROOF_SOURCE_MARKER)
                    || comment.starts_with(PROOF_FINGERPRINT_MARKER)
            });
        !is_metadata && line_references_lean_name(line, name)
    })
}

fn skip_proof_header_block_comment(path: &Path, source: &str, start: usize) -> RenderResult<usize> {
    let bytes = source.as_bytes();
    let mut offset = start + 2;
    let mut depth = 1usize;
    while offset < bytes.len() {
        if bytes[offset..].starts_with(b"/-") {
            depth += 1;
            offset += 2;
        } else if bytes[offset..].starts_with(b"-/") {
            depth -= 1;
            offset += 2;
            if depth == 0 {
                return Ok(offset);
            }
        } else {
            offset += 1;
        }
    }
    Err(proof_metadata_error(
        path,
        "cannot safely locate the import header because it contains an unterminated block comment",
    ))
}

fn skip_proof_header_trivia(path: &Path, source: &str, mut offset: usize) -> RenderResult<usize> {
    let bytes = source.as_bytes();
    loop {
        while offset < bytes.len() && bytes[offset].is_ascii_whitespace() {
            offset += 1;
        }
        if bytes[offset..].starts_with(b"--") {
            offset += 2;
            while offset < bytes.len() && bytes[offset] != b'\n' {
                offset += 1;
            }
            continue;
        }
        if bytes[offset..].starts_with(b"/-") {
            offset = skip_proof_header_block_comment(path, source, offset)?;
            continue;
        }
        return Ok(offset);
    }
}

fn is_proof_import_keyword(source: &str, offset: usize) -> bool {
    let bytes = source.as_bytes();
    if !bytes[offset..].starts_with(b"import") {
        return false;
    }
    bytes
        .get(offset + "import".len())
        .is_some_and(|byte| byte.is_ascii_whitespace() || *byte == b'/')
}

fn valid_proof_import_name(name: &str) -> bool {
    name.split('.').all(|segment| {
        let mut bytes = segment.bytes();
        bytes
            .next()
            .is_some_and(|byte| byte.is_ascii_alphabetic() || byte == b'_')
            && bytes.all(|byte| byte.is_ascii_alphanumeric() || matches!(byte, b'_' | b'\''))
    })
}

fn parse_proof_import(
    path: &Path,
    source: &str,
    command_start: usize,
) -> RenderResult<(String, usize)> {
    let bytes = source.as_bytes();
    let mut offset = command_start + "import".len();
    let mut saw_separator = false;
    loop {
        while offset < bytes.len() && matches!(bytes[offset], b' ' | b'\t' | b'\r' | b'\n') {
            saw_separator = true;
            offset += 1;
        }
        if bytes[offset..].starts_with(b"/-") {
            saw_separator = true;
            offset = skip_proof_header_block_comment(path, source, offset)?;
            continue;
        }
        break;
    }
    if !saw_separator || offset == bytes.len() || bytes[offset..].starts_with(b"--") {
        return Err(proof_metadata_error(
            path,
            "cannot safely locate the import header because it contains a malformed import command",
        ));
    }
    let name_start = offset;
    while offset < bytes.len()
        && !bytes[offset].is_ascii_whitespace()
        && !bytes[offset..].starts_with(b"--")
        && !bytes[offset..].starts_with(b"/-")
    {
        offset += 1;
    }
    let name = &source[name_start..offset];
    if !valid_proof_import_name(name) {
        return Err(proof_metadata_error(
            path,
            format!(
                "cannot safely locate the import header because `{name}` is not a supported module import"
            ),
        ));
    }
    loop {
        while offset < bytes.len() && matches!(bytes[offset], b' ' | b'\t' | b'\r') {
            offset += 1;
        }
        if offset == bytes.len() {
            return Ok((name.to_string(), offset));
        }
        if bytes[offset] == b'\n' {
            return Ok((name.to_string(), offset + 1));
        }
        if bytes[offset..].starts_with(b"--") {
            while offset < bytes.len() && bytes[offset] != b'\n' {
                offset += 1;
            }
            return Ok((name.to_string(), offset + usize::from(offset < bytes.len())));
        }
        if bytes[offset..].starts_with(b"/-") {
            let comment_start = offset;
            offset = skip_proof_header_block_comment(path, source, offset)?;
            if source[comment_start..offset].contains('\n') {
                return Ok((name.to_string(), offset));
            }
            continue;
        }
        return Err(proof_metadata_error(
            path,
            "cannot safely locate the import header because an import command has trailing syntax",
        ));
    }
}

/// Locate the end of the real leading Lean import header without interpreting
/// import-shaped text inside comments or later commands. Reconciliation stops
/// at the first non-import command and fails closed on ambiguous header syntax.
fn proof_stub_insertion_offset(
    path: &Path,
    source: &str,
    required_import: &str,
) -> RenderResult<usize> {
    let mut saw_required_import = false;
    let mut last_import_end = None;
    let mut offset = 0;
    loop {
        offset = skip_proof_header_trivia(path, source, offset)?;
        if offset == source.len() || !is_proof_import_keyword(source, offset) {
            break;
        }
        let (import, import_end) = parse_proof_import(path, source, offset)?;
        saw_required_import |= import == required_import;
        last_import_end = Some(import_end);
        offset = import_end;
    }
    if !saw_required_import {
        return Err(proof_metadata_error(
            path,
            format!(
                "cannot safely insert a missing proof stub because the source does not directly import `{required_import}`"
            ),
        ));
    }
    Ok(last_import_end.expect("required import has an insertion boundary"))
}

fn check_proof_statement_drift(
    path: &Path,
    plan: &ProofFilePlan,
    fingerprints: &BTreeMap<String, String>,
) -> RenderResult<()> {
    for stub in &plan.stubs {
        let normalized_name = native_models::normalize_lean_name(&stub.name);
        if let Some(recorded) = fingerprints.get(&normalized_name) {
            if recorded != &stub.fingerprint {
                return Err(RenderError::ProofStatementDrift {
                    path: path.display().to_string(),
                    obligation: stub.name.clone(),
                    recorded_fingerprint: format!("sha256:{recorded}"),
                    generated_fingerprint: format!("sha256:{}", stub.fingerprint),
                    generated_prop: stub.generated_prop.clone(),
                    generated_statement: stub.generated_statement.clone(),
                    replacement_marker: proof_fingerprint_marker(&stub.name, &stub.fingerprint),
                });
            }
        }
    }
    Ok(())
}

fn updated_source_proof(
    path: &Path,
    existing: &str,
    plan: &ProofFilePlan,
    metadata: &ProofMetadata,
) -> RenderResult<Option<Vec<u8>>> {
    check_proof_statement_drift(path, plan, &metadata.fingerprints)?;
    let mut missing = Vec::new();
    for stub in &plan.stubs {
        let normalized_name = native_models::normalize_lean_name(&stub.name);
        if metadata.fingerprints.contains_key(&normalized_name) {
            continue;
        }
        if proof_name_occurs_outside_metadata(existing, &normalized_name) {
            if metadata.managed {
                return Err(proof_metadata_error(
                    path,
                    format!(
                        "managed proof source references obligation `{}` without its fingerprint marker; restore `{}`",
                        stub.name,
                        proof_fingerprint_marker(&stub.name, &stub.fingerprint)
                    ),
                ));
            }
            continue;
        }
        missing.push(stub);
    }
    if missing.is_empty() {
        return Ok(None);
    }
    let insertion = proof_stub_insertion_offset(path, existing, plan.required_import.as_str())?;
    let added_len = missing.iter().map(|stub| stub.source.len()).sum::<usize>();
    let mut updated = Vec::with_capacity(existing.len() + added_len + 2);
    updated.extend_from_slice(&existing.as_bytes()[..insertion]);
    if insertion > 0 && !existing[..insertion].ends_with('\n') {
        updated.push(b'\n');
    }
    updated.push(b'\n');
    for stub in missing {
        updated.extend_from_slice(stub.source.as_bytes());
    }
    updated.extend_from_slice(&existing.as_bytes()[insertion..]);
    Ok(Some(updated))
}

fn write_proof_atomically(
    path: &Path,
    contents: &[u8],
    permissions: Option<std::fs::Permissions>,
    replace: bool,
) -> RenderResult<()> {
    let parent = path.parent().ok_or_else(|| RenderError::Io {
        what: format!("proof path has no parent: {}", path.display()),
    })?;
    let mut temporary =
        tempfile::NamedTempFile::new_in(parent).map_err(|error| RenderError::Io {
            what: format!("create temporary proof under {}: {error}", parent.display()),
        })?;
    std::io::Write::write_all(&mut temporary, contents).map_err(|error| RenderError::Io {
        what: format!("write temporary proof for {}: {error}", path.display()),
    })?;
    std::io::Write::flush(&mut temporary).map_err(|error| RenderError::Io {
        what: format!("flush temporary proof for {}: {error}", path.display()),
    })?;
    if let Some(permissions) = permissions {
        temporary
            .as_file()
            .set_permissions(permissions)
            .map_err(|error| RenderError::Io {
                what: format!("set permissions for {}: {error}", path.display()),
            })?;
    } else {
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            temporary
                .as_file()
                .set_permissions(std::fs::Permissions::from_mode(0o644))
                .map_err(|error| RenderError::Io {
                    what: format!("set permissions for {}: {error}", path.display()),
                })?;
        }
    }
    temporary
        .as_file()
        .sync_all()
        .map_err(|error| RenderError::Io {
            what: format!("sync temporary proof for {}: {error}", path.display()),
        })?;
    let result = if replace {
        temporary.persist(path)
    } else {
        temporary.persist_noclobber(path)
    };
    result.map(|_| ()).map_err(|error| RenderError::Io {
        what: format!("commit proof {}: {}", path.display(), error.error),
    })
}

fn read_source_proof(path: &Path) -> RenderResult<Option<(std::fs::Metadata, String)>> {
    let metadata = match std::fs::symlink_metadata(path) {
        Ok(metadata) if metadata.file_type().is_symlink() => {
            return Err(RenderError::Io {
                what: format!("proof source must not be a symlink: {}", path.display()),
            });
        }
        Ok(metadata) if !metadata.is_file() => {
            return Err(RenderError::Io {
                what: format!("proof source must be a regular file: {}", path.display()),
            });
        }
        Ok(metadata) => metadata,
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => return Ok(None),
        Err(error) => {
            return Err(RenderError::Io {
                what: format!("metadata({}): {error}", path.display()),
            });
        }
    };
    let source = std::fs::read_to_string(path).map_err(|error| RenderError::Io {
        what: format!("read({}): {error}", path.display()),
    })?;
    Ok(Some((metadata, source)))
}

struct PlannedSourceProofWrite {
    path: PathBuf,
    original: Option<Vec<u8>>,
    permissions: Option<std::fs::Permissions>,
    contents: Option<Vec<u8>>,
}

fn require_source_proof_state(
    path: &Path,
    expected: Option<&[u8]>,
    context: &str,
) -> RenderResult<()> {
    let current = read_source_proof(path)?;
    let matches = match (expected, current.as_ref()) {
        (None, None) => true,
        (Some(expected), Some((_, source))) => expected == source.as_bytes(),
        _ => false,
    };
    if matches {
        Ok(())
    } else {
        Err(RenderError::Io {
            what: format!("{context}: proof source changed: {}", path.display()),
        })
    }
}

fn commit_source_proof_write(write: &PlannedSourceProofWrite) -> RenderResult<bool> {
    let Some(contents) = &write.contents else {
        return Ok(false);
    };
    let parent = write.path.parent().ok_or_else(|| RenderError::Io {
        what: format!("proof path has no parent: {}", write.path.display()),
    })?;
    std::fs::create_dir_all(parent).map_err(|error| RenderError::Io {
        what: format!("create_dir_all({}): {error}", parent.display()),
    })?;
    let lock_path = parent.join(".sui-lean-proof-directory.lock");
    let directory = std::fs::OpenOptions::new()
        .read(true)
        .write(true)
        .create(true)
        .open(&lock_path)
        .map_err(|error| RenderError::Io {
            what: format!("open proof directory lock {}: {error}", lock_path.display()),
        })?;
    fs4::fs_std::FileExt::lock_exclusive(&directory).map_err(|error| RenderError::Io {
        what: format!("lock proof directory {}: {error}", parent.display()),
    })?;

    match (&write.original, read_source_proof(&write.path)?) {
        (Some(original), Some((_, current))) if current.as_bytes() == original => {
            write_proof_atomically(&write.path, contents, write.permissions.clone(), true)?;
        }
        (None, None) => write_proof_atomically(&write.path, contents, None, false)?,
        _ => {
            return Err(RenderError::Io {
                what: format!(
                    "proof changed while planning update: {}",
                    write.path.display()
                ),
            });
        }
    }
    Ok(true)
}

fn rollback_source_proof_write(write: &PlannedSourceProofWrite) -> RenderResult<()> {
    let Some(contents) = &write.contents else {
        return Ok(());
    };
    let current = read_source_proof(&write.path)?;
    let Some((_, current_source)) = current else {
        return Err(RenderError::Io {
            what: format!(
                "proof disappeared before rollback: {}",
                write.path.display()
            ),
        });
    };
    if current_source.as_bytes() != contents {
        return Err(RenderError::Io {
            what: format!(
                "proof changed after pipeline write; refusing rollback: {}",
                write.path.display()
            ),
        });
    }
    if let Some(original) = &write.original {
        write_proof_atomically(&write.path, original, write.permissions.clone(), true)
    } else {
        std::fs::remove_file(&write.path).map_err(|error| RenderError::Io {
            what: format!("remove failed proof seed {}: {error}", write.path.display()),
        })
    }
}

fn rollback_source_proof_writes(
    writes: &[PlannedSourceProofWrite],
    committed: &[usize],
    primary: RenderError,
) -> RenderError {
    let mut failures = Vec::new();
    for index in committed.iter().rev() {
        if let Err(error) = rollback_source_proof_write(&writes[*index]) {
            failures.push(format!("{error:?}"));
        }
    }
    if failures.is_empty() {
        primary
    } else {
        RenderError::Io {
            what: format!(
                "proof update failed ({primary:?}); rollback also failed: {}",
                failures.join("; ")
            ),
        }
    }
}

fn require_proof_directory(path: &Path) -> RenderResult<()> {
    let metadata = std::fs::symlink_metadata(path).map_err(|error| RenderError::Io {
        what: format!("metadata({}): {error}", path.display()),
    })?;
    if metadata.file_type().is_symlink() || !metadata.is_dir() {
        return Err(RenderError::Io {
            what: format!(
                "proof overlay directory must be a non-symlink directory: {}",
                path.display()
            ),
        });
    }
    Ok(())
}

fn prepare_proof_parent(proof_sources_dir: &Path, path: &Path) -> RenderResult<()> {
    let parent = path.parent().ok_or_else(|| RenderError::Io {
        what: format!("proof path has no parent: {}", path.display()),
    })?;
    let relative = parent
        .strip_prefix(proof_sources_dir)
        .map_err(|_| RenderError::Io {
            what: format!(
                "proof parent is outside overlay {}: {}",
                proof_sources_dir.display(),
                parent.display()
            ),
        })?;
    let mut current = proof_sources_dir.to_path_buf();
    for component in relative.components() {
        let std::path::Component::Normal(component) = component else {
            return Err(RenderError::Io {
                what: format!("invalid proof path component in {}", path.display()),
            });
        };
        current.push(component);
        match std::fs::symlink_metadata(&current) {
            Ok(_) => require_proof_directory(&current)?,
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => {
                std::fs::create_dir(&current).map_err(|error| RenderError::Io {
                    what: format!("create_dir({}): {error}", current.display()),
                })?;
                require_proof_directory(&current)?;
            }
            Err(error) => {
                return Err(RenderError::Io {
                    what: format!("metadata({}): {error}", current.display()),
                });
            }
        }
    }
    Ok(())
}

fn lock_source_proof_overlay(proof_sources_dir: &Path) -> RenderResult<std::fs::File> {
    std::fs::create_dir_all(proof_sources_dir).map_err(|error| RenderError::Io {
        what: format!("create_dir_all({}): {error}", proof_sources_dir.display()),
    })?;
    require_proof_directory(proof_sources_dir)?;
    #[cfg(not(windows))]
    let overlay = std::fs::File::open(proof_sources_dir).map_err(|error| RenderError::Io {
        what: format!(
            "open proof overlay {}: {error}",
            proof_sources_dir.display()
        ),
    })?;
    #[cfg(windows)]
    let overlay = {
        use std::fs::OpenOptions;

        let parent = proof_sources_dir.parent().ok_or_else(|| RenderError::Io {
            what: format!(
                "proof overlay has no parent: {}",
                proof_sources_dir.display()
            ),
        })?;
        let name = proof_sources_dir
            .file_name()
            .and_then(|name| name.to_str())
            .unwrap_or("proof-overlay");
        let lock_path = parent.join(format!(".{name}.proof-overlay.lock"));
        OpenOptions::new()
            .read(true)
            .write(true)
            .create(true)
            .open(&lock_path)
            .map_err(|error| RenderError::Io {
                what: format!("open proof overlay lock {}: {error}", lock_path.display()),
            })?
    };
    fs4::fs_std::FileExt::lock_exclusive(&overlay).map_err(|error| RenderError::Io {
        what: format!(
            "lock proof overlay {}: {error}",
            proof_sources_dir.display()
        ),
    })?;
    require_proof_directory(proof_sources_dir)?;
    Ok(overlay)
}

fn apply_source_proof_updates_locked(
    proof_sources_dir: &Path,
    updates: &[SourceProofUpdate],
) -> RenderResult<()> {
    if updates.is_empty() {
        return Ok(());
    }
    let mut paths = BTreeSet::new();
    let mut roots = BTreeSet::new();
    for update in updates {
        if !update.path.starts_with(proof_sources_dir)
            || update.path.parent() == Some(proof_sources_dir)
        {
            return Err(RenderError::Io {
                what: format!(
                    "generated proof must live below a package directory: {}",
                    update.path.display()
                ),
            });
        }
        if !paths.insert(update.path.clone()) || !roots.insert(update.root.clone()) {
            return Err(RenderError::Io {
                what: format!(
                    "duplicate proof update path or module root: {} ({})",
                    update.path.display(),
                    update.root
                ),
            });
        }
    }
    for update in updates {
        prepare_proof_parent(proof_sources_dir, &update.path)?;
    }
    let mut writes = Vec::with_capacity(updates.len());
    for update in updates {
        let (original, permissions, contents) = match read_source_proof(&update.path)? {
            Some((metadata, source)) => {
                let proof_metadata = proof_metadata(&update.path, &source)?;
                let contents =
                    updated_source_proof(&update.path, &source, &update.plan, &proof_metadata)?;
                (
                    Some(source.into_bytes()),
                    Some(metadata.permissions()),
                    contents,
                )
            }
            None => (None, None, Some(update.plan.body.as_bytes().to_vec())),
        };
        writes.push(PlannedSourceProofWrite {
            path: update.path.clone(),
            original,
            permissions,
            contents,
        });
    }

    if writes.iter().all(|write| write.contents.is_none()) {
        for write in &writes {
            require_source_proof_state(
                &write.path,
                write.original.as_deref(),
                "unchanged proof source validation",
            )?;
        }
        return Ok(());
    }

    for write in &writes {
        require_source_proof_state(
            &write.path,
            write.original.as_deref(),
            "proof source preflight",
        )?;
    }

    let mut committed = Vec::new();
    for (index, write) in writes.iter().enumerate() {
        match commit_source_proof_write(write) {
            Ok(true) => committed.push(index),
            Ok(false) => {}
            Err(error) => {
                return Err(rollback_source_proof_writes(&writes, &committed, error));
            }
        }
    }

    for write in &writes {
        let expected = write.contents.as_deref().or(write.original.as_deref());
        if let Err(error) =
            require_source_proof_state(&write.path, expected, "updated proof source validation")
        {
            return Err(rollback_source_proof_writes(&writes, &committed, error));
        }
    }
    Ok(())
}

#[cfg(test)]
fn apply_source_proof_updates(
    proof_sources_dir: &Path,
    updates: &[SourceProofUpdate],
) -> RenderResult<()> {
    let _overlay = lock_source_proof_overlay(proof_sources_dir)?;
    apply_source_proof_updates_locked(proof_sources_dir, updates)
}

fn is_regular_non_symlink_file_beneath(root: &Path, relative: &Path) -> RenderResult<bool> {
    let components: Vec<_> = relative.components().collect();
    if components.is_empty()
        || components
            .iter()
            .any(|component| !matches!(component, std::path::Component::Normal(_)))
    {
        return Err(RenderError::Io {
            what: format!(
                "native model source must be a relative path beneath {}: {}",
                root.display(),
                relative.display()
            ),
        });
    }
    let mut path = root.to_path_buf();
    for (index, component) in components.iter().enumerate() {
        let std::path::Component::Normal(component) = component else {
            unreachable!("components were validated above")
        };
        path.push(component);
        let metadata = match std::fs::symlink_metadata(&path) {
            Ok(metadata) => metadata,
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => return Ok(false),
            Err(error) => {
                return Err(RenderError::Io {
                    what: format!("inspect native model source {}: {error}", path.display()),
                });
            }
        };
        let is_last = index + 1 == components.len();
        if metadata.file_type().is_symlink()
            || (is_last && !metadata.is_file())
            || (!is_last && !metadata.is_dir())
        {
            return Err(RenderError::Io {
                what: format!(
                    "native model source path must contain only regular directories and end in a regular file: {}",
                    path.display()
                ),
            });
        }
    }
    Ok(true)
}

fn reject_output_symlinks(output_dir: &Path) -> RenderResult<()> {
    for entry in std::fs::read_dir(output_dir).map_err(|error| RenderError::Io {
        what: format!("scan render output {}: {error}", output_dir.display()),
    })? {
        let entry = entry.map_err(|error| RenderError::Io {
            what: format!("scan render output entry: {error}"),
        })?;
        let path = entry.path();
        let metadata = std::fs::symlink_metadata(&path).map_err(|error| RenderError::Io {
            what: format!("inspect render output entry {}: {error}", path.display()),
        })?;
        if metadata.file_type().is_symlink() {
            return Err(RenderError::Io {
                what: format!("render output contains a symlink: {}", path.display()),
            });
        }
        if metadata.is_dir() {
            reject_output_symlinks(&path)?;
        }
    }
    Ok(())
}

/// Render `program` to a full Lake project under `output_dir`.
///
/// Produces:
/// - `<output_dir>/NewPipeline/Code.lean`  -- the rendered Lean source
///   with a preamble of imports pulling in every native module that
///   exists under `lemmas_dir/*`.
/// - `<output_dir>/lakefile.lean`           -- Lake project declaring
///   `NewPipeline` and one `lean_lib` per top-level dir under
///   `lemmas_dir` (typically `Prelude`, `MoveStdlib`, `Sui`, `Prover`).
/// - `<output_dir>/lean-toolchain`           -- fixed Lean toolchain pin.
/// - `<output_dir>/lake-manifest.json`      -- Lake manifest.
/// - `<output_dir>/<top-level dir>/...`     -- recursive copy of every
///   subdir under `lemmas_dir`.
///
/// The output is suitable for `lake build` to type-check the rendered
/// Lean against the prelude + natives.
pub fn render_program_to_dir(
    program: &Program,
    output_dir: &Path,
    lemmas_dir: Option<&Path>,
    user_package: Option<&str>,
    proof_sources_dir: Option<&Path>,
    // `Test` hard-locks every recursive helper to `partial_fixpoint` (so the
    // `--test` drivers' `#eval` stays sound); `Proof` allows the opt-in
    // total-`def` upgrade when the registry supplies a real measure/proof;
    // `Execution` emits recursion as opaque `partial def` for runtime-only
    // semantic checks.
    loop_mode: loop_termination::LoopMode,
    // Path to the optional loop-termination registry (a missing file is
    // fine -- every loop then falls back to `partial_fixpoint`).
    loop_termination_path: Option<&Path>,
    // The ROOT (user) package name, from the top-level `Move.toml`. Its
    // native models use the legacy flat `lean/natives/*Natives.lean`
    // layout. Dependency native models are package-qualified beneath
    // `lean/natives/<Package>/`. `None` disables project-overlay lookup and
    // rejects a referenced user native that has no shipped framework model.
    root_package: Option<&str>,
) -> RenderResult<()> {
    render_program_to_dir_with_policy(
        program,
        output_dir,
        lemmas_dir,
        user_package,
        proof_sources_dir,
        proof_sources_dir,
        loop_mode,
        loop_termination_path,
        root_package,
    )
}

pub fn render_program_to_dir_with_policy(
    program: &Program,
    output_dir: &Path,
    lemmas_dir: Option<&Path>,
    user_package: Option<&str>,
    proof_sources_dir: Option<&Path>,
    native_policy_dir: Option<&Path>,
    loop_mode: loop_termination::LoopMode,
    loop_termination_path: Option<&Path>,
    root_package: Option<&str>,
) -> RenderResult<()> {
    let output_lock = acquire_render_output_lock(output_dir, proof_sources_dir, native_policy_dir)?;
    render_program_to_dir_with_policy_locked(
        program,
        output_dir,
        lemmas_dir,
        user_package,
        proof_sources_dir,
        native_policy_dir,
        loop_mode,
        loop_termination_path,
        root_package,
        &output_lock,
    )
}

pub struct RenderOutputLock {
    canonical_dir: PathBuf,
    _directory: std::fs::File,
    proof_overlay_dir: Option<PathBuf>,
    _proof_overlay: Option<std::fs::File>,
}

pub fn acquire_render_output_lock(
    output_dir: &Path,
    proof_sources_dir: Option<&Path>,
    native_policy_dir: Option<&Path>,
) -> RenderResult<RenderOutputLock> {
    use std::fs;

    require_render_paths_disjoint(output_dir, proof_sources_dir, native_policy_dir)?;
    fs::create_dir_all(output_dir).map_err(|e| RenderError::Io {
        what: format!("create_dir_all({}): {}", output_dir.display(), e),
    })?;
    let output_metadata = fs::symlink_metadata(output_dir).map_err(|error| RenderError::Io {
        what: format!("metadata({}): {error}", output_dir.display()),
    })?;
    if output_metadata.file_type().is_symlink() || !output_metadata.is_dir() {
        return Err(RenderError::Io {
            what: format!(
                "render output must be a non-symlink directory: {}",
                output_dir.display()
            ),
        });
    }
    #[cfg(not(windows))]
    let directory = std::fs::File::open(output_dir).map_err(|error| RenderError::Io {
        what: format!("open render output {}: {error}", output_dir.display()),
    })?;
    #[cfg(windows)]
    let directory = {
        use std::fs::OpenOptions;

        let parent = output_dir.parent().ok_or_else(|| RenderError::Io {
            what: format!("render output has no parent: {}", output_dir.display()),
        })?;
        let name = output_dir
            .file_name()
            .and_then(|name| name.to_str())
            .unwrap_or("render-output");
        let lock_path = parent.join(format!(".{name}.render.lock"));
        OpenOptions::new()
            .read(true)
            .write(true)
            .create(true)
            .open(&lock_path)
            .map_err(|error| RenderError::Io {
                what: format!("open render output lock {}: {error}", lock_path.display()),
            })?
    };
    fs4::fs_std::FileExt::lock_exclusive(&directory).map_err(|error| RenderError::Io {
        what: format!("lock render output {}: {error}", output_dir.display()),
    })?;
    let canonical_dir = output_dir.canonicalize().map_err(|error| RenderError::Io {
        what: format!(
            "canonicalize render output {}: {error}",
            output_dir.display()
        ),
    })?;
    let proof_overlay = proof_sources_dir
        .map(lock_source_proof_overlay)
        .transpose()?;
    let proof_overlay_dir = proof_sources_dir
        .map(|path| {
            path.canonicalize().map_err(|error| RenderError::Io {
                what: format!("canonicalize proof overlay {}: {error}", path.display()),
            })
        })
        .transpose()?;
    Ok(RenderOutputLock {
        canonical_dir,
        _directory: directory,
        proof_overlay_dir,
        _proof_overlay: proof_overlay,
    })
}

pub fn render_program_to_dir_with_policy_locked(
    program: &Program,
    output_dir: &Path,
    lemmas_dir: Option<&Path>,
    user_package: Option<&str>,
    proof_sources_dir: Option<&Path>,
    native_policy_dir: Option<&Path>,
    loop_mode: loop_termination::LoopMode,
    loop_termination_path: Option<&Path>,
    root_package: Option<&str>,
    output_lock: &RenderOutputLock,
) -> RenderResult<()> {
    render_program_to_dir_with_policy_locked_and_sidecars(
        program,
        output_dir,
        lemmas_dir,
        user_package,
        proof_sources_dir,
        native_policy_dir,
        loop_mode,
        loop_termination_path,
        root_package,
        output_lock,
        &[],
    )
}

#[derive(Debug, Clone)]
pub struct RenderSidecar {
    relative_path: PathBuf,
    contents: Option<Vec<u8>>,
}

impl RenderSidecar {
    pub fn write(relative_path: impl Into<PathBuf>, contents: impl Into<Vec<u8>>) -> Self {
        Self {
            relative_path: relative_path.into(),
            contents: Some(contents.into()),
        }
    }

    pub fn remove(relative_path: impl Into<PathBuf>) -> Self {
        Self {
            relative_path: relative_path.into(),
            contents: None,
        }
    }
}

pub fn render_program_to_dir_with_policy_locked_and_sidecars(
    program: &Program,
    output_dir: &Path,
    lemmas_dir: Option<&Path>,
    user_package: Option<&str>,
    proof_sources_dir: Option<&Path>,
    native_policy_dir: Option<&Path>,
    loop_mode: loop_termination::LoopMode,
    loop_termination_path: Option<&Path>,
    root_package: Option<&str>,
    output_lock: &RenderOutputLock,
    sidecars: &[RenderSidecar],
) -> RenderResult<()> {
    require_render_paths_disjoint(output_dir, proof_sources_dir, native_policy_dir)?;
    let canonical_output = output_dir.canonicalize().map_err(|error| RenderError::Io {
        what: format!(
            "canonicalize render output {}: {error}",
            output_dir.display()
        ),
    })?;
    if canonical_output != output_lock.canonical_dir {
        return Err(RenderError::Io {
            what: format!(
                "render output lock covers {}, not {}",
                output_lock.canonical_dir.display(),
                canonical_output.display()
            ),
        });
    }
    let canonical_proof_overlay = proof_sources_dir
        .map(|path| {
            path.canonicalize().map_err(|error| RenderError::Io {
                what: format!("canonicalize proof overlay {}: {error}", path.display()),
            })
        })
        .transpose()?;
    if canonical_proof_overlay != output_lock.proof_overlay_dir {
        return Err(RenderError::Io {
            what: "render output lock does not cover the requested proof overlay".to_string(),
        });
    }
    reject_output_symlinks(output_dir)?;

    let staging_parent = canonical_output.parent().ok_or_else(|| RenderError::Io {
        what: format!(
            "render output has no parent for staging: {}",
            canonical_output.display()
        ),
    })?;
    let staging = tempfile::Builder::new()
        .prefix(".sui-lean-render-")
        .tempdir_in(staging_parent)
        .map_err(|error| RenderError::Io {
            what: format!(
                "create render staging directory under {}: {error}",
                staging_parent.display()
            ),
        })?;
    let staging_started = std::time::Instant::now();
    let staged = render_program_to_staging(
        program,
        staging.path(),
        lemmas_dir,
        user_package,
        proof_sources_dir,
        native_policy_dir,
        loop_mode,
        loop_termination_path,
        root_package,
    )?;
    let staging_elapsed = staging_started.elapsed();
    let planning_started = std::time::Instant::now();
    let mut plan = self::materialize::RenderPlan::from_staging_tree(staging.path())?;
    for sidecar in sidecars {
        match &sidecar.contents {
            Some(contents) => plan.insert(&sidecar.relative_path, contents.clone())?,
            None => plan.remove(&sidecar.relative_path)?,
        }
    }
    add_unowned_generated_removals(
        &mut plan,
        output_dir,
        &staged.user_packages,
        &staged.lemma_libs,
    )?;
    let planning_elapsed = planning_started.elapsed();
    let publication_started = std::time::Instant::now();
    let publication = plan.publish_with_bootstrap(
        output_dir,
        self::materialize::BootstrapPolicy::AdoptExistingPlannedPaths,
    )?;
    let publication_elapsed = publication_started.elapsed();
    let proof_updates_started = std::time::Instant::now();
    if let Some(source_dir) = proof_sources_dir {
        if let Err(error) =
            apply_source_proof_updates_locked(source_dir, &staged.source_proof_updates)
        {
            return match publication.rollback() {
                Ok(()) => Err(error),
                Err(rollback) => Err(RenderError::Io {
                    what: format!(
                        "proof update failed ({error:?}); generated-output rollback also failed ({rollback:?})"
                    ),
                }),
            };
        }
    }
    let proof_updates_elapsed = proof_updates_started.elapsed();
    let commit_started = std::time::Instant::now();
    publication.commit()?;
    remove_empty_retired_scaffold_directories(output_dir);
    eprintln!(
        "[timing] renderer phases: staging={}ms planning={}ms publication={}ms \
         proof_updates={}ms commit={}ms",
        staging_elapsed.as_millis(),
        planning_elapsed.as_millis(),
        publication_elapsed.as_millis(),
        proof_updates_elapsed.as_millis(),
        commit_started.elapsed().as_millis(),
    );
    Ok(())
}

struct StagedRender {
    source_proof_updates: Vec<SourceProofUpdate>,
    user_packages: BTreeSet<String>,
    lemma_libs: Vec<String>,
}

fn render_program_to_staging(
    program: &Program,
    output_dir: &Path,
    lemmas_dir: Option<&Path>,
    user_package: Option<&str>,
    proof_sources_dir: Option<&Path>,
    native_policy_dir: Option<&Path>,
    loop_mode: loop_termination::LoopMode,
    loop_termination_path: Option<&Path>,
    root_package: Option<&str>,
) -> RenderResult<StagedRender> {
    use std::fs;

    let proof_automation_dependencies = proof_automation_dependencies(lemmas_dir)?;
    for module in program.modules.values() {
        if user_package.is_some_and(|package| module.package_name != package && !module.is_native) {
            continue;
        }
        let location = module_render_location(&module.package_name, &module.name);
        if RESERVED_LEAN_MODULE_ROOTS.contains(&location.package.as_str()) {
            return Err(RenderError::Io {
                what: format!(
                    "generated module {}.{} collides with reserved Lean module root `{}`",
                    location.package, location.file_stem, location.package
                ),
            });
        }
    }
    if let Some(proof_sources_dir) = proof_sources_dir {
        for root in RESERVED_LEAN_MODULE_ROOTS {
            for path in [
                proof_sources_dir.join(root),
                proof_sources_dir.join(format!("{root}.lean")),
            ] {
                match std::fs::symlink_metadata(&path) {
                    Ok(_) => {
                        return Err(RenderError::Io {
                            what: format!(
                                "proof-overlay path {} collides with reserved Lean module root `{root}`",
                                path.display()
                            ),
                        });
                    }
                    Err(error) if error.kind() == std::io::ErrorKind::NotFound => {}
                    Err(error) => {
                        return Err(RenderError::Io {
                            what: format!(
                                "cannot inspect proof-overlay path {}: {error}",
                                path.display()
                            ),
                        });
                    }
                }
            }
        }
    }

    // Load the loop-emission context (mode + measure/proof registry) for
    // this render. In `Proof` mode, orphaned registry entries (keys matching
    // no live loop) are reported loudly.
    let loop_registry = match loop_termination_path {
        Some(p) => loop_termination::LoopTerminationRegistry::load(p),
        None => loop_termination::LoopTerminationRegistry::default(),
    };
    if loop_mode == loop_termination::LoopMode::Proof {
        loop_termination::report_orphans(program, &loop_registry);
    }
    let context = self::context::RenderContext::new(
        program,
        self::loop_termination::LoopRenderContext::new(loop_mode, loop_registry),
    );

    // The package root -- `<package-root>/loop_termination.txt`'s parent
    // -- is where the pipeline looks up hand-written natives files for
    // user-declared `native fun`s (see the per-module `natives/` copy in
    // the emission loop below). `None` when no loop-termination path was
    // supplied; a user native then hard-errors with a message pointing at
    // the missing lookup root.
    let package_root: Option<&Path> = loop_termination_path.and_then(|p| p.parent());

    let mut lemma_libs: Vec<String> = Vec::new();
    let mut native_imports: Vec<String> = Vec::new();
    // Destination paths of every file copied from `lemmas/` in this run.
    // The per-module render loop consults this set instead of
    // `path.exists()` so it can safely overwrite its own stubs from a
    // prior render while still leaving lemma-sourced files untouched.
    let mut copied_from_lemmas: HashSet<PathBuf> = HashSet::new();
    let mut copied_from_package_overlays: HashSet<PathBuf> = HashSet::new();
    // Which `*Lemmas.lean` companions this program can actually build, and
    // which subject each rides in on. See `render/lemma_companions.rs`.
    // Test mode keeps the historic blanket skip (see the copy loop below),
    // so its plan is empty and no companion import is emitted either.
    let companion_plan = if loop_mode == loop_termination::LoopMode::Test {
        self::lemma_companions::CompanionPlan::default()
    } else {
        self::lemma_companions::CompanionPlan::build(program, lemmas_dir)?
    };
    if let Some(src) = lemmas_dir {
        if src.is_dir() {
            // Build a flat list of (display_name, source_dir) pairs to
            // copy. Each top-level dir under `lemmas_dir` becomes a
            // `lean_lib` -- EXCEPT `natives/`, whose own subdirs
            // (`MoveStdlib`, `Sui`, `Prover`) get promoted to
            // top-level libs. That matches the legacy backend's
            // output layout, which the prelude files' `namespace`
            // declarations are written against.
            let mut to_copy: Vec<(String, std::path::PathBuf)> = Vec::new();
            for entry in fs::read_dir(src).map_err(|e| RenderError::Io {
                what: format!("read_dir({}): {}", src.display(), e),
            })? {
                let entry = entry.map_err(|e| RenderError::Io {
                    what: format!("read_dir entry: {}", e),
                })?;
                let path = entry.path();
                if !path.is_dir() {
                    continue;
                }
                let name = path
                    .file_name()
                    .and_then(|n| n.to_str())
                    .ok_or_else(|| RenderError::Io {
                        what: format!("non-utf8 dir name under {}", src.display()),
                    })?
                    .to_string();
                if name == "natives" {
                    // Promote `natives/<X>` -> top-level `<X>`.
                    for nat_entry in fs::read_dir(&path).map_err(|e| RenderError::Io {
                        what: format!("read_dir({}): {}", path.display(), e),
                    })? {
                        let nat_entry = nat_entry.map_err(|e| RenderError::Io {
                            what: format!("read_dir entry: {}", e),
                        })?;
                        let nat_path = nat_entry.path();
                        if !nat_path.is_dir() {
                            continue;
                        }
                        let nat_name = nat_path
                            .file_name()
                            .and_then(|n| n.to_str())
                            .ok_or_else(|| RenderError::Io {
                                what: format!("non-utf8 dir name under {}", path.display()),
                            })?
                            .to_string();
                        to_copy.push((nat_name, nat_path));
                    }
                } else {
                    to_copy.push((name, path));
                }
            }
            // Proof-lemma modules (`*Lemmas.lean`) state theorems about
            // GENERATED defs (`MoveOption.some.aborts`,
            // `Table_vec.borrow.aborts` ...). Whether a given corpus still
            // HAS those defs after per-package pruning is exactly what
            // `companion_plan` answers: a companion is copied only when
            // every constant it names from its subject survives. Test mode
            // keeps the blunter rule -- a `--test` project prunes to what
            // the drivers reach and has no proof seeds to consume a
            // companion, so nothing there is worth building.
            let skip_proof_lemma_files = loop_mode == loop_termination::LoopMode::Test;
            for (lib_name, src_path) in to_copy {
                if RESERVED_LEAN_MODULE_ROOTS.contains(&lib_name.as_str()) {
                    return Err(RenderError::Io {
                        what: format!(
                            "lemma library `{lib_name}` collides with a reserved Lean module root"
                        ),
                    });
                }
                let dst = output_dir.join(&lib_name);
                copy_dir_recursive(
                    &src_path,
                    &dst,
                    &mut copied_from_lemmas,
                    &|candidate: &Path| {
                        if skip_proof_lemma_files {
                            return false;
                        }
                        match self::lemma_companions::relative_to_root(src, candidate) {
                            Some(relative) => companion_plan.retains(&relative),
                            None => false,
                        }
                    },
                )
                .map_err(|e| RenderError::Io {
                    what: format!(
                        "copy_dir_recursive({} -> {}): {}",
                        src_path.display(),
                        dst.display(),
                        e
                    ),
                })?;
                collect_imports(&src_path, &lib_name, &mut native_imports).map_err(|e| {
                    RenderError::Io {
                        what: format!("collect_imports({}): {}", src_path.display(), e),
                    }
                })?;
                lemma_libs.push(lib_name);
            }
        }
    }
    lemma_libs.sort();
    native_imports.sort();
    native_imports.dedup();

    // Set of lemma-lib package names for fast membership tests in the
    // per-module loop. Used to gate per-package AnyKey imports out of
    // native modules (whose `Generated/` directory is never written).
    let lemma_libs_set: std::collections::BTreeSet<String> = lemma_libs.iter().cloned().collect();

    // Per-module file emission. Each non-native Move module gets its
    // own `<package_name>/<module_namespace>.lean` containing the
    // imports it needs + its namespace block. Native modules get a
    // forwarding module for a selected hand-written natives sibling,
    // or an empty namespace when they expose no rendered declarations.
    //
    // Cross-module dependencies are inferred by walking each module's
    // body for `Struct` / `Call` references to other modules and
    // emitting the appropriate `import <pkg>.<module>` lines. This
    // mirrors the legacy backend's per-module-file layout, which the
    // hand-written natives files (`Sui/CoinNatives.lean` etc.) are
    // written against.
    let mut emitted_module_paths: Vec<String> = Vec::new();
    let mut source_proof_updates = Vec::new();
    let mut proof_declaration_fingerprints = BTreeMap::new();
    let referenced_native_fids = self::native_models::referenced_native_fids(program, user_package);
    for (mid, module) in &program.modules {
        let location = module_render_location(&module.package_name, &module.name);
        let pkg_name = location.package;
        let ns = location.file_stem;

        // Optional user-package filter: only emit user-package modules.
        if let Some(pkg) = user_package {
            if module.package_name != pkg && !module.is_native {
                continue;
            }
        }

        let pkg_dir = output_dir.join(&pkg_name);
        fs::create_dir_all(&pkg_dir).map_err(|e| RenderError::Io {
            what: format!("create_dir_all({}): {}", pkg_dir.display(), e),
        })?;
        let path = pkg_dir.join(format!("{}.lean", ns));

        // Don't overwrite a file that was copied from `lemmas/` this
        // run (hand-written `<X>Natives.lean` siblings, prelude
        // modules, etc.). Stale per-module files left behind by an
        // earlier render — including renderer-emitted forwarding modules that
        // predate a change to the natives allowlist — ARE overwritten
        // here; otherwise updates to `NATIVE_FUNCTION_MODULES` / `NATIVE_STRUCTS` silently fail
        // to take effect on re-renders into a non-empty `output_dir`.
        if copied_from_lemmas.contains(&path) {
            continue;
        }

        let pkg_is_lemma = lemma_libs_set.contains(&pkg_name);

        // Root-package native models retain the legacy flat path. Models
        // for dependency-package natives are package-qualified so modules
        // with the same name cannot consume one another's definitions.
        // Both are mandatory: no generated native fallback is permitted.
        let module_has_external_user_natives = program.natives.decls.iter().any(|(fid, d)| {
            let belongs_to_user_native = d.user_native.is_some()
                || d.spec_target
                    .and_then(|target| program.natives.decls.get(&target))
                    .is_some_and(|target| target.user_native.is_some());
            d.module == *mid
                && belongs_to_user_native
                && referenced_native_fids.contains(fid)
                && !self::native_models::is_renderer_owned_end_transaction_model(d, program)
        });
        let natives_sibling = pkg_dir.join(format!("{}Natives.lean", ns));
        if module_has_external_user_natives && !copied_from_lemmas.contains(&natives_sibling) {
            let module_name = format!("{}::{}", module.package_name, module.name);
            if root_package.is_none() {
                return Err(RenderError::MissingRootPackage {
                    module: module_name,
                });
            }
            let Some(root) = package_root else {
                return Err(RenderError::MissingPackageRoot {
                    module: module_name,
                });
            };
            let relative = if root_package == Some(pkg_name.as_str()) {
                PathBuf::from("lean")
                    .join("natives")
                    .join(format!("{}Natives.lean", ns))
            } else {
                PathBuf::from("lean")
                    .join("natives")
                    .join(&pkg_name)
                    .join(format!("{}Natives.lean", ns))
            };
            let src = root.join(&relative);
            let source_available = match is_regular_non_symlink_file_beneath(root, &relative) {
                Ok(available) => available,
                Err(error) => return Err(error),
            };
            if !source_available {
                return Err(RenderError::MissingNativesFile {
                    module: module_name,
                    looked_up: src.display().to_string(),
                });
            }
            if !copied_from_lemmas.contains(&natives_sibling) {
                fs::copy(&src, &natives_sibling).map_err(|e| RenderError::Io {
                    what: format!(
                        "copy natives file {} -> {}: {}",
                        src.display(),
                        natives_sibling.display(),
                        e
                    ),
                })?;
                copied_from_lemmas.insert(natives_sibling.clone());
                copied_from_package_overlays.insert(natives_sibling.clone());
            }
        }

        // Only files selected during this render may satisfy a native
        // import. An arbitrary or stale output file is never authoritative.
        let natives_import = self::native_models::resolve_native_forward(
            output_dir,
            &pkg_name,
            &module.name,
            |candidate| copied_from_lemmas.contains(candidate),
        )
        .map(|forward| forward.import);
        // Helper to assemble a Lean file body. Captures pkg_is_lemma,
        // pkg_name, and ns so the boilerplate (recursion depth +
        // lemma-only notation block) stays consistent across the
        // (potentially) two files we emit per Move module.
        // Per-module ObjType taint: at least one function in this
        // module has a type param that flows into transfer/take_*.
        // Used to pin the file-scoped `World` notation's Object slot
        // to `Bag.Entry _root_.ObjType` so call sites of typed
        // natives can unify ObjUniv = _root_.ObjType.
        let module_has_obj_taint = module_has_obj_taint(&context, *mid);
        let assemble_lean_file = |imports: &[String], module_namespace: &str| -> String {
            let mut content = String::new();
            for imp in imports {
                content.push_str("import ");
                content.push_str(imp);
                content.push('\n');
            }
            if !imports.is_empty() {
                content.push('\n');
            }
            // Bump Lean's elaborator recursion-depth ceiling for
            // every rendered file. Test-mode `.aborts` companions in
            // particular emit one giant `||`-chained boolean for
            // each test body (see `IntegerMate/I128_tests.lean`
            // around lines 1212 / 4194 / 4810 -- ~80-level deep
            // `||` cascades). Lean's default `maxRecDepth = 512`
            // trips on these; 4096 is the conventional headroom.
            // The option is file-scoped, doesn't affect other
            // imported modules, and only relaxes a ceiling that
            // exists to catch *user-written* infinite recursion --
            // which the renderer cannot introduce.
            //
            // Also raise the elaboration heartbeat ceiling. De-jumping
            // a very large test body produces a few enormous
            // `.aborts.cont_*` continuation defs (navi-lending
            // `Incentive_v3_integration_test` emits a single ~2350-line
            // def); these blow the default `maxHeartbeats = 200000`,
            // which then *cascades* into a bogus
            // `Function.<field>` projection error at the next
            // declaration that calls the timed-out one (it never made
            // it into the environment). Mirror the legacy backend's
            // 8000000 / synthInstance 4000000 ceilings. Same rationale
            // as `maxRecDepth`: relaxes a runaway-detection limit the
            // renderer cannot legitimately trip.
            //
            // Disable the unused-variable linter file-wide: generated bodies
            // routinely bind names they never read -- tuple destructuring that
            // ignores some slots, and threaded loop/world state that is dead on
            // a particular branch -- which is correct codegen, not a mistake to
            // flag. (The per-test drivers already set this; module files did
            // not, so every such binder produced a `linter.unusedVariables`
            // warning during `lake build`.)
            // The `noncomputable section` is NOT opened here (file scope):
            // that would wrap the whole module, and a `deriving Inhabited`
            // on a Move enum inside a `noncomputable section` makes the
            // derived instance noncomputable (and outright panics the LCNF
            // compiler on a minimal file -- `ExplicitBoxing:301:45`). Type
            // definitions, their `deriving` clauses, and hand-written
            // `instance`s must stay OUTSIDE it. `render_single_module`
            // opens a minimal `noncomputable section` around the function
            // payload only (step structs / explicit native models / ghost decls /
            // function bodies -- the defs that reference the noncomputable
            // quantifier-traversal helpers).
            content.push_str(
                "set_option maxRecDepth 4096
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 4000000
set_option linter.unusedVariables false

",
            );
            // Translated modules in lemma packages (Sui::accumulator,
            // Sui::table_vec, MoveStdlib::option, ...) don't get the
            // per-user-package `Generated/AnyKey` abbrev that brings
            // a concrete `Mutation` / `Edge` shorthand into scope.
            // We can't import it either -- there's one AnyKey per
            // user package and the framework files are shared. Emit
            // a file-scoped `variable {Key : Type}` so Lean's
            // auto-bound implicits make every signature in the file
            // polymorphic over Key; the abbrevs then expand to the
            // 2-arg prelude form.
            //
            // Per-notation filtering: a `local notation` whose name
            // matches the module's own namespace would shadow the
            // namespace itself at parse time. The only collision in
            // practice is the synthetic `prover::world` module whose
            // namespace is literally `World`; we omit the `World`
            // line for that case so its `namespace World ... end
            // World` block parses normally.
            if pkg_is_lemma {
                // Make `Mutation T` / `Edge` resolve to the 2-arg
                // prelude form parameterised over an auto-bound Key.
                // Using `notation` (parse-time expansion) rather than
                // `abbrev`: the expansion places `__MutKey` directly
                // into each enclosing definition's type, which Lean's
                // auto-bound-implicit rule then attaches as a `{__MutKey
                // : Type}` parameter. An `abbrev` wouldn't auto-bind
                // because Lean elaborates the abbrev's RHS once and
                // captures the section variable as a parameter on the
                // abbrev itself, leaving each use site with an
                // independent metavariable.
                //
                // Name `__MutKey` (underscore prefix) avoids collisions
                // with module-level `structure Key` (e.g. accumulator's
                // `Key`).
                //
                // The `AnyKey` -> `__MutKey` notation lets each body's
                // `@Prover.Mutation.Mutation.<op> AnyKey ...` call
                // resolve against the file-scoped polymorphic key.
                // User-package files import `Generated/AnyKey.lean`
                // and use the concrete `AnyKey` inductive directly,
                // so this notation only fires in lemma modules.
                // Body-rendering code in `render/expr.rs` keeps
                // emitting the literal `AnyKey` identifier; the
                // notation handles the lemma-vs-user dispatch at
                // parse time.
                content.push_str("variable {__MutKey : Type}\n");
                if ns != "AnyKey" {
                    content.push_str("local notation:max \"AnyKey\" => __MutKey\n");
                }
                if ns != "Mutation" {
                    content.push_str(
                        "local notation:max \"Mutation \" T:max => Prover.Mutation.Mutation __MutKey T\n",
                    );
                }
                if ns != "Edge" {
                    content
                        .push_str("local notation:max \"Edge\" => Prover.Mutation.Edge __MutKey\n");
                }
                // Stage 4 (effects) threads `world : World` through Impure
                // callees; in user packages `Generated/World.lean` supplies
                // the concrete `World := Prover.World.World AnyEvent AnyObject`
                // abbreviation, but lemma packages don't have a per-package
                // Generated tree. Emit a file-scoped polymorphic `World`
                // notation -- same trick as `AnyKey` / `Mutation` above.
                //
                // The object slot is kept ABSTRACT (`__WorldObject`) for ALL
                // lemma modules. ObjType-tainted functions (transfer /
                // test_scenario wrappers) pin it per-function to
                // `Bag.Entry __ObjU` via its owned type-render overrides (see
                // render::function), with `[Universe __ObjU]` as a hypothesis
                // resolved at the user call site. Pinning `_root_.ObjType` at
                // the module level instead would force `Universe ObjType` (which
                // lives only in `Generated.ObjTypeInterp`) into framework
                // modules like `Sui.Transfer`, closing a `TyCodeInterp ->
                // Sui.Package -> Sui.Transfer -> ObjTypeInterp` build cycle.
                // Untainted World uses fall back to the free `__WorldObject`.
                content.push_str(
                    "variable {__WorldEvent __WorldObject __WorldDfEntry __WorldBagEntry : Type}\n",
                );
                if ns != "World" {
                    content.push_str(
                        "local notation:max \"World\" => Prover.World.World __WorldEvent __WorldObject __WorldDfEntry __WorldBagEntry\n",
                    );
                }
                content.push_str("\n");
            }
            content.push_str(module_namespace);
            content
        };

        // For lemma packages keep the legacy single-file shape (their
        // structs are all `is_native` so a Types slice would be empty).
        // For user packages, split into:
        //   * `<Mod>_Types.lean` -- structs only. Lean imports gated
        //     to other Types files + minimal Prelude.
        //   * `<Mod>.lean`       -- function bodies + explicit native models.
        //     Imports own _Types, other modules' regular files, and
        //     `Generated.TyCode` when heterogeneous storage is used.
        // The split is what breaks the lemma->user cycle that would
        // otherwise form via `Generated.TyCode` (see Phase 3b in
        // `plans/lean-pipeline/dynamic-typing-via-repr-design.md`).
        //
        // A bag-cycle lemma module (Bag-containing + a bag-value struct, e.g.
        // Sui `coin_registry`) instead falls through to the user-package
        // Bag-split below, so `Generated.BagUInterp` can import only its
        // Bag-free `_Types_Skeleton`.
        if pkg_is_lemma && !lemma_module_bag_split(&context, *mid) {
            // Lemma/framework modules are normally single-file (`Full`):
            // their structs are usually all `is_native`, so a `_Types`
            // slice would be empty. EXCEPTION: a few obj-tainted framework
            // modules (e.g. `Sui::test_scenario`) declare a real
            // `structure` AND import `Generated.ObjTypeInterp` for their
            // impure function bodies. The universe interpreters
            // (`TyCode`/`ObjType`/`AnyKey`) must name that struct, but
            // importing the whole module would pull in `ObjTypeInterp` and
            // close an import cycle. For those, split out a pure
            // `<Mod>_Types.lean` leaf (struct defs only -- no lemma
            // notations, no Generated interpreter imports) and keep the
            // functions in `<Mod>.lean`, which imports its own `_Types`.
            let has_nonnative_struct = program
                .structs
                .iter()
                .any(|(_, s)| s.module_id == *mid && !s.is_native);
            if module_has_obj_taint && has_nonnative_struct {
                let mut types_imports = collect_types_module_imports(
                    &context,
                    *mid,
                    &pkg_name,
                    &ns,
                    &lemma_libs_set,
                    /*for_skeleton=*/ false,
                );
                if let Some(ref ni) = natives_import {
                    types_imports.push(ni.clone());
                }
                types_imports.sort();
                types_imports.dedup();
                let types_ns = render_single_module(&context, *mid, ModuleKind::Types)?;
                // Assemble the leaf WITHOUT the lemma `notation` block:
                // struct fields are storable, so they never reference
                // `AnyKey` / `Mutation` / `Edge` / `World`, and emitting
                // those notations would force `Prover.*` imports the pure
                // leaf must not carry.
                let mut types_body = String::new();
                for imp in &types_imports {
                    types_body.push_str("import ");
                    types_body.push_str(imp);
                    types_body.push('\n');
                }
                if !types_imports.is_empty() {
                    types_body.push('\n');
                }
                types_body.push_str("set_option maxRecDepth 4096\nset_option maxHeartbeats 8000000\nset_option synthInstance.maxHeartbeats 4000000\nset_option linter.unusedVariables false\n\n");
                types_body.push_str(&types_ns);
                let types_path = pkg_dir.join(format!("{}_Types.lean", ns));
                fs::write(&types_path, &types_body).map_err(|e| RenderError::Io {
                    what: format!("write({}): {}", types_path.display(), e),
                })?;
                emitted_module_paths.push(format!("{}.{}_Types", pkg_name, ns));

                let mut imports = collect_module_imports(
                    &context,
                    *mid,
                    &pkg_name,
                    &ns,
                    &lemma_libs_set,
                    &companion_plan,
                );
                imports.push(format!("{}.{}_Types", pkg_name, ns));
                if let Some(ref ni) = natives_import {
                    imports.push(ni.clone());
                }
                imports.sort();
                imports.dedup();
                let body_ns = render_single_module(&context, *mid, ModuleKind::Funcs)?;
                let body = assemble_lean_file(&imports, &body_ns);
                fs::write(&path, &body).map_err(|e| RenderError::Io {
                    what: format!("write({}): {}", path.display(), e),
                })?;
                emitted_module_paths.push(format!("{}.{}", pkg_name, ns));
            } else {
                let mut imports = collect_module_imports(
                    &context,
                    *mid,
                    &pkg_name,
                    &ns,
                    &lemma_libs_set,
                    &companion_plan,
                );
                if let Some(ref ni) = natives_import {
                    imports.push(ni.clone());
                }
                let body_ns = render_single_module(&context, *mid, ModuleKind::Full)?;
                let body = assemble_lean_file(&imports, &body_ns);
                fs::write(&path, &body).map_err(|e| RenderError::Io {
                    what: format!("write({}): {}", path.display(), e),
                })?;
                emitted_module_paths.push(format!("{}.{}", pkg_name, ns));
            }
        } else {
            // Determine whether this module needs a Types split.
            // A module's `Bag` field is typed over `BagU`, so a
            // Bag-CONTAINING struct's `_Types` imports `BagUInterp`.
            // When the SAME module ALSO defines a bag-VALUE struct (a
            // `BagU` member, which `BagUInterp` imports), a single
            // `_Types` would cycle (`_Types -> BagUInterp -> _Types`).
            // Split to break it:
            //   * `<Mod>_Types_Skeleton.lean` -- Bag-FREE structs only,
            //     no `BagUInterp` dependency. This is what
            //     `Generated/BagUInterp.lean` imports (bag VALUES are
            //     Bag-free, so they live here).
            //   * `<Mod>_Types.lean` -- Bag-CONTAINING structs only,
            //     imports its own `_Types_Skeleton` + `BagUInterp` for
            //     `[Universe BagU]`. `TyCodeInterp` (df values incl.
            //     Bag-containing structs) and function files import
            //     `<Mod>_Types`, which re-exports the skeleton.
            // No Bag-containing struct -> single `<Mod>_Types.lean`.
            // See `plans/lean-pipeline/split-bag-df-universes.md`.
            let bag_struct_ids = context.bag_containing_structs();
            let module_bag_struct_ids: std::collections::HashSet<StructId> = bag_struct_ids
                .iter()
                .copied()
                .filter(|sid| {
                    program
                        .structs
                        .get(sid)
                        .map_or(false, |s| s.module_id == *mid)
                })
                .collect();
            let needs_split = !module_bag_struct_ids.is_empty();

            if needs_split {
                // Bag-free structs (everything in module NOT in bag_struct_ids).
                let bag_free_struct_ids: std::collections::HashSet<StructId> = program
                    .structs
                    .iter()
                    .filter(|(sid, s)| s.module_id == *mid && !module_bag_struct_ids.contains(sid))
                    .map(|(sid, _)| *sid)
                    .collect();

                // 1a) Skeleton file -- Bag-free structs, no BagUInterp.
                //     Routes split cross-module deps to THEIR skeletons
                //     so this file never transitively imports BagUInterp.
                let skel_imports = collect_types_module_imports(
                    &context,
                    *mid,
                    &pkg_name,
                    &ns,
                    &lemma_libs_set,
                    /*for_skeleton=*/ true,
                );
                let skel_ns = render_single_module_filtered(
                    &context,
                    *mid,
                    ModuleKind::Types,
                    Some(&bag_free_struct_ids),
                )?;
                let skel_body = assemble_lean_file(&skel_imports, &skel_ns);
                let skel_path = pkg_dir.join(format!("{}_Types_Skeleton.lean", ns));
                fs::write(&skel_path, &skel_body).map_err(|e| RenderError::Io {
                    what: format!("write({}): {}", skel_path.display(), e),
                })?;
                emitted_module_paths.push(format!("{}.{}_Types_Skeleton", pkg_name, ns));

                // 1b) Main _Types file -- Bag-containing structs only.
                //     Imports own Skeleton + BagUInterp. Unlike the
                //     skeleton, this file already imports BagUInterp,
                //     so it may import split deps' full `_Types`
                //     (needed for Bag-containing dep struct references).
                let mut types_imports = collect_types_module_imports(
                    &context,
                    *mid,
                    &pkg_name,
                    &ns,
                    &lemma_libs_set,
                    /*for_skeleton=*/ false,
                );
                types_imports.push(format!("{}.{}_Types_Skeleton", pkg_name, ns));
                types_imports.push("Generated.BagUInterp".to_string());
                types_imports.sort();
                types_imports.dedup();
                let types_ns = render_single_module_filtered(
                    &context,
                    *mid,
                    ModuleKind::Types,
                    Some(&module_bag_struct_ids),
                )?;
                let types_body = assemble_lean_file(&types_imports, &types_ns);
                let types_path = pkg_dir.join(format!("{}_Types.lean", ns));
                if !copied_from_lemmas.contains(&types_path) {
                    fs::write(&types_path, &types_body).map_err(|e| RenderError::Io {
                        what: format!("write({}): {}", types_path.display(), e),
                    })?;
                    emitted_module_paths.push(format!("{}.{}_Types", pkg_name, ns));
                }
            } else {
                // 1) Types slice -- all structs. Minimal imports; no
                //    `Generated.TyCode` (would create the cycle we're
                //    splitting to avoid).
                let types_imports = collect_types_module_imports(
                    &context,
                    *mid,
                    &pkg_name,
                    &ns,
                    &lemma_libs_set,
                    /*for_skeleton=*/ false,
                );
                let types_ns = render_single_module(&context, *mid, ModuleKind::Types)?;
                let types_body = assemble_lean_file(&types_imports, &types_ns);
                let types_path = pkg_dir.join(format!("{}_Types.lean", ns));
                if !copied_from_lemmas.contains(&types_path) {
                    fs::write(&types_path, &types_body).map_err(|e| RenderError::Io {
                        what: format!("write({}): {}", types_path.display(), e),
                    })?;
                    emitted_module_paths.push(format!("{}.{}_Types", pkg_name, ns));
                }
            }
            // 2) Funcs slice -- explicit native models + functions. Adds own
            //    `_Types` self-import and the natives sibling import.
            let mut funcs_imports = collect_module_imports(
                &context,
                *mid,
                &pkg_name,
                &ns,
                &lemma_libs_set,
                &companion_plan,
            );
            funcs_imports.push(format!("{}.{}_Types", pkg_name, ns));
            if let Some(ref ni) = natives_import {
                funcs_imports.push(ni.clone());
            }
            funcs_imports.sort();
            funcs_imports.dedup();
            let funcs_ns = render_single_module(&context, *mid, ModuleKind::Funcs)?;
            let funcs_body = assemble_lean_file(&funcs_imports, &funcs_ns);
            fs::write(&path, &funcs_body).map_err(|e| RenderError::Io {
                what: format!("write({}): {}", path.display(), e),
            })?;
            emitted_module_paths.push(format!("{}.{}", pkg_name, ns));
        }

        // The module declares each proof obligation as a named proposition.
        // Source-proof mode seeds a missing durable sibling and inserts newly
        // emitted obligations after its lexical import header. Durable stubs
        // scope their resource options and export their qualified declaration
        // for legacy bare cross-proof references. Output-only mode regenerates
        // its byte-compatible disposable sibling without durable ownership
        // metadata.
        let theorem_fns: Vec<(&FunId, &crate::ir::Function)> = program
            .functions
            .iter()
            .filter(|(_, f)| {
                f.module == *mid && matches!(f.kind, crate::ir::FunctionKind::Theorem { .. })
            })
            .collect();
        let output_proofs_path = pkg_dir.join(format!("{}_Proofs.lean", ns));
        if !theorem_fns.is_empty() {
            let module_namespace = self::escape::module_render_namespace(&pkg_name, &module.name);
            if let Some(source_dir) = proof_sources_dir {
                let proofs_path = source_dir
                    .join(&pkg_name)
                    .join(format!("{}_Proofs.lean", ns));
                if proofs_path.exists() {
                    return Err(RenderError::Io {
                        what: format!(
                            "monolithic durable proof module is unsupported: {}; migrate each obligation to {}/{}_Proofs/<obligation>.lean",
                            proofs_path.display(), pkg_name, ns
                        ),
                    });
                }
                let shard_dir = source_dir.join(&pkg_name).join(format!("{ns}_Proofs"));
                let mut shard_stems = BTreeSet::new();
                for theorem in &theorem_fns {
                    let stem = proof_shard_stem(&theorem.1.name);
                    if !shard_stems.insert(stem.clone()) {
                        return Err(RenderError::Io {
                            what: format!(
                                "proof shard name collision in {pkg_name}.{ns}: `{stem}`"
                            ),
                        });
                    }
                    let proof_namespace = format!("{pkg_name}.{ns}_Proofs");
                    let proof_root = format!("{proof_namespace}.{stem}");
                    let singleton = [*theorem];
                    let plan = proof_file_plan(
                        &pkg_name,
                        &ns,
                        &module_namespace,
                        Some(&proof_namespace),
                        &singleton,
                        &context,
                    )?;
                    for stub in &plan.stubs {
                        proof_declaration_fingerprints.insert(
                            (module_namespace.clone(), stub.name.clone()),
                            stub.proof_declaration_sha256.clone(),
                        );
                    }
                    source_proof_updates.push(SourceProofUpdate {
                        path: shard_dir.join(format!("{stem}.lean")),
                        root: proof_root,
                        plan,
                    });
                }
            } else {
                let plan = proof_file_plan(
                    &pkg_name,
                    &ns,
                    &module_namespace,
                    None,
                    &theorem_fns,
                    &context,
                )?;
                for stub in &plan.stubs {
                    proof_declaration_fingerprints.insert(
                        (module_namespace.clone(), stub.name.clone()),
                        stub.proof_declaration_sha256.clone(),
                    );
                }
                fs::write(&output_proofs_path, plan.body).map_err(|error| RenderError::Io {
                    what: format!("write({}): {error}", output_proofs_path.display()),
                })?;
                emitted_module_paths.push(format!("{}.{}_Proofs", pkg_name, ns));
            }
        }
    }

    // Identify user packages from the emitted module paths. Each
    // emitted path has form `<pkg>.<ns>`; pull the leading `<pkg>`
    // segment. This way we only declare lean_libs for packages that
    // actually have files on disk. Also dedupe against lemma libs
    // (which the lakefile already declares).
    let lemma_set: std::collections::BTreeSet<&str> =
        lemma_libs.iter().map(|s| s.as_str()).collect();
    let mut user_packages: std::collections::BTreeSet<String> = std::collections::BTreeSet::new();
    for p in &emitted_module_paths {
        if let Some(pkg) = p.split('.').next() {
            if !lemma_set.contains(pkg) {
                user_packages.insert(pkg.to_string());
            }
        }
    }

    // Single shared `Generated/` library at the output root with
    // `AnyKey.lean` / `AnyEvent.lean` / `AnyObject.lean` / `World.lean`.
    // Previously these were emitted PER USER PACKAGE; each package
    // got its own `<pkg>.Generated.AnyKey` -> `inductive AnyKey`
    // declaration. When a file in one package transitively imported
    // a file in another (e.g. `Pyth.Deserialize` <- `Wormhole.*`),
    // Lean rejected the second `AnyKey.ctorIdx` definition: each
    // package's inductive was a separate declaration even though
    // the variant set was globally collected and the bodies were
    // identical.
    //
    // Sharing one inductive across packages is also semantically
    // cleaner: `Mutation` is parameterized over `AnyKey`, so a
    // single `AnyKey` makes cross-package Mutation values
    // interoperate without coercions. See
    // `mutable-references.md` §6 / Umbrella plan "Stretch:
    // properly handling generic Any*" for the broader context;
    // this is the minimal fix that unblocks the lake build, with
    // the per-call-monomorphisation work still ahead.
    let any_key_variants = self::mutation::collect_any_key_in(&context);
    let any_key_body =
        self::mutation::render_any_key_file_in(&any_key_variants, &context, &lemma_libs_set);
    let (any_event_variants, any_object_variants) = self::world::collect_any_event_object(program);
    let any_event_body = self::world::render_any_event_file(&any_event_variants);
    let any_object_body = self::world::render_any_object_file(&any_object_variants);
    let shared_world_body = self::world::render_shared_world_file();

    let shared_gen_dir = output_dir.join("Generated");
    fs::create_dir_all(&shared_gen_dir).map_err(|e| RenderError::Io {
        what: format!("create_dir_all({}): {}", shared_gen_dir.display(), e),
    })?;
    for (name, body) in [
        ("AnyKey.lean", &any_key_body),
        ("AnyEvent.lean", &any_event_body),
        ("AnyObject.lean", &any_object_body),
        ("World.lean", &shared_world_body),
    ] {
        let path = shared_gen_dir.join(name);
        fs::write(&path, body).map_err(|e| RenderError::Io {
            what: format!("write({}): {}", path.display(), e),
        })?;
    }

    // Name-keyed datatype tag table. Import-free, so every generated
    // module (user AND lemma package) can import it without any cycle
    // risk. See `render::struct_idx`.
    self::struct_idx::write_struct_idx_file(program, output_dir).map_err(|e| RenderError::Io {
        what: format!("write Generated/StructIdx.lean: {}", e),
    })?;

    // Per-project closed-universe `TyCode` for heterogeneous-storage
    // natives (`Sui.Bag`, `Sui.ObjectBag`, `Sui.Dynamic_field`,
    // `Sui.Dynamic_object_field`). Always emit, even if no types
    // were collected -- the inductive carries a `dummy` constructor
    // so user files can `import Generated.TyCode` unconditionally
    // and get a valid (if empty) universe for projects that don't
    // exercise heterogeneous storage.
    let dyn_universe = self::dyn_type_universe::collect(program);
    self::dyn_type_universe::write_ty_code_file(&dyn_universe, program, output_dir).map_err(
        |e| RenderError::Io {
            what: format!("write Generated/TyCode.lean: {}", e),
        },
    )?;
    self::dyn_type_universe::write_ty_code_interp_file(
        &dyn_universe,
        &context,
        output_dir,
        &lemma_libs_set,
    )
    .map_err(|e| RenderError::Io {
        what: format!("write Generated/TyCodeInterp.lean: {}", e),
    })?;

    // Per-project closed-universe `ObjType` for types that flow
    // through `Sui::transfer::*` and `Sui::test_scenario::take_*`
    // -- objects that get deposited in / extracted from the World
    // owned / shared / frozen pools. Separate universe from TyCode
    // (which is for bag K/V types) so Bag-containing structs like
    // Vault can appear in ObjType without re-triggering the
    // `_Types -> TyCodeInterp -> _Types` cycle.
    let obj_universe = self::obj_type_universe::collect_in(&context);
    self::obj_type_universe::write_obj_type_file(&obj_universe, program, output_dir).map_err(
        |e| RenderError::Io {
            what: format!("write Generated/ObjType.lean: {}", e),
        },
    )?;
    self::obj_type_universe::write_obj_type_interp_file(
        &obj_universe,
        &context,
        output_dir,
        &lemma_libs_set,
    )
    .map_err(|e| RenderError::Io {
        what: format!("write Generated/ObjTypeInterp.lean: {}", e),
    })?;

    // Per-project closed-universe `BagU` for `Sui::bag::*` /
    // `Sui::object_bag::*` key & value types. Separate, self-contained
    // universe from TyCode (the df universe): a struct's `Bag` field is
    // typed over `BagU`, so a Bag-containing struct can be a `TyCode`
    // (df) value without the `_Types -> TyCodeInterp -> _Types` cycle.
    // BagU EXCLUDES bag-containing structs, keeping the import graph a
    // DAG. See `plans/lean-pipeline/split-bag-df-universes.md`.
    let bag_universe = self::bag_universe::collect_in(&context);
    self::bag_universe::write_bagu_file(&bag_universe, program, output_dir).map_err(|e| {
        RenderError::Io {
            what: format!("write Generated/BagU.lean: {}", e),
        }
    })?;
    self::bag_universe::write_bagu_interp_file(
        &bag_universe,
        &context,
        output_dir,
        &lemma_libs_set,
    )
    .map_err(|e| RenderError::Io {
        what: format!("write Generated/BagUInterp.lean: {}", e),
    })?;

    let mut lakefile = String::new();
    lakefile.push_str(
        "import Lake\nopen Lake DSL\n\npackage new_pipeline_output where\n  fixedToolchain := true\n  -- generated by lean-pipeline::render\n\n",
    );
    for dependency in &proof_automation_dependencies {
        lakefile.push_str(&format!(
            "require {} from \"{}\"\n",
            dependency.name,
            lake_path_literal(&dependency.directory)
        ));
    }
    if !proof_automation_dependencies.is_empty() {
        lakefile.push('\n');
    }
    for lib in &lemma_libs {
        lakefile.push_str(&format!(
            "lean_lib {} where\n  roots := #[`{}]\n  globs := #[.submodules `{}]\n\n",
            lib, lib, lib
        ));
    }
    // The shared `Generated` lean_lib carries the global AnyKey /
    // AnyEvent / AnyObject inductives plus the `World` abbrev. Every
    // user package imports `Generated.AnyKey` / `Generated.World` to
    // see the inductives; sharing one definition avoids cross-package
    // `AnyKey.ctorIdx` collisions when one package transitively
    // imports another.
    lakefile.push_str(
        "lean_lib Generated where\n  roots := #[`Generated]\n  globs := #[.submodules `Generated]\n\n",
    );
    for lib in &user_packages {
        lakefile.push_str(&format!(
            "@[default_target]\nlean_lib {} where\n  roots := #[`{}]\n  globs := #[.submodules `{}]\n\n",
            lib, lib, lib
        ));
    }
    // NON-default `Proofs` lib. The foxy `spec_proof_with_lean` skill writes
    // per-spec proof files under `Proofs/` (module `Proofs.<Module>_<spec>`).
    // Declaring the lib puts them in the build graph so
    // `lake build Proofs.<Module>_<spec>` type-checks a single proof through
    // lake -- making its pass/fail trustworthy by construction, and removing
    // the old workaround (the `::` in the output dir name breaks `lake env
    // lean`'s LEAN_PATH, which forced a colon-free-symlink hack per proof).
    // It is deliberately NOT a `@[default_target]`: an in-progress or
    // `sorry`-bearing scaffold must never redden the whole-package `lake
    // build`. Emitted in legacy/output-proof mode only. When source proofs
    // are configured, the source tree owns proof modules instead, via exact
    // roots below, and those committed proofs are default targets.
    if proof_sources_dir.is_none() {
        lakefile.push_str(
            "lean_lib Proofs where\n  roots := #[`Proofs]\n  globs := #[.submodules `Proofs]\n\n",
        );
    }
    if let Some(source_dir) = proof_sources_dir {
        let mut roots = discover_source_proof_roots(source_dir)?;
        roots.extend(
            source_proof_updates
                .iter()
                .map(|update| update.root.clone()),
        );
        roots.sort();
        roots.dedup();
        if !roots.is_empty() {
            lakefile.push_str("@[default_target]\nlean_lib SourceProofs where\n");
            lakefile.push_str(&format!(
                "  srcDir := \"{}\"\n",
                lake_path_literal(&path_relative_to(output_dir, source_dir))
            ));
            lakefile.push_str("  roots := #[");
            for (i, root) in roots.iter().enumerate() {
                if i > 0 {
                    lakefile.push_str(", ");
                }
                lakefile.push('`');
                lakefile.push_str(root);
            }
            lakefile.push_str("]\n\n");
        }
    }
    let lakefile_path = output_dir.join("lakefile.lean");
    fs::write(&lakefile_path, &lakefile).map_err(|e| RenderError::Io {
        what: format!("write({}): {}", lakefile_path.display(), e),
    })?;
    let lean_toolchain_path = output_dir.join("lean-toolchain");
    fs::write(&lean_toolchain_path, GENERATED_LEAN_TOOLCHAIN).map_err(|e| RenderError::Io {
        what: format!("write({}): {}", lean_toolchain_path.display(), e),
    })?;

    let manifest = LakeManifest {
        version: "1.2.0",
        packages_dir: ".lake/packages",
        packages: proof_automation_dependencies
            .iter()
            .map(|dependency| LakeManifestPathDependency {
                dependency_type: "path",
                scope: "",
                name: &dependency.name,
                manifest_file: "lake-manifest.json",
                inherited: false,
                dir: &dependency.directory,
                config_file: &dependency.config_file,
            })
            .collect(),
        name: "new_pipeline_output",
        lake_dir: ".lake",
        fixed_toolchain: true,
    };
    let manifest = serde_json::to_string_pretty(&manifest).map_err(|error| RenderError::Io {
        what: format!("serialize generated Lake manifest: {error}"),
    })? + "\n";
    let manifest_path = output_dir.join("lake-manifest.json");
    fs::write(&manifest_path, manifest).map_err(|e| RenderError::Io {
        what: format!("write({}): {}", manifest_path.display(), e),
    })?;

    validate_internal_imports(output_dir, &lemma_libs, &user_packages).map_err(|e| {
        RenderError::Io {
            what: format!("validate_internal_imports: {e}"),
        }
    })?;

    let test_declarations_path = output_dir.join(TEST_DECLARATIONS_MANIFEST);
    if loop_mode == loop_termination::LoopMode::Test {
        write_test_declarations_manifest(program, output_dir)?;
    } else {
        match fs::remove_file(&test_declarations_path) {
            Ok(()) => {}
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => {}
            Err(error) => {
                return Err(RenderError::Io {
                    what: format!("remove_file({}): {error}", test_declarations_path.display()),
                });
            }
        }
    }
    write_obligations_manifest(program, output_dir, &proof_declaration_fingerprints)?;
    self::native_models::classify_and_write_with_overlays(
        program,
        output_dir,
        lemmas_dir,
        native_policy_dir,
        user_package,
        root_package,
        loop_mode,
        &copied_from_lemmas,
        &copied_from_package_overlays,
    )?;
    write_abort_origins_sidecar(program, output_dir)?;

    Ok(StagedRender {
        source_proof_updates,
        user_packages,
        lemma_libs,
    })
}

/// Plan removal of files sitting in renderer-owned directories that this
/// render does not produce.
///
/// The renderer owns, in full, every `.lean` under each user package, each
/// lemma library, `Generated/` and `proof_scaffolds/`: the plan is the whole
/// staging tree, so anything it does not contain is not ours. `publish`
/// already drops manifest entries this plan omits -- but a manifest diff can
/// only reclaim what the manifest LISTS. Files a different writer dropped into
/// those directories are unowned, so no diff ever reaches them.
///
/// The concrete such writer is the retired `move-prover-lean-backend`, which
/// renders into the same output tree whenever `--new-pipeline` is omitted and
/// keeps no manifest. Its bundle carries six Prelude modules the live bundle
/// does not (`AbortsTactics`, `BoundedArith`, `Combinatorics`,
/// `LoopTermination`, `MoveType`, `WorldSimp`) plus lowercase `_types` /
/// `_types_skeleton` splits, and while the manifest gate below was
/// bootstrap-only those survived every subsequent render. That is not cosmetic:
/// `Prelude/AbortsTactics.lean` declares a `syntax` tactic, and the audit's
/// import-time-execution gate walks every `.lean` under the output root, so a
/// once-contaminated corpus could never be audited again even though nothing
/// imported the module.
///
/// Before the manifest exists the sweep also adopts the pre-manifest sidecars.
/// Once it exists the sweep stays on `.lean` files under non-preserved roots --
/// the surface the audit reads, and the one a stale render can poison.
fn add_unowned_generated_removals(
    plan: &mut self::materialize::RenderPlan,
    output_dir: &Path,
    user_packages: &BTreeSet<String>,
    lemma_libs: &[String],
) -> RenderResult<()> {
    let bootstrap = !output_dir
        .join(self::materialize::OWNED_MANIFEST_FILE)
        .exists();

    let mut candidates = BTreeSet::new();
    for package in user_packages {
        let directory = output_dir.join(package);
        let entries = match std::fs::read_dir(&directory) {
            Ok(entries) => entries,
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => continue,
            Err(error) => {
                return Err(RenderError::Io {
                    what: format!(
                        "scan legacy generated package {}: {error}",
                        directory.display()
                    ),
                });
            }
        };
        for entry in entries {
            let entry = entry.map_err(|error| RenderError::Io {
                what: format!(
                    "scan legacy generated package {}: {error}",
                    directory.display()
                ),
            })?;
            let path = entry.path();
            let metadata = std::fs::symlink_metadata(&path).map_err(|error| RenderError::Io {
                what: format!("inspect legacy generated path {}: {error}", path.display()),
            })?;
            if metadata.is_file()
                && path.extension().and_then(|value| value.to_str()) == Some("lean")
            {
                candidates.insert(path);
            }
        }
    }
    for library in lemma_libs {
        collect_legacy_generated_files(&output_dir.join(library), &mut candidates)?;
    }
    collect_legacy_generated_files(&output_dir.join("Generated"), &mut candidates)?;
    collect_legacy_generated_files(&output_dir.join("proof_scaffolds"), &mut candidates)?;
    if bootstrap {
        for relative in [
            Path::new(TEST_DECLARATIONS_MANIFEST),
            Path::new(crate::ir::ABORT_ORIGINS_FILE),
        ] {
            let path = output_dir.join(relative);
            if path.is_file() {
                candidates.insert(path);
            }
        }
    }

    let mut reclaimed: Vec<PathBuf> = Vec::new();
    for path in candidates {
        let relative = path.strip_prefix(output_dir).map_err(|_| RenderError::Io {
            what: format!(
                "legacy generated path escaped output {}: {}",
                output_dir.display(),
                path.display()
            ),
        })?;
        if !bootstrap {
            if path.extension().and_then(|value| value.to_str()) != Some("lean") {
                continue;
            }
            // `plan.reclaim` REFUSES a preserved root rather than skipping it,
            // so filter here: a lemma library named `Proofs` must not turn a
            // render into a hard error.
            let preserved = relative
                .components()
                .next()
                .and_then(|component| component.as_os_str().to_str())
                .map(self::materialize::is_preserved_root)
                .unwrap_or(true);
            if preserved {
                continue;
            }
        }
        if !plan.files().contains_key(relative) && !plan.removals().contains(relative) {
            if bootstrap {
                plan.remove(relative)?;
            } else {
                // Every candidate above came from a directory the renderer owns
                // wholesale, which is the containment `reclaim` requires.
                plan.reclaim(relative)?;
                reclaimed.push(relative.to_path_buf());
            }
        }
    }
    if !reclaimed.is_empty() {
        // Deleting a file no manifest claims is worth saying out loud: it means
        // something else wrote into this output tree, and the overwhelmingly
        // likely something is a `sui-lean` run that omitted `--new-pipeline`.
        eprintln!(
            "new-pipeline: reclaimed {} unowned generated file(s) left in the output tree by \
             another renderer (most likely a run without `--new-pipeline`):",
            reclaimed.len()
        );
        for path in &reclaimed {
            eprintln!("  {}", path.display());
        }
    }
    Ok(())
}

fn collect_legacy_generated_files(
    directory: &Path,
    files: &mut BTreeSet<PathBuf>,
) -> RenderResult<()> {
    let entries = match std::fs::read_dir(directory) {
        Ok(entries) => entries,
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => return Ok(()),
        Err(error) => {
            return Err(RenderError::Io {
                what: format!(
                    "scan legacy generated directory {}: {error}",
                    directory.display()
                ),
            });
        }
    };
    for entry in entries {
        let entry = entry.map_err(|error| RenderError::Io {
            what: format!(
                "scan legacy generated directory {}: {error}",
                directory.display()
            ),
        })?;
        let path = entry.path();
        let metadata = std::fs::symlink_metadata(&path).map_err(|error| RenderError::Io {
            what: format!("inspect legacy generated path {}: {error}", path.display()),
        })?;
        if metadata.is_dir() {
            collect_legacy_generated_files(&path, files)?;
        } else if metadata.is_file() {
            files.insert(path);
        } else {
            return Err(RenderError::Io {
                what: format!(
                    "legacy generated tree contains a non-regular entry: {}",
                    path.display()
                ),
            });
        }
    }
    Ok(())
}

fn remove_empty_retired_scaffold_directories(output_dir: &Path) {
    fn remove_empty_tree(directory: &Path) -> std::io::Result<()> {
        let entries = match std::fs::read_dir(directory) {
            Ok(entries) => entries,
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => return Ok(()),
            Err(error) => return Err(error),
        };
        for entry in entries {
            let path = entry?.path();
            let metadata = std::fs::symlink_metadata(&path)?;
            if metadata.is_dir() && !metadata.file_type().is_symlink() {
                remove_empty_tree(&path)?;
            }
        }
        match std::fs::remove_dir(directory) {
            Ok(()) => Ok(()),
            Err(error)
                if matches!(
                    error.kind(),
                    std::io::ErrorKind::NotFound | std::io::ErrorKind::DirectoryNotEmpty
                ) =>
            {
                Ok(())
            }
            Err(error) => Err(error),
        }
    }

    let retired = output_dir.join("proof_scaffolds");
    if let Err(error) = remove_empty_tree(&retired) {
        eprintln!(
            "unable to remove empty retired scaffold directories under {}: {error}",
            retired.display()
        );
    }
}

pub fn write_abort_origins_sidecar(program: &Program, output_dir: &Path) -> RenderResult<()> {
    use crate::ir::{AbortPayloadMode, ABORT_ORIGINS_FILE};

    let path = output_dir.join(ABORT_ORIGINS_FILE);
    if program.abort_provenance.mode == AbortPayloadMode::Proof {
        match std::fs::remove_file(&path) {
            Ok(()) => {}
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => {}
            Err(error) => {
                return Err(RenderError::Io {
                    what: format!("remove stale {}: {error}", path.display()),
                });
            }
        }
        return Ok(());
    }

    std::fs::create_dir_all(output_dir).map_err(|error| RenderError::Io {
        what: format!("create render output {}: {error}", output_dir.display()),
    })?;
    let document = program.abort_provenance.document();
    document.validate().map_err(|error| RenderError::Io {
        what: format!("invalid {}: {error}", path.display()),
    })?;
    let contents = toml::to_string_pretty(&document).map_err(|error| RenderError::Io {
        what: format!("serialize {}: {error}", path.display()),
    })?;
    let mut temporary =
        tempfile::NamedTempFile::new_in(output_dir).map_err(|error| RenderError::Io {
            what: format!(
                "create temporary abort origins under {}: {error}",
                output_dir.display()
            ),
        })?;
    std::io::Write::write_all(&mut temporary, contents.as_bytes()).map_err(|error| {
        RenderError::Io {
            what: format!(
                "write temporary abort origins for {}: {error}",
                path.display()
            ),
        }
    })?;
    std::io::Write::flush(&mut temporary).map_err(|error| RenderError::Io {
        what: format!(
            "flush temporary abort origins for {}: {error}",
            path.display()
        ),
    })?;
    temporary
        .as_file()
        .sync_all()
        .map_err(|error| RenderError::Io {
            what: format!(
                "sync temporary abort origins for {}: {error}",
                path.display()
            ),
        })?;
    temporary.persist(&path).map_err(|error| RenderError::Io {
        what: format!("persist abort origins {}: {}", path.display(), error.error),
    })?;
    Ok(())
}

pub fn read_abort_origins_sidecar(
    output_dir: &Path,
) -> RenderResult<crate::ir::AbortOriginsDocument> {
    use crate::ir::ABORT_ORIGINS_FILE;

    let path = output_dir.join(ABORT_ORIGINS_FILE);
    let input = std::fs::read_to_string(&path).map_err(|error| RenderError::Io {
        what: format!("read {}: {error}", path.display()),
    })?;
    let document: crate::ir::AbortOriginsDocument =
        toml::from_str(&input).map_err(|error| RenderError::Io {
            what: format!("parse {}: {error}", path.display()),
        })?;
    document.validate().map_err(|error| RenderError::Io {
        what: format!("invalid {}: {error}", path.display()),
    })?;
    Ok(document)
}

/// Follow imports reachable from emitted user-package modules and reject a
/// missing module in a renderer-owned package. This is a narrow generation
/// preflight; Lean remains the authority for parsing and elaborating imports.
/// Manufacturing an empty namespace would hide a real dependency gap.
fn validate_internal_imports(
    output_dir: &Path,
    lemma_libs: &[String],
    user_packages: &BTreeSet<String>,
) -> std::io::Result<()> {
    let mut internal_roots: BTreeSet<String> = lemma_libs.iter().cloned().collect();
    internal_roots.extend(user_packages.iter().cloned());
    internal_roots.insert("Generated".to_string());

    let mut modules = BTreeMap::new();
    collect_lean_modules(output_dir, output_dir, &mut modules)?;
    let mut pending: Vec<String> = modules
        .keys()
        .filter(|module| {
            module
                .split('.')
                .next()
                .is_some_and(|root| user_packages.contains(root))
        })
        .cloned()
        .collect();
    let mut visited = BTreeSet::new();
    let mut missing = BTreeSet::new();
    while let Some(module) = pending.pop() {
        if !visited.insert(module.clone()) {
            continue;
        }
        let Some(path) = modules.get(&module) else {
            continue;
        };
        for import in imports_from_file(path)? {
            if modules.contains_key(&import) {
                pending.push(import);
            } else if import
                .split('.')
                .next()
                .is_some_and(|root| internal_roots.contains(root))
            {
                missing.insert(import);
            }
        }
    }
    if !missing.is_empty() {
        return Err(std::io::Error::new(
            std::io::ErrorKind::NotFound,
            format!(
                "generated Lean has unresolved internal imports: {}",
                missing.into_iter().collect::<Vec<_>>().join(", ")
            ),
        ));
    }
    Ok(())
}

fn collect_lean_modules(
    root: &Path,
    directory: &Path,
    modules: &mut BTreeMap<String, PathBuf>,
) -> std::io::Result<()> {
    for entry in std::fs::read_dir(directory)? {
        let entry = entry?;
        let path = entry.path();
        if path.is_dir() {
            collect_lean_modules(root, &path, modules)?;
        } else if path.extension().and_then(|s| s.to_str()) == Some("lean") {
            let relative = path.strip_prefix(root).expect("walk stays beneath root");
            let mut parts: Vec<String> = relative
                .parent()
                .into_iter()
                .flat_map(Path::components)
                .filter_map(|component| component.as_os_str().to_str().map(str::to_string))
                .collect();
            parts.push(
                path.file_stem()
                    .and_then(|stem| stem.to_str())
                    .ok_or_else(|| {
                        std::io::Error::new(
                            std::io::ErrorKind::InvalidData,
                            format!("generated Lean path is not UTF-8: {}", path.display()),
                        )
                    })?
                    .to_string(),
            );
            modules.insert(parts.join("."), path);
        }
    }
    Ok(())
}

fn imports_from_file(path: &Path) -> std::io::Result<Vec<String>> {
    Ok(std::fs::read_to_string(path)?
        .lines()
        .filter_map(|line| line.strip_prefix("import "))
        .map(str::trim)
        .map(str::to_string)
        .collect())
}

fn collect_imports(dir: &Path, lib_name: &str, out: &mut Vec<String>) -> std::io::Result<()> {
    walk_imports(dir, lib_name, &mut Vec::new(), out)
}

fn walk_imports(
    cur: &Path,
    lib_name: &str,
    rel: &mut Vec<String>,
    out: &mut Vec<String>,
) -> std::io::Result<()> {
    use std::fs;
    if !cur.is_dir() {
        return Ok(());
    }
    for entry in fs::read_dir(cur)? {
        let entry = entry?;
        let path = entry.path();
        let name = match entry.file_name().into_string() {
            Ok(s) => s,
            Err(_) => continue,
        };
        if path.is_dir() {
            rel.push(name);
            walk_imports(&path, lib_name, rel, out)?;
            rel.pop();
        } else if name.ends_with(".lean") {
            let stem = &name[..name.len() - ".lean".len()];
            let mut parts = vec![lib_name.to_string()];
            parts.extend(rel.iter().cloned());
            parts.push(stem.to_string());
            out.push(parts.join("."));
        }
    }
    Ok(())
}

/// Copy a lemma library into the output tree. `keep_companion` decides each
/// `*Lemmas.lean` file: a proof-lemma companion is copied only when the
/// program can build it (its subject's required constants survived pruning)
/// -- see `render/lemma_companions.rs`. Every other file is copied verbatim.
fn copy_dir_recursive(
    src: &Path,
    dst: &Path,
    copied: &mut HashSet<PathBuf>,
    keep_companion: &dyn Fn(&Path) -> bool,
) -> std::io::Result<()> {
    use std::fs;
    let src_metadata = fs::symlink_metadata(src)?;
    if src_metadata.file_type().is_symlink() || !src_metadata.is_dir() {
        return Err(std::io::Error::new(
            std::io::ErrorKind::InvalidInput,
            format!(
                "lemma source must be a regular directory, not a symlink: {}",
                src.display()
            ),
        ));
    }
    match fs::symlink_metadata(dst) {
        Ok(metadata) if metadata.file_type().is_symlink() || !metadata.is_dir() => {
            return Err(std::io::Error::new(
                std::io::ErrorKind::InvalidInput,
                format!(
                    "lemma destination must be a regular directory, not a symlink: {}",
                    dst.display()
                ),
            ));
        }
        Ok(_) => {}
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => fs::create_dir(dst)?,
        Err(error) => return Err(error),
    }
    for entry in fs::read_dir(src)? {
        let entry = entry?;
        let src_path = entry.path();
        let dst_path = dst.join(entry.file_name());
        let file_type = entry.file_type()?;
        if file_type.is_symlink() {
            return Err(std::io::Error::new(
                std::io::ErrorKind::InvalidInput,
                format!("lemma source must not be a symlink: {}", src_path.display()),
            ));
        }
        if file_type.is_dir() {
            copy_dir_recursive(&src_path, &dst_path, copied, keep_companion)?;
        } else if file_type.is_file() {
            match fs::symlink_metadata(&dst_path) {
                Ok(metadata) if metadata.file_type().is_symlink() || !metadata.is_file() => {
                    return Err(std::io::Error::new(
                        std::io::ErrorKind::InvalidInput,
                        format!(
                            "lemma destination must be a regular file, not a symlink: {}",
                            dst_path.display()
                        ),
                    ));
                }
                Ok(_) => {}
                Err(error) if error.kind() == std::io::ErrorKind::NotFound => {}
                Err(error) => return Err(error),
            }
            let is_companion = entry
                .file_name()
                .to_str()
                .is_some_and(|n| n.ends_with(self::lemma_companions::COMPANION_SUFFIX));
            if is_companion && !keep_companion(&src_path) {
                // A companion this program cannot build must also not be
                // LEFT behind by an earlier render. The per-lib `lean_lib`
                // globs submodules, so a stale copy stays a nameable
                // `lake build <Lib>.<X>Lemmas` target -- and the emitted
                // import, if the subject later regains the constant, would
                // pick up whichever text happens to be on disk.
                if dst_path.is_file() {
                    fs::remove_file(&dst_path)?;
                }
                continue;
            }
            std::fs::copy(&src_path, &dst_path)?;
            copied.insert(dst_path);
        } else {
            return Err(std::io::Error::new(
                std::io::ErrorKind::InvalidInput,
                format!(
                    "lemma source must contain only regular files and directories: {}",
                    src_path.display()
                ),
            ));
        }
    }
    Ok(())
}

/// Sort structs in dependency order (deps first) within their
/// module. A struct `B` whose fields reference struct `A` (directly
/// or via generic parameterisation) must be emitted after `A` so the
/// Lean parser sees `A`'s definition first.
///
/// Cross-module dependencies are ignored here -- they're handled by
/// the namespace boundary (a struct can refer to one in another
/// namespace because the renderer emits each namespace block
/// independently).
fn topo_sort_structs<'a>(
    items: &mut Vec<(&'a StructId, &'a crate::ir::Struct)>,
    program: &Program,
) {
    use std::collections::BTreeMap;

    let in_module: std::collections::BTreeSet<StructId> =
        items.iter().map(|(id, _)| **id).collect();

    // For each item, collect the StructIds it depends on (same module only).
    let mut deps: BTreeMap<StructId, Vec<StructId>> = BTreeMap::new();
    let mut id_to_item: BTreeMap<StructId, &'a crate::ir::Struct> = BTreeMap::new();
    for (id, s) in items.iter() {
        deps.insert(**id, struct_field_struct_ids(s, &in_module));
        id_to_item.insert(**id, *s);
    }

    // Kahn's algorithm with deterministic ordering (BTreeMap +
    // sorted ready set).
    let mut indeg: BTreeMap<StructId, usize> = BTreeMap::new();
    for &id in id_to_item.keys() {
        indeg.entry(id).or_insert(0);
    }
    let mut reverse: BTreeMap<StructId, Vec<StructId>> = BTreeMap::new();
    for (&src, ds) in &deps {
        for &dst in ds {
            *indeg.entry(src).or_insert(0) += 1;
            reverse.entry(dst).or_default().push(src);
        }
    }
    let mut ready: Vec<StructId> = indeg
        .iter()
        .filter(|(_, &d)| d == 0)
        .map(|(&id, _)| id)
        .collect();
    ready.sort();
    let mut out: Vec<StructId> = Vec::new();
    while let Some(id) = ready.pop() {
        out.push(id);
        if let Some(downstream) = reverse.get(&id).cloned() {
            for d in downstream {
                let v = indeg.get_mut(&d).expect("indeg present");
                *v -= 1;
                if *v == 0 {
                    ready.push(d);
                }
            }
            ready.sort();
        }
    }
    // Any unsorted residue is a cycle -- append in original order so
    // the output is still complete (Lean will reject the cycle, but
    // the rest of the file builds).
    if out.len() < items.len() {
        for (id, _) in items.iter() {
            if !out.contains(id) {
                out.push(**id);
            }
        }
    }

    let mut id_index: BTreeMap<StructId, (&'a StructId, &'a crate::ir::Struct)> = BTreeMap::new();
    for (id_ref, s_ref) in items.iter() {
        id_index.insert(**id_ref, (*id_ref, *s_ref));
    }
    let mut new_items: Vec<(&'a StructId, &'a crate::ir::Struct)> = Vec::with_capacity(items.len());
    for id in &out {
        if let Some(entry) = id_index.get(id) {
            new_items.push(*entry);
        }
    }
    *items = new_items;
}

/// Collect struct ids referenced from `s`'s field types -- both
/// directly (a field type is `Struct { id }`) and inside generic
/// instantiations (a field type is `Vector(Struct { id })` etc.).
/// Restricted to `same_module` so we only honour intra-module
/// ordering.
fn struct_field_struct_ids(
    s: &crate::ir::Struct,
    same_module: &std::collections::BTreeSet<StructId>,
) -> Vec<StructId> {
    let mut out: std::collections::BTreeSet<StructId> = Default::default();
    fn walk_ty(
        ty: &crate::ir::Type,
        same_module: &std::collections::BTreeSet<StructId>,
        out: &mut std::collections::BTreeSet<StructId>,
    ) {
        use crate::ir::Type::*;
        match ty {
            Struct {
                struct_id,
                type_args,
            } => {
                if same_module.contains(struct_id) {
                    out.insert(*struct_id);
                }
                for t in type_args {
                    walk_ty(t, same_module, out);
                }
            }
            Vector(inner) | Reference(inner) => walk_ty(inner, same_module, out),
            MutableRef { inner, root } => {
                walk_ty(inner, same_module, out);
                walk_ty(root, same_module, out);
            }
            Tuple(ts) => {
                for t in ts {
                    walk_ty(t, same_module, out);
                }
            }
            Unit | Bool | Prop | UInt(_) | Address | TypeParam(_) => {}
        }
    }
    for f in &s.fields {
        walk_ty(&f.field_type, same_module, &mut out);
    }
    if let Some(variants) = &s.variants {
        for v in variants {
            for f in &v.fields {
                walk_ty(&f.field_type, same_module, &mut out);
            }
        }
    }
    out.into_iter().collect()
}

/// Render exactly one module's `namespace <X> ... end <X>` block to a
/// fresh `String`. Used by `render_program_to_dir` to emit one Lean
/// source file per Move module.
///
/// Which slice of a Move module to render.
///
/// User packages are split into TWO Lean files per Move module:
///   * `<Pkg>/<Mod>_Types.lean` -- struct/enum definitions only.
///     Used as a dependency by other files (and by
///     `Generated/TyCode.lean`). Has minimal imports -- only the
///     other `_Types` files whose structs appear as field types.
///   * `<Pkg>/<Mod>.lean` -- explicit native models + function bodies.
///     Imports its own `_Types`, plus other modules' regular files
///     (which transitively bring in their `_Types`), plus
///     `Generated.TyCode` when the module uses heterogeneous
///     storage.
///
/// Splitting like this breaks the cycle that would otherwise form
/// between user files and the renderer-emitted
/// `Generated/TyCode.lean`: TyCode imports the per-project user
/// types it interprets, so it must import the `_Types` files; user
/// `.lean` files import `Generated.TyCode` for the Universe /
/// HasCode instances they need at every `Bag.add` / `Bag.borrow`
/// call site. Without the split, both files would want to import
/// each other; with the split, only `<Mod>.lean` imports
/// `Generated.TyCode`, and `Generated.TyCode` imports only
/// `<Mod>_Types`, so the import graph is a DAG.
///
/// Lemma packages (Sui, MoveStdlib, Prover, Pyth, ...) are kept
/// as single files (`Full`): their structs are all `is_native`
/// (provided by the prelude), so a separate `_Types` slice would
/// be empty.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ModuleKind {
    /// Single-file mode -- structs + explicit native models + functions in one
    /// `<Mod>.lean`. Used for lemma packages and as the
    /// backward-compatible default for tests.
    Full,
    /// `<Mod>_Types.lean` slice -- structs / enums only.
    Types,
    /// `<Mod>.lean` slice -- explicit native models + functions only.
    Funcs,
}

fn render_single_module(
    context: &self::context::RenderContext<'_>,
    mid: ModId,
    kind: ModuleKind,
) -> RenderResult<String> {
    render_single_module_filtered(context, mid, kind, None)
}

/// Same as `render_single_module` but with an optional struct-ID
/// allowlist. When `struct_keep` is `Some`, only structs in the set
/// are emitted (in addition to the usual `module_id == mid` filter).
/// Used by the user-package emission path to split a module's
/// structs into the `_Types_Skeleton` (Bag-free) and `_Types`
/// (Bag-containing) files.
fn render_single_module_filtered(
    context: &self::context::RenderContext<'_>,
    mid: ModId,
    kind: ModuleKind,
    struct_keep: Option<&std::collections::HashSet<StructId>>,
) -> RenderResult<String> {
    use std::collections::HashSet;
    let program = context.program;
    let module = program
        .modules
        .get(&mid)
        .ok_or(RenderError::UnknownModId { id: mid })?;
    if matches!(kind, ModuleKind::Full | ModuleKind::Funcs) {
        self::globals::ensure_threaded(program)?;
    }
    let namespace = self::escape::module_render_namespace(&module.package_name, &module.name);

    let mut w = LeanWriter::new(String::new());
    w.write("namespace ");
    w.line(&namespace);
    w.newline();

    if matches!(kind, ModuleKind::Full | ModuleKind::Funcs) {
        let opaque_const_aliases = module_opaque_const_aliases(program, mid);
        if !opaque_const_aliases.is_empty() {
            emit_opaque_const_aliases(&mut w, &opaque_const_aliases);
        }
    }

    if matches!(kind, ModuleKind::Full | ModuleKind::Types) {
        let mut module_structs: Vec<(&StructId, &crate::ir::Struct)> = program
            .structs
            .iter()
            .filter(|(_, s)| s.module_id == mid)
            .filter(|(sid, _)| struct_keep.map_or(true, |keep| keep.contains(sid)))
            .collect();
        topo_sort_structs(&mut module_structs, program);
        for (_, s) in module_structs {
            if s.is_native {
                // The prelude provides this struct's body (either via a
                // `<Module>Natives.lean` sibling or a `Prelude/*.lean`
                // file like `Prover.World.World`). Emitting another
                // `structure` here would conflict with the prelude
                // definition and/or with file-scoped `local notation`
                // declarations that reference the prelude type.
                continue;
            }
            if crate::stage_07_dejumps::aborts_defunctionalize::is_loop_step_struct(s) {
                // Defunctionalized loop-step inductive: emitted in the impl
                // (Funcs) file where its impl-only `cont` payload types are in
                // scope. See the Funcs branch below.
                continue;
            }
            render_struct(s, context, Some(&namespace), &mut w)?;
        }
    }

    if matches!(kind, ModuleKind::Full | ModuleKind::Funcs) {
        self::globals::render_module_globals(program, mid, &namespace, &mut w)?;
    }

    // Ghost-opaque decl fids: emitted as generated `opaque` declarations
    // below (never as native fallback bodies -- an opaque with another
    // sibling would be a duplicate definition).
    let ghost_opaque_fids: HashSet<FunId> = program
        .ghost_opaque_outputs
        .values()
        .flat_map(|v| v.iter().map(|(_, _, f)| *f))
        .collect();

    if matches!(kind, ModuleKind::Full | ModuleKind::Funcs) {
        // Open a MINIMAL `noncomputable section` around the function payload
        // only. The quantifier-traversal helpers are noncomputable, so the
        // function bodies may use noncomputable World operations and need the
        // modifier -- but
        // the type definitions above must stay OUTSIDE it: a `deriving Inhabited`
        // on a Move enum inside a `noncomputable section` yields a noncomputable
        // derived instance and panics the LCNF compiler. Loop-step inductives
        // carry no `deriving`, so keeping them inside the section is harmless.
        w.line("noncomputable section");
        w.newline();

        // Defunctionalized loop-step inductives live in the impl (Funcs) file,
        // not the Types file: their `cont` variant carries impl-only types (the
        // `World` `local notation`, project structs imported via `Generated.*`)
        // that the restricted Types files do not bring into scope. Emit them
        // here, ahead of the loop functions that match on them.
        let mut step_structs: Vec<(&StructId, &crate::ir::Struct)> = program
            .structs
            .iter()
            .filter(|(_, s)| s.module_id == mid)
            .filter(|(_, s)| {
                crate::stage_07_dejumps::aborts_defunctionalize::is_loop_step_struct(s)
            })
            .collect();
        topo_sort_structs(&mut step_structs, program);
        for (_, s) in step_structs {
            render_struct(s, context, Some(&namespace), &mut w)?;
        }

        // `end_transaction` is a renderer-owned executable test model. It
        // cannot live in the sibling because its result mentions the
        // module-local `TransactionEffects` structure. No other NativeDecl
        // receives a synthesized body.
        if module.package_name == "Sui" && module.name == "test_scenario" {
            if let Some((_, decl)) = program.natives.decls.iter().find(|(fid, decl)| {
                decl.module == mid
                    && !ghost_opaque_fids.contains(fid)
                    && self::native_models::is_renderer_owned_end_transaction_model(decl, program)
            }) {
                self::function::render_end_transaction_model(
                    decl,
                    program,
                    Some(&namespace),
                    &mut w,
                )?;
            }
        }

        // Opaque ghost-output declarations (ensures-published ghosts,
        // ghost-support.md Part 4): emitted unconditionally -- even when a
        // natives sibling covers this module's ordinary natives, the
        // sibling cannot declare per-program synthesised symbols.
        self::function::render_ghost_opaque_decls(program, mid, Some(&namespace), &mut w);

        let module_funcs: Vec<(&FunId, &crate::ir::Function)> = program
            .functions
            .iter()
            .filter(|(_, f)| f.module == mid)
            .collect();
        let sccs = compute_function_sccs(&module_funcs, program);
        emit_function_sccs(&sccs, context, &namespace, &mut w)?;

        w.line("end");
        w.newline();
    }

    w.write("end ");
    w.line(&namespace);
    w.newline();
    let _ = HashSet::<i32>::new(); // appease unused-import lint suppressors
    Ok(w.into_inner())
}

/// The attribute the wide-literal `.val` facts carry.
///
/// `move_effect` is the channel that makes them REACHABLE: every `move_norm*`
/// form applies it, including the `only [...]` forms, so each rung of the
/// `move_auto` ladder sees the fact. The other two channels were measured and
/// rejected. `move_auto_base` is frozen name-for-name by `checkMoveAutoBase`,
/// so a generated tag into it makes every `move_auto` call in the file fail
/// with "move_auto_base was extended or altered". `simp` is a no-op for the
/// ladder -- every rung is `simp only` / `grind only` / aesop with
/// `enableSimp := false` -- and it is not merely inert: made ambient over a
/// corpus it changes the normal form the corpora's OWN hand-written `simp`
/// steps were written against, which broke existing proof text in the probe
/// runs while closing nothing the ladder could not already reach.
///
/// The `move_effect` contract is termination, not confluence: the right-hand
/// side must be strictly smaller than the left in the "runtime operations
/// applied" measure. `<alias>.val = <literal>` removes a `.val` projection on
/// an opaque constant and introduces a bare numeral, so it can never re-enter
/// its own left-hand head.
const OPAQUE_CONST_ALIAS_VAL_ATTR: &str = "@[move_effect]";

/// Module that declares the `move_effect` attribute syntax. A module emitting
/// alias `_val` facts must import it (`register_simp_attr` syntax is usable
/// only after import).
const MOVE_AUTO_ATTR_MODULE: &str = "Prover.MoveAutoAttr";

/// `2^64`, as canonical decimal. A `.val` fact is registered only for literals
/// STRICTLY BELOW this.
///
/// The key is the literal's VALUE, never its declared width: the generator
/// emits an alias for any constant over 4096 at whatever Move type it appears
/// in, so `large_uint_u256_1048576` is a small value at a wide type and is
/// perfectly safe, while `large_uint_u128_79226673515401279992447579055` is not.
///
/// The ceiling is a measured one. `move_norm_all` rewrites the projection to a
/// numeral in hypotheses as well as the goal, and a rung that then hands a 29+
/// digit literal to `grind` -- whose cutsat / ring / linarith engines previously
/// saw an opaque ATOM there -- explodes: momentum's `Sqrt_price_math_Proofs`
/// went from 26 s to an 18.2 GB OOM, and `maxHeartbeats` does not interrupt it,
/// so the failure mode is a kill rather than a rung timeout. De-registering
/// exactly the >= 2^64 facts in that module's scope returned it to 6 s.
/// `omega` handles wide literals fine; `grind` is where the cost lives.
const MOVE_EFFECT_VALUE_CEILING: &str = "18446744073709551616";

/// Attribute carried by the `_val` facts the value gate EXCLUDES. A
/// `register_simp_attr` set (declared in [`MOVE_AUTO_ATTR_MODULE`]) that
/// nothing ambient consults: no `move_auto` rung bundle, no `simp` default
/// set, no `move_effect` list names it, so a proof reaches these facts only by
/// spelling the set (`move_auto ... only [move_wide_val]`, `simp
/// [move_wide_val]`).
///
/// This is the delivery for the class the fresh-tail census measured as an
/// ABSOLUTE blocker: 0 of 404 closed leaves cite an above-gate literal and
/// all 45 leaves that do are still exhausted, because the registered
/// conversion faces decode `(convert lit).val` ambiently while the literal's
/// own `_val` fact is gated out, leaving the rung facing an opaque alias.
/// Scoping is what makes that citable without re-opening the OOM the gate
/// exists to prevent -- ambient is the failure mode, not the fact itself.
const WIDE_ALIAS_VAL_ATTR: &str = "@[move_wide_val]";

/// Whether the `_val` fact for a literal of this decimal value is registered
/// (i.e. carries `@[move_effect]` and is therefore ambient in every
/// `move_auto` rung). Both sides are canonical decimal with no leading zeros,
/// so length-then-lexicographic IS numeric order and no bignum parse is
/// needed.
fn alias_val_fact_is_registered(decimal: &str) -> bool {
    decimal.len() < MOVE_EFFECT_VALUE_CEILING.len()
        || (decimal.len() == MOVE_EFFECT_VALUE_CEILING.len() && decimal < MOVE_EFFECT_VALUE_CEILING)
}

/// Does this module need [`MOVE_AUTO_ATTR_MODULE`]? Every alias `_val` fact
/// now carries an attribute from that module -- `@[move_effect]` below the
/// value gate, `@[move_wide_val]` above it -- so the answer is "does the
/// module declare any alias at all". It used to be "any REGISTERED alias",
/// which was correct while above-gate facts carried no attribute; leaving it
/// that way would emit `@[move_wide_val]` into a module that never imported
/// its declaration, and `register_simp_attr` syntax is usable only downstream
/// of the registration.
fn module_registers_alias_val_facts(
    aliases: &std::collections::BTreeMap<String, (u32, String)>,
) -> bool {
    !aliases.is_empty()
}

/// Emit one wide-literal alias and its `.val` fact.
///
/// THE ALIAS STAYS `opaque`, AND ITS `_val` FACT STAYS `native_decide` -- both
/// deliberately, and both against a real attempt to change them.
///
/// The attempt: an `opaque` constant has no definitional content for the kernel,
/// so `<alias>.val = <literal>` can only ever be an `ofReduceBool` fact, which is
/// why the generated model is the fleet's LAST native_decide population.
/// `@[irreducible] def` + `unfold <alias>; rfl` fixes exactly that, and in
/// isolation it looks free: measured on a probe, `rfl` / `decide` / `simp` all
/// fail to see through EITHER shape at default transparency, and the resulting
/// `_val` depends on `BoundedNat_bound_zero_absurd` alone.
///
/// It is not free at corpus scale. A/B on a regenerated cetus tree, single
/// variable, everything else identical: with the `def` shape, three
/// reward-math modules (`CetusCLMMSpecs.Rewarder_Proofs`, `Proofs.Rewarder`,
/// `Proofs.PoolRewardsOperational`) are OOM-KILLED after 81-279 s where the
/// baseline builds them in 7.5-8.7 s; with `opaque` restored the same tree is
/// rc=0 / 422 oleans / 0 errors. The kernel can delta-reduce an irreducible
/// `def` even though the elaborator will not, so a proof term that was an ATOM
/// all the way down now carries a 39-digit literal into kernel defeq -- which
/// is the same class of blow-up the `move_effect` VALUE GATE above exists to
/// prevent, arriving by a different door. Making these facts kernel-checked
/// needs a route that does not de-opaque the alias.
fn emit_opaque_const_aliases<W: Write>(
    w: &mut LeanWriter<W>,
    aliases: &std::collections::BTreeMap<String, (u32, String)>,
) {
    for (alias, (bits, decimal)) in aliases {
        w.line(&format!(
            "opaque {} : BoundedNat (2^{}) := {}",
            alias, bits, decimal
        ));
        w.newline();
        if alias_val_fact_is_registered(decimal) {
            w.line(OPAQUE_CONST_ALIAS_VAL_ATTR);
        } else {
            w.line(WIDE_ALIAS_VAL_ATTR);
        }
        w.line(&format!(
            "theorem {}_val : {}.val = {} := by",
            alias, alias, decimal
        ));
        w.line("  native_decide");
        w.newline();
    }
}

fn module_opaque_const_aliases(
    program: &Program,
    mid: ModId,
) -> std::collections::BTreeMap<String, (u32, String)> {
    use crate::ir::visit::{walk_expr_default, Visitor};
    use crate::ir::Expr;

    struct C<'a> {
        out: &'a mut std::collections::BTreeMap<String, (u32, String)>,
    }

    impl Visitor for C<'_> {
        fn visit_expr(&mut self, e: &Expr) {
            if let Expr::Const(c) = e {
                self::expr::collect_opaque_uint_const_aliases(c, self.out);
            }
            walk_expr_default(self, e);
        }
    }

    let mut out = std::collections::BTreeMap::new();
    for f in program.functions.values().filter(|f| f.module == mid) {
        let mut c = C { out: &mut out };
        c.visit_block(&f.body);
    }
    out
}

/// Compute the import lines for a per-module emitted file. Each
/// translated module imports Prelude + any other module (native or
/// translated) referenced by its struct fields, function signatures,
/// or function bodies.
///
/// Cross-module dependencies are inferred by walking the module's
/// own structs and functions for `Type::Struct { struct_id }` and
/// `Expr::Call { fun }` references whose module_id differs from
/// `mid`.
fn collect_module_imports(
    context: &self::context::RenderContext<'_>,
    mid: ModId,
    own_pkg: &str,
    own_ns: &str,
    lemma_libs: &std::collections::BTreeSet<String>,
    companions: &self::lemma_companions::CompanionPlan,
) -> Vec<String> {
    let program = context.program;
    let own_pkg_is_lemma = lemma_libs.contains(own_pkg);
    let mut deps = ModuleDeps::default();

    // Modules this one CALLS into (real function-call edges). Deps that
    // are NOT call edges are type-only references -- they are imported as
    // the dep's `_Types` (not its full function module) to avoid spurious
    // function->function import cycles from ghost dynamic-field value-type
    // pins. See `collect_call_dep_modules`.
    let call_dep_modules = collect_call_dep_modules(program, mid);

    // Walk all structs in this module for field-type references to
    // other modules' structs.
    for (_, s) in program.structs.iter() {
        if s.module_id != mid {
            continue;
        }
        walk_fields_for_module_deps(s, program, mid, &mut deps);
    }

    // Walk all functions in this module: signature + body.
    for (_, f) in program.functions.iter() {
        if f.module != mid {
            continue;
        }
        walk_signature_for_module_deps(&f.signature, program, mid, &mut deps);
        walk_block_for_module_deps(&f.body, program, mid, &mut deps);
    }

    // A boundary root helper is emitted for every global owned by this
    // module. Its value parameter mentions the global's pointee type even
    // when no translated function signature does, so include those type
    // dependencies in the function-module import set.
    for global in program
        .globals
        .values()
        .filter(|global| global.module_id == mid)
    {
        walk_type_for_module_deps(&global.ty, program, mid, &mut deps);
    }

    // Renderer-owned declarations live in `program.natives.decls`, not
    // `program.functions`, so neither walk above sees their signatures.
    // Preserve any `AbortResult` type dependency they carry. This is
    // conservative for native declarations that are supplied by a sibling,
    // and cycle-safe because `Prover.Abort` is a near-leaf prelude file.
    for decl in program.natives.decls.values() {
        if decl.module == mid && type_references_abort_result(&decl.signature.return_type, program)
        {
            walk_type_for_module_deps(&decl.signature.return_type, program, mid, &mut deps);
        }
    }

    let mut imports: Vec<String> = Vec::new();
    // Always import Prelude.
    imports.push("Prelude.BoundedNat".to_string());
    imports.push("Prelude.Helpers".to_string());
    imports.push("Prelude.MoveAbort".to_string());
    imports.push("Prelude.Mutation".to_string());
    imports.push("Prelude.ProgramState".to_string());
    imports.push("Prelude.Quantifiers".to_string());
    imports.push("Prelude.TypeConversion".to_string());
    imports.push("Prelude.TypedMap".to_string());
    // Stage 4 emits `world : World` parameters / threaded calls in
    // any Impure user function. Both lemma packages (which get a
    // file-scoped polymorphic `World` notation) and user packages
    // (which see the concrete `Prover.World.World AnyEvent AnyObject`
    // via `Generated/World.lean`) need the prelude structure import.
    // (The Lean module is `Prelude.World`; the namespace inside it
    // is `Prover.World`. The renderer also writes a stubbed
    // `Prover/World.lean` for the `Prover::world` native module
    // forwarder, which is unrelated.)
    imports.push("Prelude.World".to_string());

    // Wide-literal aliases carry `@[move_effect]` on their `.val` fact, and
    // `move_effect`'s syntax exists only after importing the module that
    // `register_simp_attr`s it. Conditional on the module actually REGISTERING
    // one, so a module with no wide literals -- or only literals above the
    // value ceiling -- keeps a byte-identical import list.
    if module_registers_alias_val_facts(&module_opaque_const_aliases(program, mid)) {
        imports.push(MOVE_AUTO_ATTR_MODULE.to_string());
    }

    // For each dep module, emit `import <pkg>.<ns>`. Skip self.
    for dep_mid in &deps.modules {
        if *dep_mid == mid {
            continue;
        }
        if let Some(dep_module) = program.modules.get(dep_mid) {
            let dep_pkg = if dep_module.package_name.is_empty() {
                "NewPipeline".to_string()
            } else {
                dep_module.package_name.clone()
            };
            let dep_ns = self::escape::module_name_to_namespace(&dep_module.name);
            if dep_pkg == own_pkg && dep_ns == own_ns {
                continue;
            }
            // Defensive cycle-break: a lemma package's emitted .lean
            // file must never `import` a non-lemma (user) package.
            // Lemma packages are the shared framework
            // (Sui, MoveStdlib, Prover, Pyth, ...); they are project-
            // independent by construction. If the dep walker
            // surfaces a user-package reference for a function
            // attributed to a lemma module, treating it as an
            // import creates a circular dependency
            // (lemma -> user -> lemma). The generic instantiation
            // that triggers such a reference is already rendered at
            // the call site inside the user-package file, so
            // dropping the import here does NOT lose any
            // type-resolution -- the call site has the concrete
            // type in scope via its own imports. Emit a stderr
            // warning so the upstream walker bug stays visible
            // without breaking the lake build.
            let dep_pkg_is_lemma = lemma_libs.contains(&dep_pkg);
            if own_pkg_is_lemma && !dep_pkg_is_lemma && dep_pkg != "NewPipeline" {
                eprintln!(
                    "warning: collect_module_imports: dropped leaked import `{}.{}` from lemma module `{}.{}` (would create lemma->user cycle)",
                    dep_pkg, dep_ns, own_pkg, own_ns,
                );
                continue;
            }
            // A dep reached ONLY via type references (struct fields,
            // signatures, type args) -- never via a function call --
            // needs only the dep's `_Types`, not its full function
            // module. Importing the full module re-introduces the
            // ghost-field cross-module cycle (e.g. `Market` references
            // `Apm` purely because its ghost dynamic-field holds an
            // `Apm` type, while `apm` genuinely CALLS `market` -- a
            // function->function cycle that is not a real Move call
            // cycle). Real call edges keep the full module import
            // (the Move call graph is a DAG, so they never cycle).
            // Lemma packages have no `_Types` split -- always import
            // the module path (the per-module stub forwards to the
            // `<X>Natives.lean` sibling).
            if dep_pkg_is_lemma || call_dep_modules.contains(dep_mid) {
                let dep_path = format!("{}.{}", dep_pkg, dep_ns);
                // Generator-conditional lemma imports: a module that
                // imports a subject also imports the subject's proof-lemma
                // companion, when the program still declares everything the
                // companion names. The companion imports the subject and
                // nothing below the subject imports the companion, so this
                // cannot close a cycle. See `render/lemma_companions.rs`.
                for companion in companions.companions_for(&dep_path) {
                    imports.push(companion.clone());
                }
                imports.push(dep_path);
            } else {
                imports.push(format!("{}.{}_Types", dep_pkg, dep_ns));
            }
        }
    }
    // Name-keyed datatype tags (`StructIdx.<Pkg>__<mod>__<Name>`).
    // Every package emits borrow paths, lemma packages included
    // (`Sui.Coin`, `MoveStdlib.MoveOption`), so this one is
    // unconditional. `Generated/StructIdx.lean` has no imports of its
    // own, so it cannot participate in a cycle.
    imports.push("Generated.StructIdx".to_string());
    // Bring the per-package `Mutation` / `Edge` / `AnyKey`
    // abbreviations into scope so `Type::MutableRef` renderings can
    // refer to them unqualified.
    //
    // Skip when own_pkg is a native lemma package (Prover, Sui,
    // MoveStdlib, ...): those packages don't get a `Generated/AnyKey.lean`
    // written (the per-package AnyKey is for user packages only),
    // and importing a non-existent file triggers the missing-import
    // stubber which writes a circular `import NewPipeline.Code` stub.
    if !own_pkg_is_lemma {
        // Shared root-level `Generated` lean_lib (see
        // `render_program_to_dir`): one global `AnyKey` /
        // `AnyEvent` / `AnyObject` / `World` shared across user
        // packages. Importing `Generated.*` (no package prefix)
        // resolves against the root-level library so cross-package
        // imports don't trigger duplicate `AnyKey.ctorIdx`
        // declarations.
        imports.push("Generated.AnyKey".to_string());
        imports.push("Generated.World".to_string());
        // `Generated.TyCodeInterp` carries the `Universe TyCode`
        // instance and per-type `HasCode TyCode T` instances. Every
        // non-lemma (user) `.lean` file imports it unconditionally:
        // (a) functions get `[HasCode _root_.TyCode T]` constraints
        //     per type param (Phase 3d), needing the typeclass +
        //     instances in scope, and
        // (b) Bag.add / borrow / etc. call sites synthesize
        //     `[Universe TyCode]` from the imported instance.
        // No cycle: `_Types` files don't import `TyCodeInterp`; only
        // `.lean` (funcs) files do. The Types-file DAG keeps the
        // import graph acyclic.
        imports.push("Generated.TyCodeInterp".to_string());
        // `Generated.ObjTypeInterp` carries the `Universe ObjType`
        // instance plus `HasCode ObjType T` and `HasObjectId T`
        // instances for project + framework object types. User
        // call sites of typed `transfer::*` / `test_scenario::take_*`
        // resolve their `[HasCode ObjType T] [HasObjectId T]`
        // constraints against these instances. No cycle: only `.lean`
        // (funcs) files import it -- never `_Types` files.
        imports.push("Generated.ObjTypeInterp".to_string());
    } else {
        // Lemma packages (Sui, Prover, MoveStdlib, ...) carry
        // ObjType constraints on type params that flow into
        // `transfer::*` / `test_scenario::take_*` (Phase 6 Step 1
        // propagation).
        //
        // For most lemma modules, importing the bare
        // `Generated.ObjType` inductive is enough -- the module's
        // functions either don't carry ObjType constraints (no
        // taint), or carry them in a position where Lean only needs
        // the type name to be in scope (e.g. signature display).
        //
        // Lemma modules that carry ObjType-tainted functions (transfer /
        // test_scenario wrappers) are kept universe-POLYMORPHIC: each tainted
        // type param takes an abstract `{__ObjU} [Universe __ObjU] [HasCode
        // __ObjU T]` (see render::function), and the typed native infers
        // `__ObjU` from the world arg. This needs only the `Universe`/`HasCode`
        // CLASSES (Prelude.Universe), never the per-project `Universe ObjType`
        // / `HasCode ObjType T` INSTANCES (Generated.ObjTypeInterp). Importing
        // ObjTypeInterp here closes a build cycle -- it pulls in framework
        // modules (`Sui.Coin`/`Sui.Package` -> `Sui.Transfer`) that import
        // `Generated.ObjTypeInterp` back. The concrete `__ObjU := _root_.ObjType`
        // resolution (instances from ObjTypeInterp) happens at the USER call
        // site, which imports it. Same pattern as the TyCode/BagU universes.
        let module_has_obj_taint = program.functions.iter().any(|(fid, f)| {
            f.module == mid
                && (0..f.signature.type_params.len())
                    .any(|i| context.obj_typeparam_needs_constraint(*fid, i))
        });
        imports.push("Generated.ObjType".to_string());
        if module_has_obj_taint {
            imports.push("Prelude.Universe".to_string());
        }
        // Lemma modules whose functions call a `type_name::*` native
        // with one of their own type params (e.g. the translated
        // `sui::package::claim`) are kept universe-POLYMORPHIC: the
        // function takes an abstract `{U} [Universe U] [Repr U]` plus
        // `[HasCode U T]` (see render::function), and the type_name
        // call infers `U` from that constraint rather than pinning
        // `TyCode`. This needs only the `Universe`/`HasCode`/`Repr`
        // CLASSES (Prelude.Universe), never the per-project `TyCode`
        // INSTANCES (Generated.TyCodeInterp) -- so we must NOT import
        // TyCodeInterp here: TyCodeInterp imports these very lemma
        // modules (their structs are TyCode leaves, e.g.
        // `sui::package::Publisher`), so importing it back would form
        // a cycle. The concrete `U := TyCode` resolution happens at
        // the USER call site, which does import TyCodeInterp.
        let module_has_tycode_taint = program.functions.iter().any(|(fid, f)| {
            f.module == mid
                && (0..f.signature.type_params.len())
                    .any(|i| context.tycode_typeparam_needs_constraint(*fid, i))
        });
        if module_has_tycode_taint {
            // Class-level scope only; instances resolve at call sites.
            imports.push("Prelude.Universe".to_string());
        }

        // A lemma module also needs the concrete `Universe BagU`
        // INSTANCE (not just the class) when one of its own structs has
        // a `Bag` / `ObjectBag` field: that field renders as
        // `Bag.Bag _root_.BagU`, and `Bag.Bag (U) [Universe U]` forces
        // Lean to synthesize `[Universe BagU]` at the field type. The
        // `module_has_tycode_taint` check above is signature-only and so
        // misses struct fields -- detect Bag-containing structs directly.
        // `Generated.BagUInterp` (always emitted) carries the instance.
        // Cycle-free for these modules: `BagUInterp` imports the BagU
        // universe LEAVES (bag VALUE types, e.g. `sui::coin::Coin`),
        // never Bag CONTAINER modules. (A module that were simultaneously
        // a bag-value-leaf AND a Bag container would cycle; no framework
        // module currently is.) See
        // `plans/lean-pipeline/split-bag-df-universes.md`.
        if self::dyn_type_universe::module_has_bag_struct(program, mid) {
            imports.push("Generated.BagUInterp".to_string());
        }
    }
    for leaf in &deps.leaf_imports {
        imports.push(leaf.clone());
    }
    imports.sort();
    imports.dedup();
    imports
}

/// Compute the import lines for a user-package `<Mod>_Types.lean`
/// file. Smaller surface than `collect_module_imports`:
///   * Walks only the module's struct field types -- no function
///     signatures, no function bodies.
///   * For non-lemma cross-package deps, emits `<Pkg>.<Mod>_Types`
///     (NOT `<Pkg>.<Mod>`) so the import graph stays a DAG: no
///     _Types file ever imports a `.lean` (functions) file.
///   * Skips `Generated.TyCode` -- TyCode imports user `_Types`
///     files, so adding it here would re-introduce the cycle.
///   * Skips natives-sibling imports -- those bring function
///     implementations, not struct definitions.
///
/// Sees: Prelude + `Generated.AnyKey` + `Generated.World` +
/// cross-module struct deps (as `_Types`).
/// True when at least one function in `mid` has a type param that flows
/// into transfer / take_* (the "ObjType taint" that pins the file-scoped
/// `World` notation's Object slot). Obj-tainted lemma modules import
/// `Generated.ObjTypeInterp`, which makes their single `Full` file impure.
fn module_has_obj_taint(context: &self::context::RenderContext<'_>, mid: ModId) -> bool {
    let program = context.program;
    program.functions.iter().any(|(fid, f)| {
        f.module == mid
            && (0..f.signature.type_params.len())
                .any(|i| context.obj_typeparam_needs_constraint(*fid, i))
    })
}

/// True when a lemma/framework module is emitted with a pure
/// `<Mod>_Types.lean` leaf (struct defs only). Happens for obj-tainted
/// lemma modules that also declare a non-native struct (e.g.
/// `Sui::test_scenario`): their `Full` file imports
/// `Generated.ObjTypeInterp`, so the universe interpreters must import
/// the pure leaf to name the struct without forming an import cycle.
fn lemma_module_has_types_leaf(
    context: &self::context::RenderContext<'_>,
    pkg: &str,
    ns: &str,
) -> bool {
    let program = context.program;
    program.modules.iter().any(|(mid, m)| {
        let m_pkg = if m.package_name.is_empty() {
            "NewPipeline"
        } else {
            m.package_name.as_str()
        };
        if m_pkg != pkg {
            return false;
        }
        if self::escape::module_name_to_namespace(&m.name) != ns {
            return false;
        }
        module_has_obj_taint(context, *mid)
            && program
                .structs
                .iter()
                .any(|(_, s)| s.module_id == *mid && !s.is_native)
    })
}

/// True when a lemma/framework module is a "bag-cycle" module: it declares
/// BOTH a Bag-CONTAINING struct (so its file imports `Generated.BagUInterp`)
/// AND a Bag-FREE non-native struct that can be a bag VALUE (so `BagUInterp`
/// imports it back) -- e.g. Sui `coin_registry` (`CurrencyInitializer` holds a
/// `Bag`; `Currency` is a bag value). Without intervention this is a direct
/// `BagUInterp <-> <Mod>` import cycle. Rendering it with the user-package
/// Bag-split (Bag-free `_Types_Skeleton` / Bag-containing `_Types` / Funcs)
/// lets `BagUInterp` import only the Bag-free skeleton (a sink), breaking the
/// cycle. Obj-tainted modules are excluded -- they use the obj-taint `_Types`
/// leaf instead.
pub(crate) fn lemma_module_bag_split(
    context: &self::context::RenderContext<'_>,
    mid: ModId,
) -> bool {
    let program = context.program;
    if module_has_obj_taint(context, mid) {
        return false;
    }
    let bag_ids = context.bag_containing_structs();
    let mut has_bag_containing = false;
    let mut has_bag_free_nonnative = false;
    for (sid, s) in program.structs.iter() {
        if s.module_id != mid || s.is_native {
            continue;
        }
        if bag_ids.contains(sid) {
            has_bag_containing = true;
        } else {
            has_bag_free_nonnative = true;
        }
    }
    has_bag_containing && has_bag_free_nonnative
}

fn collect_types_module_imports(
    context: &self::context::RenderContext<'_>,
    mid: ModId,
    own_pkg: &str,
    own_ns: &str,
    lemma_libs: &std::collections::BTreeSet<String>,
    for_skeleton: bool,
) -> Vec<String> {
    let program = context.program;
    let mut deps = ModuleDeps::default();
    for (_, s) in program.structs.iter() {
        if s.module_id != mid {
            continue;
        }
        walk_fields_for_module_deps(s, program, mid, &mut deps);
    }

    let mut imports: Vec<String> = Vec::new();
    imports.push("Prelude.BoundedNat".to_string());
    imports.push("Prelude.Helpers".to_string());
    imports.push("Prelude.MoveAbort".to_string());
    imports.push("Prelude.Mutation".to_string());
    imports.push("Prelude.ProgramState".to_string());
    imports.push("Prelude.Quantifiers".to_string());
    imports.push("Prelude.TypeConversion".to_string());
    imports.push("Prelude.TypedMap".to_string());
    imports.push("Prelude.World".to_string());

    // Detect whether our own module is split (i.e. has Bag-containing
    // structs). When OUR module is non-split, importing the full
    // `<dep>.<Mod>_Types` of a split dep pulls `Generated.BagUInterp`
    // into our import closure -- and `BagUInterp` may import OUR
    // module's `_Types` (since `_Types` is the only file for non-split
    // modules), forming a `Mod_Types -> dep_Types -> BagUInterp -> Mod_Types`
    // cycle. Prefer the dep's `_Types_Skeleton` (Bag-free structs
    // only) when available; the cross-module struct references in our
    // module typically target the Bag-free portion (e.g. cetus_clmm's
    // `Pool` -> `Rewarder.RewarderManager`, where `RewarderManager`
    // is in the skeleton). If our use actually requires a Bag-containing
    // struct from the dep, Lean will surface a missing-identifier
    // error and we can refine the heuristic.
    let own_has_bag = self::dyn_type_universe::module_has_bag_struct(program, mid);
    for dep_mid in &deps.modules {
        if *dep_mid == mid {
            continue;
        }
        if let Some(dep_module) = program.modules.get(dep_mid) {
            let dep_pkg = if dep_module.package_name.is_empty() {
                "NewPipeline".to_string()
            } else {
                dep_module.package_name.clone()
            };
            let dep_ns = self::escape::module_name_to_namespace(&dep_module.name);
            if dep_pkg == own_pkg && dep_ns == own_ns {
                continue;
            }
            let dep_pkg_is_lemma = lemma_libs.contains(&dep_pkg);
            if dep_pkg_is_lemma {
                if lemma_module_has_types_leaf(context, &dep_pkg, &dep_ns) {
                    imports.push(format!("{}.{}_Types", dep_pkg, dep_ns));
                } else {
                    imports.push(format!("{}.{}", dep_pkg, dep_ns));
                }
            } else {
                // Skeleton-preference cycle break. Import the dep's
                // `_Types_Skeleton` (Bag-free, no `BagUInterp` dep)
                // instead of its full `_Types` when EITHER:
                //   * we are emitting a `_Types_Skeleton` file
                //     (`for_skeleton`) -- a skeleton must never pull in
                //     `BagUInterp`, or it forms a
                //     `BagUInterp -> dep_Types -> our_Skeleton ->
                //      BagUInterp` cycle (BagUInterp imports our
                //     skeleton); or
                //   * our own module is non-split (`!own_has_bag`), where
                //     importing a split dep's full `_Types` would pull
                //     `BagUInterp` into our single `_Types` file.
                // Bag-containment is transitive, so a Bag-free struct
                // (the only kind in a skeleton / the source of these
                // refs) only references Bag-free dep structs, which live
                // in the dep's skeleton -- the skeleton import always
                // resolves.
                let dep_has_bag = self::dyn_type_universe::module_has_bag_struct(program, *dep_mid);
                if dep_has_bag && (for_skeleton || !own_has_bag) {
                    imports.push(format!("{}.{}_Types_Skeleton", dep_pkg, dep_ns));
                } else {
                    imports.push(format!("{}.{}_Types", dep_pkg, dep_ns));
                }
            }
        }
    }

    // User-package `_Types` files contain ONLY struct definitions
    // (ModuleKind::Types). Move references (`&T` / `&mut T`) are not
    // storable, so a struct field can never be a mutable reference --
    // therefore a `_Types` file never references the `Mutation` / `Edge`
    // abbreviations or `AnyKey`. We deliberately do NOT import
    // `Generated.AnyKey` here. That import was previously blanket-added
    // to every user `_Types` file but is universally dead (verified: 0
    // usages across the corpus), and it forms a back-edge
    // `user._Types -> Generated.AnyKey` that becomes an import CYCLE the
    // moment `AnyKey` carries a USER-struct key payload (`AnyKey` must
    // then `import <Pkg>.<Mod>_Types` back). Funcs (`.lean`) files still
    // import `Generated.AnyKey` directly (see `collect_module_imports`).
    let own_pkg_is_lemma = lemma_libs.contains(own_pkg);
    if !own_pkg_is_lemma {
        // `Generated.World` is intentionally NOT imported here even
        // though the renderer emits a `local notation:max "World" =>
        // Prover.World.World __WorldEvent __WorldObject __WorldBagEntry` block at the
        // top of each _Types file. The notation closes over generic
        // `Prelude.World` variables (`__WorldEvent`, `__WorldObject`),
        // not over the per-project `Generated.World` abbreviation.
        // Importing `Generated.World` would (now that it carries the
        // typed bag-storage parameter via TyCodeInterp) create a
        // cycle: _Types -> Generated.World -> TyCodeInterp -> _Types.
    }

    // If any struct field references a heterogeneous-storage native
    // (Bag / ObjectBag / dynamic_field / dynamic_object_field), the
    // rendered type carries a `_root_.TyCode` arg. Import the BARE
    // inductive so `_root_.TyCode` resolves. The Universe instance
    // is NOT needed here -- the prelude's Bag (U : Type) has no
    // class constraint at the struct level.
    let needs_tycode = deps.modules.iter().any(|dep_mid| {
        program.modules.get(dep_mid).map_or(false, |m| {
            m.package_name == "Sui"
                && matches!(
                    m.name.as_str(),
                    "bag" | "object_bag" | "dynamic_field" | "dynamic_object_field"
                )
        })
    });
    if needs_tycode {
        imports.push("Generated.TyCode".to_string());
    }

    for leaf in &deps.leaf_imports {
        imports.push(leaf.clone());
    }

    imports.sort();
    imports.dedup();
    imports
}

/// Hand-written native structs that live in a dedicated *leaf* file
/// (separate from their module's main natives sibling) to break an
/// import cycle. `random::RandomInner` lives in
/// `Sui/RandomInnerNatives.lean` (Prelude-only imports) so the
/// generated `versioned::Versioned` -- whose ghost dynamic-field type
/// references `RandomInner` -- can import just the leaf instead of the
/// whole `random` module (which imports `Versioned` for `Random.inner`,
/// otherwise closing a `Versioned -> Random -> Versioned` cycle).
/// Returns the Lean module path to import for such a struct, or None
/// for the default (parent module).
fn native_struct_leaf_module(program: &Program, sid: &StructId) -> Option<String> {
    let s = program.structs.get(sid)?;
    let m = program.modules.get(&s.module_id)?;
    let pkg = if m.package_name.is_empty() {
        "NewPipeline"
    } else {
        m.package_name.as_str()
    };
    match (pkg, m.name.as_str(), s.name.as_str()) {
        ("Sui", "random", "RandomInner") => Some("Sui.RandomInnerNatives".to_string()),
        _ => None,
    }
}

/// Accumulator for module-dependency walks. `modules` holds referenced
/// Move modules (imported as `<pkg>.<ns>` / `_Types`); `leaf_imports`
/// holds fully-qualified Lean module paths for native structs that live
/// in a dedicated leaf file (see `native_struct_leaf_module`).
#[derive(Default)]
struct ModuleDeps {
    modules: std::collections::BTreeSet<ModId>,
    leaf_imports: std::collections::BTreeSet<String>,
}

/// Record a cross-module struct reference into `deps`, routing structs
/// that live in a dedicated leaf file to `leaf_imports` instead of the
/// parent module.
fn record_struct_dep(
    program: &Program,
    struct_id: &StructId,
    own_mid: ModId,
    deps: &mut ModuleDeps,
) {
    if let Some(s) = program.structs.get(struct_id) {
        if s.module_id != own_mid {
            if let Some(leaf) = native_struct_leaf_module(program, struct_id) {
                deps.leaf_imports.insert(leaf);
            } else {
                deps.modules.insert(s.module_id);
            }
        }
    }
}

fn walk_fields_for_module_deps(
    s: &crate::ir::Struct,
    program: &Program,
    own_mid: ModId,
    deps: &mut ModuleDeps,
) {
    for f in &s.fields {
        walk_type_for_module_deps(&f.field_type, program, own_mid, deps);
    }
    if let Some(variants) = &s.variants {
        for v in variants {
            for f in &v.fields {
                walk_type_for_module_deps(&f.field_type, program, own_mid, deps);
            }
        }
    }
}

fn walk_signature_for_module_deps(
    sig: &crate::ir::Signature,
    program: &Program,
    own_mid: ModId,
    deps: &mut ModuleDeps,
) {
    for p in &sig.params {
        walk_type_for_module_deps(&p.ty, program, own_mid, deps);
    }
    walk_type_for_module_deps(&sig.return_type, program, own_mid, deps);
}

/// True iff `ty` (or one of its type arguments) references the synthetic
/// `Prover::abort::AbortResult` struct that stage 7's `.aborts` pass
/// materialises (`retype_abort_code_native_companions`). Used to drive
/// the `Prover.Abort` import for renderer-owned declarations, whose
/// signatures are absent from the regular function walks.
fn type_references_abort_result(ty: &crate::ir::Type, program: &Program) -> bool {
    use crate::ir::Type::*;
    match ty {
        Struct {
            struct_id,
            type_args,
        } => {
            program.structs.get(struct_id).map_or(false, |s| {
                s.qualified_name == crate::stage_07_dejumps::option_aborts::OPTION_QUALIFIED_NAME
            }) || type_args
                .iter()
                .any(|t| type_references_abort_result(t, program))
        }
        Vector(inner) | Reference(inner) => type_references_abort_result(inner, program),
        MutableRef { inner, root } => {
            type_references_abort_result(inner, program)
                || type_references_abort_result(root, program)
        }
        Tuple(ts) => ts.iter().any(|t| type_references_abort_result(t, program)),
        Unit | Bool | Prop | UInt(_) | Address | TypeParam(_) => false,
    }
}

fn walk_type_for_module_deps(
    ty: &crate::ir::Type,
    program: &Program,
    own_mid: ModId,
    deps: &mut ModuleDeps,
) {
    use crate::ir::Type::*;
    match ty {
        Struct {
            struct_id,
            type_args,
        } => {
            record_struct_dep(program, struct_id, own_mid, deps);
            for t in type_args {
                walk_type_for_module_deps(t, program, own_mid, deps);
            }
        }
        Vector(inner) | Reference(inner) => {
            walk_type_for_module_deps(inner, program, own_mid, deps)
        }
        MutableRef { inner, root } => {
            walk_type_for_module_deps(inner, program, own_mid, deps);
            walk_type_for_module_deps(root, program, own_mid, deps);
        }
        Tuple(ts) => {
            for t in ts {
                walk_type_for_module_deps(t, program, own_mid, deps);
            }
        }
        Unit | Bool | Prop | UInt(_) | Address | TypeParam(_) => {}
    }
}

fn walk_block_for_module_deps(
    b: &crate::ir::Block,
    program: &Program,
    own_mid: ModId,
    deps: &mut ModuleDeps,
) {
    use crate::ir::visit::{walk_expr_default, Visitor};
    use crate::ir::Expr;
    struct C<'a> {
        program: &'a Program,
        own_mid: ModId,
        deps: &'a mut ModuleDeps,
    }
    impl Visitor for C<'_> {
        fn visit_expr(&mut self, e: &Expr) {
            match e {
                Expr::Call { fun, type_args, .. } => {
                    // Use `lookup_callee` so native callees (in
                    // `program.natives.decls`) register their module in
                    // `deps` too. The old `program.functions.get(fun)`
                    // lookup only saw translated functions, so calls to
                    // natives (Event.emit, Ghost.global,
                    // Vector_iter.slice, Transfer.*_impl, Object.*_impl,
                    // ...) silently dropped their import -- the rendered
                    // file then referenced an identifier whose Lean
                    // module wasn't imported and lake build failed with
                    // `Unknown identifier`.
                    if let Some(callee) = self.program.lookup_callee(*fun) {
                        let m = callee.module();
                        if m != self.own_mid {
                            self.deps.modules.insert(m);
                        }
                    }
                    for t in type_args {
                        walk_type_for_module_deps(t, self.program, self.own_mid, self.deps);
                    }
                }
                Expr::Match { struct_id, .. } => {
                    record_struct_dep(self.program, struct_id, self.own_mid, self.deps)
                }
                _ => {}
            }
            walk_expr_default(self, e);
        }
    }
    C {
        program,
        own_mid,
        deps,
    }
    .visit_block(b);
}

/// Collect the set of OTHER modules whose FUNCTIONS are called by any
/// function in module `mid` (real call edges). Mirrors
/// `walk_*_for_module_deps` but records only `Expr::Call` callee
/// modules -- NOT type references. `collect_module_imports` uses this to
/// decide whether a dep needs the full function module (a call edge) or
/// only its `_Types` (a type-only edge). Routing type-only deps to
/// `_Types` breaks spurious function->function import cycles created when
/// the ghost dynamic-field augmentation pins a cross-module value type
/// into a struct (e.g. `Market`'s ghost `TypedMap _ Apm.MinPriceHistory`
/// field makes `Market` reference `Apm` purely as a type, while `apm`
/// genuinely calls `market` -- a cycle that is NOT a real Move call
/// cycle, which is always a DAG).
fn collect_call_dep_modules(program: &Program, mid: ModId) -> std::collections::BTreeSet<ModId> {
    let mut out: std::collections::BTreeSet<ModId> = std::collections::BTreeSet::new();
    for (_, f) in program.functions.iter() {
        if f.module != mid {
            continue;
        }
        walk_block_for_call_modules(&f.body, program, mid, &mut out);
    }
    out
}

fn walk_block_for_call_modules(
    b: &crate::ir::Block,
    program: &Program,
    own_mid: ModId,
    out: &mut std::collections::BTreeSet<ModId>,
) {
    use crate::ir::visit::{walk_expr_default, Visitor};
    use crate::ir::Expr;
    struct C<'a> {
        program: &'a Program,
        own_mid: ModId,
        out: &'a mut std::collections::BTreeSet<ModId>,
    }
    impl Visitor for C<'_> {
        fn visit_expr(&mut self, e: &Expr) {
            if let Expr::Call { fun, .. } = e {
                if let Some(callee) = self.program.lookup_callee(*fun) {
                    let cm = callee.module();
                    if cm != self.own_mid {
                        self.out.insert(cm);
                    }
                }
            }
            walk_expr_default(self, e);
        }
    }
    C {
        program,
        own_mid,
        out,
    }
    .visit_block(b);
}

/// Sort functions in callee-first order within their module. A
/// function `f` whose body calls another function `g` in the same
/// module must be emitted after `g` so the Lean parser sees `g`'s
/// definition first. Spec companions (`.aborts`, `.requires`,
/// `.ensures`) similarly call back to their target -- they must be
/// emitted after the target.
///
/// Cross-module calls don't matter (imports handle them). Cycles
/// (mutual recursion) currently fall back to original-order
/// emission with a comment; full SCC merging into `mutual ... end`
/// blocks is a future improvement.
fn topo_sort_functions<'a>(
    items: &mut Vec<(&'a FunId, &'a crate::ir::Function)>,
    program: &Program,
) {
    use std::collections::BTreeMap;

    let in_module: std::collections::BTreeSet<FunId> = items.iter().map(|(id, _)| **id).collect();

    let mut deps: BTreeMap<FunId, Vec<FunId>> = BTreeMap::new();
    let mut id_to_item: BTreeMap<FunId, &'a crate::ir::Function> = BTreeMap::new();
    for (id, f) in items.iter() {
        let mut my_deps: std::collections::BTreeSet<FunId> = Default::default();
        function_call_deps(f, &in_module, **id, &mut my_deps);
        // Spec companions depend on their target (they call `target`
        // by FunId in `.aborts` composition).
        if let crate::ir::FunctionKind::Spec { target, .. } = f.kind {
            if in_module.contains(&target) && target != **id {
                my_deps.insert(target);
            }
        }
        deps.insert(**id, my_deps.into_iter().collect());
        id_to_item.insert(**id, *f);
    }

    let mut indeg: BTreeMap<FunId, usize> = BTreeMap::new();
    for &id in id_to_item.keys() {
        indeg.entry(id).or_insert(0);
    }
    let mut reverse: BTreeMap<FunId, Vec<FunId>> = BTreeMap::new();
    for (&src, ds) in &deps {
        for &dst in ds {
            *indeg.entry(src).or_insert(0) += 1;
            reverse.entry(dst).or_default().push(src);
        }
    }
    let mut ready: Vec<FunId> = indeg
        .iter()
        .filter(|(_, &d)| d == 0)
        .map(|(&id, _)| id)
        .collect();
    ready.sort();
    let mut out: Vec<FunId> = Vec::new();
    while let Some(id) = ready.pop() {
        out.push(id);
        if let Some(downstream) = reverse.get(&id).cloned() {
            for d in downstream {
                let v = indeg.get_mut(&d).expect("indeg present");
                *v -= 1;
                if *v == 0 {
                    ready.push(d);
                }
            }
            ready.sort();
        }
    }
    if out.len() < items.len() {
        for (id, _) in items.iter() {
            if !out.contains(id) {
                out.push(**id);
            }
        }
    }

    // Build a `FunId -> &(&FunId, &Function)` lookup once, then
    // index into it. The previous O(N^2) inner loop made ember-class
    // packages (thousands of functions per module) hang.
    let mut id_index: BTreeMap<FunId, (&'a FunId, &'a crate::ir::Function)> = BTreeMap::new();
    for (id_ref, f_ref) in items.iter() {
        id_index.insert(**id_ref, (*id_ref, *f_ref));
    }
    let mut new_items: Vec<(&'a FunId, &'a crate::ir::Function)> = Vec::with_capacity(items.len());
    for id in &out {
        if let Some(entry) = id_index.get(id) {
            new_items.push(*entry);
        }
    }
    *items = new_items;
}

/// Emit a list of SCCs to the writer, wrapping non-trivial SCCs
/// (cycles, or single nodes with self-edges) in `mutual ... end`
/// blocks so Lean can elaborate them together. Trivial SCCs (single
/// non-recursive node) get plain `def` emission via `render_function`.
///
/// Pre-condition: SCCs are in callees-first topological order
/// (Tarjan's output from [`compute_function_sccs`]).
fn emit_function_sccs<'a, W: Write>(
    sccs: &[Vec<(&'a FunId, &'a crate::ir::Function)>],
    context: &self::context::RenderContext<'_>,
    namespace: &str,
    w: &mut LeanWriter<W>,
) -> RenderResult<()> {
    let program = context.program;
    for scc in sccs {
        if scc.is_empty() {
            continue;
        }
        if scc_needs_mutual_block(scc, program) {
            // Mutual block: Lean rejects mixing emission strategies within
            // one block, so every member uses the same one.
            //
            // If the whole SCC is a tangle of generated loop helpers /
            // abort companions of loops (`scc_is_fixpoint_eligible`), emit
            // every member as `def … partial_fixpoint` -- they are all
            // first-order and provably monotone (mutual `partial_fixpoint`
            // is supported, and the abort members get their match scrutinee
            // inlined like the single-loop case). This makes the loop
            // PROVABLE instead of opaque.
            //
            // Otherwise (the SCC contains a source-level recursive function
            // or an abort companion mirroring source recursion -- which can
            // pass a recursive call into a higher-order combinator and
            // defeat `partial_fixpoint`'s monotonicity derivation) fall back
            // to opaque `partial def` across the whole block.
            let execution_only =
                context.loop_termination.mode() == self::loop_termination::LoopMode::Execution;
            let fixpoint = !execution_only && scc_is_fixpoint_eligible(scc, program);
            let fixpoint_world_bottom = if fixpoint {
                scc_read_only_world_bottom_param(scc, program)
            } else {
                None
            };
            let scc_partial =
                execution_only || (!fixpoint && scc_contains_partial_member(scc, program));
            w.line("mutual");
            for (fid, f) in scc {
                render_function(
                    f,
                    **fid,
                    context,
                    Some(namespace),
                    w,
                    scc_partial,
                    false,
                    fixpoint,
                    fixpoint_world_bottom.as_ref(),
                )?;
            }
            w.line("end");
            w.newline();
        } else {
            for (fid, f) in scc {
                let fixpoint_world_bottom = scc_read_only_world_bottom_param(scc, program);
                render_function(
                    f,
                    **fid,
                    context,
                    Some(namespace),
                    w,
                    false,
                    false,
                    false,
                    fixpoint_world_bottom.as_ref(),
                )?;
                // Trusted obligation (stage 12): follow the Prop def with
                // its assumed `axiom NAME_holds (params) : <ns>.NAME args`
                // in the SAME module file. The proof-stub rendering path
                // handles the signature; `is_axiom` inside swaps the
                // keyword/name and drops the `:= by sorry`.
                if matches!(f.kind, crate::ir::FunctionKind::Axiom { .. }) {
                    render_function(
                        f,
                        **fid,
                        context,
                        Some(namespace),
                        w,
                        false,
                        /*as_proof_stub=*/ true,
                        false,
                        None,
                    )?;
                }
            }
        }
    }
    Ok(())
}

/// Find the World parameter that can safely define a shared bottom for a
/// pair-valued, read-only `partial_fixpoint` SCC. The parameter must
/// occur in every member and every recursive SCC call must pass it unchanged
/// at the matching callee position. Among those parameters, the oldest
/// canonical World SSA generation is the captured entry snapshot; parameter
/// order is deliberately irrelevant because generated helper order is a
/// durable proof ABI. Other return shapes retain Lean's conservative fallback.
fn scc_read_only_world_bottom_param<'a>(
    scc: &[(&'a FunId, &'a crate::ir::Function)],
    program: &Program,
) -> Option<VarId> {
    use crate::ir::Type;

    let world_id =
        program.struct_id_by_qualified_name(crate::stage_04_effects::WORLD_QUALIFIED_NAME)?;
    let is_world = |ty: &Type| crate::stage_04_effects::common::is_world_type(ty, world_id);
    let returns_world = |f: &crate::ir::Function| {
        matches!(&f.signature.return_type, Type::Tuple(parts) if
            parts.len() == 2 && parts.last().is_some_and(&is_world))
    };

    if scc
        .iter()
        .any(|(_, f)| f.effects.world_writes || !returns_world(f))
    {
        return None;
    }

    let first = scc.first()?.1;
    let mut candidates: Vec<VarId> = first
        .signature
        .params
        .iter()
        .filter(|p| is_world(&p.ty))
        .map(|p| p.var.clone())
        .collect();
    candidates.retain(|candidate| {
        scc.iter().all(|(_, f)| {
            f.signature
                .params
                .iter()
                .any(|p| &p.var == candidate && is_world(&p.ty))
        })
    });

    let members: std::collections::BTreeSet<FunId> = scc.iter().map(|(fid, _)| **fid).collect();
    candidates
        .into_iter()
        .filter(|candidate| {
            scc.iter()
                .all(|(_, f)| function_forwards_param_to_scc_calls(f, candidate, &members, program))
        })
        .filter_map(|candidate| {
            crate::ir::names::world_ssa_generation(candidate.as_ref())
                .map(|generation| (generation, candidate))
        })
        .min_by(|(left_generation, left), (right_generation, right)| {
            left_generation
                .cmp(right_generation)
                .then_with(|| left.cmp(right))
        })
        .map(|(_, candidate)| candidate)
}

fn function_forwards_param_to_scc_calls(
    function: &crate::ir::Function,
    param: &VarId,
    members: &std::collections::BTreeSet<FunId>,
    program: &Program,
) -> bool {
    use crate::ir::visit::{walk_expr_default, Visitor};
    use crate::ir::Expr;

    struct ForwardingChecker<'a> {
        param: &'a VarId,
        members: &'a std::collections::BTreeSet<FunId>,
        program: &'a Program,
        valid: bool,
    }
    impl Visitor for ForwardingChecker<'_> {
        fn visit_expr(&mut self, expr: &Expr) {
            if let Expr::Call { fun, args, .. } = expr {
                if self.members.contains(fun) {
                    let forwarded = self
                        .program
                        .functions
                        .get(fun)
                        .and_then(|callee| {
                            callee
                                .signature
                                .params
                                .iter()
                                .position(|p| &p.var == self.param)
                        })
                        .and_then(|index| args.get(index))
                        .is_some_and(|arg| matches!(arg, Expr::Var(var) if var == self.param));
                    self.valid &= forwarded;
                }
            }
            walk_expr_default(self, expr);
        }
    }

    let mut checker = ForwardingChecker {
        param,
        members,
        program,
        valid: true,
    };
    checker.visit_block(&function.body);
    checker.valid
}

/// True iff this (non-trivial) SCC is safe to emit as a single mutual
/// `partial_fixpoint` block. Two shapes qualify:
///
/// 1. **Loop-anchored.** The cycle is ANCHORED on a real loop helper
///    (`LoopBody`/`LoopAfter`) and every member is one of: a loop helper, a
///    `Spec.Aborts` companion of a loop helper, or a `Synthetic` de-jump
///    continuation (`<loop>.cont_N` / labeled-block helper). All such
///    members are first-order -- their recursive calls sit directly in
///    monotone positions -- so `partial_fixpoint`'s monotonicity derivation
///    goes through (abort members additionally need their match scrutinee
///    inlined, which `render_function` does).
///
/// 2. **Tail-recursive SOURCE abort.** No loop anchor, but the SCC is the
///    `.aborts` companion (+ its `.cont_*` mirrors) of a self-recursive
///    SOURCE function whose abort recursion is TAIL-position
///    (`scc_is_collapsible_source_abort`). Its recursive `.aborts` call
///    starts life in a `match` SCRUTINEE (to decide "did the recursive step
///    abort?"), which is NOT monotone -- but when the post-recursion
///    continuation is trivially `NoAbort`, `render_function`'s
///    `collapse_tail_recursive_aborts_match` rewrites that identity
///    propagation to the bare recursive call, moving it to tail position
///    (monotone). This gate runs the SAME collapse on a clone and blesses
///    the SCC only if no recursive call remains in a scrutinee. Confirmed on
///    `sui::priority_queue::max_heapify_recursive`: both its VALUE face and
///    (after this change) its abort face render as `partial_fixpoint` with a
///    real `.eq_def`. A NON-tail source recursion (the continuation still
///    aborts) does not collapse, so it is correctly excluded and keeps the
///    opaque `partial def` fallback.
///
/// Empty SCC is not eligible.
fn scc_is_fixpoint_eligible<'a>(
    scc: &[(&'a FunId, &'a crate::ir::Function)],
    program: &Program,
) -> bool {
    use crate::ir::{FunctionKind, SpecKind};
    if scc.is_empty() {
        return false;
    }
    let is_loop_helper = |k: &FunctionKind| {
        matches!(
            k,
            FunctionKind::LoopBody { .. } | FunctionKind::LoopAfter { .. }
        )
    };
    let has_loop_anchor = scc.iter().any(|(_, f)| is_loop_helper(&f.kind));
    if !has_loop_anchor {
        return scc_is_collapsible_source_abort(scc, program);
    }
    scc.iter().all(|(_, f)| match &f.kind {
        FunctionKind::LoopBody { .. }
        | FunctionKind::LoopAfter { .. }
        | FunctionKind::Synthetic => true,
        FunctionKind::Spec {
            kind: SpecKind::Aborts,
            target,
        } => matches!(
            program.functions.get(target).map(|f| &f.kind),
            Some(FunctionKind::LoopBody { .. }) | Some(FunctionKind::LoopAfter { .. })
        ),
        _ => false,
    })
}

/// True iff this loop-anchor-free SCC is a TAIL-recursive SOURCE abort SCC
/// that becomes `partial_fixpoint`-eligible once `render_function`'s
/// abort-face collapse runs (shape 2 of [`scc_is_fixpoint_eligible`]).
///
/// Structural gate (cheap, bails fast on unrelated SCCs): every member is
/// either a `Synthetic` de-jump continuation (`.cont_*`) or the
/// `Spec::Aborts` companion of a SELF-RECURSIVE source function, with at
/// least one such abort companion present.
///
/// Collapsibility gate (faithful): run the same abort-face normalization
/// `render_function` applies -- scrutinee inline + tail-recursion collapse
/// + result-match normalization -- on a CLONE of each member, then require
/// that no member still has a recursive SCC-member call in a `match`
/// SCRUTINEE (the non-monotone position `partial_fixpoint` rejects). A
/// NON-tail source recursion keeps its scrutinee call after collapse, so it
/// is correctly rejected and stays opaque.
fn scc_is_collapsible_source_abort<'a>(
    scc: &[(&'a FunId, &'a crate::ir::Function)],
    program: &Program,
) -> bool {
    use crate::ir::{FunctionKind, SpecKind};
    let members: std::collections::BTreeSet<FunId> = scc.iter().map(|(id, _)| **id).collect();
    let mut has_source_abort = false;
    for (_, f) in scc {
        match &f.kind {
            FunctionKind::Synthetic => {}
            FunctionKind::Spec {
                kind: SpecKind::Aborts,
                target,
            } => {
                let Some(t) = program.functions.get(target) else {
                    return false;
                };
                if !crate::render::function::body_calls_self_by_name(
                    &t.body, &t.module, &t.name, program,
                ) {
                    return false;
                }
                has_source_abort = true;
            }
            _ => return false,
        }
    }
    if !has_source_abort {
        return false;
    }
    scc.iter().all(|(_, f)| {
        let mut b = f.body.clone();
        crate::render::function::inline_aborts_match_scrutinees(&mut b, program);
        crate::render::function::collapse_tail_recursive_aborts_match(&mut b, program);
        crate::render::function::normalize_aborts_result_matches(&mut b, program);
        !crate::render::function::block_has_member_call_in_match_scrutinee(&b, &members)
    })
}

/// True iff any function in this SCC is intrinsically `partial def`:
/// a loop helper, a Spec.Aborts companion of a loop helper, or a
/// source function whose body calls itself by name. Used by
/// `emit_function_sccs` to propagate partial-ness across every
/// function in a mutual block, since Lean rejects mixing.
fn scc_contains_partial_member<'a>(
    scc: &[(&'a FunId, &'a crate::ir::Function)],
    program: &Program,
) -> bool {
    use crate::ir::{FunctionKind, SpecKind};
    // A multi-member SCC is a real call cycle across its members -- genuine
    // MUTUAL source recursion (deepbook `big_vector::{slice_remove,
    // node_remove}`) calls no member by its own name, so the per-member
    // checks below miss it and the block rendered plain `def`s that Lean
    // rejected ("fail to show termination"). Nothing generated here
    // decreases structurally, so a non-fixpoint mutual block is partial.
    if scc.len() > 1 {
        return true;
    }
    for (_, f) in scc {
        match f.kind {
            FunctionKind::LoopBody { .. } | FunctionKind::LoopAfter { .. } => return true,
            FunctionKind::Spec {
                kind: SpecKind::Aborts,
                target,
            } => {
                if matches!(
                    program.functions.get(&target).map(|f| &f.kind),
                    Some(FunctionKind::LoopBody { .. }) | Some(FunctionKind::LoopAfter { .. })
                ) {
                    return true;
                }
                // The `.aborts` companion (and its stage-7 `.cont_*`
                // helpers) of a self-recursive SOURCE function mirrors
                // that recursion: `compose_callee_aborts` rewrites the
                // body's self-call into a self-call on the abort side,
                // and de-jumping splits it across `.cont_*` helpers
                // that recurse *mutually* (no member calls itself by
                // its own name). `body_calls_self_by_name` below
                // therefore misses every member, so the mutual block
                // would emit plain `def`s and Lean's structural
                // termination check rejects it. Detect it by checking
                // whether the target source is itself self-recursive
                // (it renders as `partial def`); if so the whole abort
                // SCC must be partial too. Surfaced by
                // `sui::priority_queue::max_heapify_recursive`.
                //
                // NOTE: for the TAIL-recursive sub-case,
                // `scc_is_fixpoint_eligible` now returns true (the abort
                // recursion collapses out of its match scrutinee into tail
                // position -- `collapse_tail_recursive_aborts_match`), so
                // the caller's `scc_partial = !fixpoint && scc_contains_
                // partial_member` evaluates to false and the SCC emits
                // `partial_fixpoint` instead. This branch still returns true
                // -- it stays the correct answer for the NON-tail (opaque)
                // sub-case, and is harmless when fixpoint wins.
                if let Some(t) = program.functions.get(&target) {
                    if crate::render::function::body_calls_self_by_name(
                        &t.body, &t.module, &t.name, program,
                    ) {
                        return true;
                    }
                }
            }
            _ => {}
        }
        // Self-recursive source function (`body_calls_self_by_name`
        // returns true). Use the same walker the renderer uses so we
        // stay consistent.
        if crate::render::function::body_calls_self_by_name(&f.body, &f.module, &f.name, program) {
            return true;
        }
    }
    false
}

/// Group functions into strongly-connected components (SCCs) over
/// the same dep graph that [`topo_sort_functions`] uses, and return
/// them in topological order (callees before callers).
///
/// Trivial SCCs (a single function with no self-edge) and
/// non-trivial SCCs (cycles, or single functions with a self-edge)
/// are returned uniformly as `Vec<...>`; the caller decides how to
/// emit each. The render path uses this to wrap non-trivial SCCs in
/// `mutual ... end` blocks so Lean can elaborate them together, and
/// emit trivial SCCs as plain `def`s.
///
/// Implements Tarjan's SCC algorithm iteratively (recursion would
/// blow the stack on very deep call graphs).
fn compute_function_sccs<'a>(
    items: &[(&'a FunId, &'a crate::ir::Function)],
    program: &Program,
) -> Vec<Vec<(&'a FunId, &'a crate::ir::Function)>> {
    use std::collections::BTreeMap;

    let in_module: std::collections::BTreeSet<FunId> = items.iter().map(|(id, _)| **id).collect();

    let mut deps: BTreeMap<FunId, Vec<FunId>> = BTreeMap::new();
    let mut id_to_item: BTreeMap<FunId, (&'a FunId, &'a crate::ir::Function)> = BTreeMap::new();
    for (id, f) in items.iter() {
        let mut my_deps: std::collections::BTreeSet<FunId> = Default::default();
        function_call_deps(f, &in_module, **id, &mut my_deps);
        if let crate::ir::FunctionKind::Spec { target, .. } = f.kind {
            if in_module.contains(&target) && target != **id {
                my_deps.insert(target);
            }
        }
        let mut v: Vec<FunId> = my_deps.into_iter().collect();
        v.sort();
        deps.insert(**id, v);
        id_to_item.insert(**id, (*id, *f));
    }

    // Tarjan's iterative SCC. Nodes are FunIds. We need:
    // - index, lowlink per node
    // - on-stack flag
    // - explicit work stack (Vec<(node, neighbor_index)>)
    // - SCC accumulator
    let nodes: Vec<FunId> = id_to_item.keys().copied().collect();
    let mut index_counter: u32 = 0;
    let mut indices: BTreeMap<FunId, u32> = BTreeMap::new();
    let mut lowlinks: BTreeMap<FunId, u32> = BTreeMap::new();
    let mut on_stack: std::collections::BTreeSet<FunId> = Default::default();
    let mut tarjan_stack: Vec<FunId> = Vec::new();
    let mut sccs_rev_topo: Vec<Vec<FunId>> = Vec::new();

    enum Frame {
        Enter(FunId),
        Visit(FunId, usize),
    }
    for start in &nodes {
        if indices.contains_key(start) {
            continue;
        }
        let mut work: Vec<Frame> = vec![Frame::Enter(*start)];
        while let Some(frame) = work.pop() {
            match frame {
                Frame::Enter(v) => {
                    indices.insert(v, index_counter);
                    lowlinks.insert(v, index_counter);
                    index_counter += 1;
                    tarjan_stack.push(v);
                    on_stack.insert(v);
                    work.push(Frame::Visit(v, 0));
                }
                Frame::Visit(v, ni) => {
                    let neighbors = deps.get(&v).cloned().unwrap_or_default();
                    if ni < neighbors.len() {
                        let w = neighbors[ni];
                        work.push(Frame::Visit(v, ni + 1));
                        if !indices.contains_key(&w) {
                            work.push(Frame::Enter(w));
                        } else if on_stack.contains(&w) {
                            let cur = lowlinks[&v];
                            let w_idx = indices[&w];
                            if w_idx < cur {
                                lowlinks.insert(v, w_idx);
                            }
                        }
                    } else {
                        // All neighbors processed. Propagate child lowlink
                        // to parent (via the previous Frame::Visit on the
                        // work stack, if any).
                        if let Some(Frame::Visit(parent, _)) = work.last() {
                            let parent = *parent;
                            let v_low = lowlinks[&v];
                            let p_low = lowlinks[&parent];
                            if v_low < p_low {
                                lowlinks.insert(parent, v_low);
                            }
                        }
                        if lowlinks[&v] == indices[&v] {
                            // Root of an SCC. Pop until v.
                            let mut scc: Vec<FunId> = Vec::new();
                            loop {
                                let w = tarjan_stack.pop().expect("stack non-empty in SCC pop");
                                on_stack.remove(&w);
                                scc.push(w);
                                if w == v {
                                    break;
                                }
                            }
                            // Tarjan produces SCCs in REVERSE topological
                            // order (callees before callers ends up at
                            // the end). We push into `sccs_rev_topo` and
                            // reverse at the end so the result is
                            // callees-first.
                            sccs_rev_topo.push(scc);
                        }
                    }
                }
            }
        }
    }

    // Already correct order: Tarjan emits SCCs as it discovers leaves
    // (callees) first, then callers. That's the callees-first order
    // the renderer wants. (The earlier comment about reversal was
    // wrong -- left in `_rev_topo` name only for clarity that this is
    // the raw Tarjan output; no reversal needed.)
    let mut out: Vec<Vec<(&'a FunId, &'a crate::ir::Function)>> =
        Vec::with_capacity(sccs_rev_topo.len());
    for scc in sccs_rev_topo {
        let mut entries: Vec<(&'a FunId, &'a crate::ir::Function)> = scc
            .into_iter()
            .filter_map(|id| id_to_item.get(&id).copied())
            .collect();
        // Deterministic intra-SCC order: by function name.
        entries.sort_by(|a, b| a.1.name.cmp(&b.1.name));
        out.push(entries);
    }
    out
}

/// True iff this SCC must be emitted inside a `mutual ... end` block.
/// That's the case when the SCC has more than one member, or when its
/// single member has a self-call (recursive `def f := ... f ...`).
fn scc_needs_mutual_block<'a>(
    scc: &[(&'a FunId, &'a crate::ir::Function)],
    program: &Program,
) -> bool {
    if scc.len() > 1 {
        return true;
    }
    let (id, f) = scc[0];
    let mut my_deps: std::collections::BTreeSet<FunId> = Default::default();
    let in_module: std::collections::BTreeSet<FunId> = std::iter::once(*id).collect();
    function_call_deps(f, &in_module, *id, &mut my_deps);
    if let crate::ir::FunctionKind::Spec { target, .. } = f.kind {
        if target == *id {
            return true;
        }
    }
    my_deps.contains(id)
}

fn function_call_deps(
    f: &crate::ir::Function,
    in_module: &std::collections::BTreeSet<FunId>,
    own_id: FunId,
    out: &mut std::collections::BTreeSet<FunId>,
) {
    walk_block_for_call_deps(&f.body, in_module, own_id, out);
}

fn walk_block_for_call_deps(
    b: &crate::ir::Block,
    in_module: &std::collections::BTreeSet<FunId>,
    own_id: FunId,
    out: &mut std::collections::BTreeSet<FunId>,
) {
    use crate::ir::visit::{walk_expr_default, Visitor};
    use crate::ir::Expr;
    struct C<'a> {
        in_module: &'a std::collections::BTreeSet<FunId>,
        own_id: FunId,
        out: &'a mut std::collections::BTreeSet<FunId>,
    }
    impl Visitor for C<'_> {
        fn visit_expr(&mut self, e: &Expr) {
            if let Expr::Call { fun, .. } = e {
                if self.in_module.contains(fun) && *fun != self.own_id {
                    self.out.insert(*fun);
                }
            }
            walk_expr_default(self, e);
        }
    }
    C {
        in_module,
        own_id,
        out,
    }
    .visit_block(b);
}
