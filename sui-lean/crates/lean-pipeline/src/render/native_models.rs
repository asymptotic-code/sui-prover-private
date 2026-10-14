use std::collections::{BTreeMap, BTreeSet, HashSet};
use std::fs;
use std::path::{Path, PathBuf};

use serde::Deserialize;

use crate::ir::connectives::Connective;
use crate::ir::{canonical_addressed_module, Program};

use super::environment::{
    query_declarations, DeclarationObservation, DeclarationQuery, DeclarationQueryGroup,
};
use super::loop_termination::LoopMode;
use super::{RenderError, RenderResult};

const POLICY_FILE: &str = "native_model_policy.toml";
pub(super) const MANIFEST_FILE: &str = "native_models.toml";

#[derive(Debug, Clone, Copy, Deserialize, PartialEq, Eq, PartialOrd, Ord)]
#[serde(rename_all = "snake_case")]
enum ModelSource {
    Intrinsic,
    GeneratedOpaque,
    GeneratedTest,
    Handwritten,
    Missing,
}

impl ModelSource {
    fn as_str(self) -> &'static str {
        match self {
            Self::Intrinsic => "intrinsic",
            Self::GeneratedOpaque => "generated_opaque",
            Self::GeneratedTest => "generated_test",
            Self::Handwritten => "handwritten",
            Self::Missing => "missing",
        }
    }
}

#[derive(Debug, Clone, Copy, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
enum ModelClassification {
    Intrinsic,
    ModeledSpecNative,
    TrustedGeneratedOpaque,
    Trusted,
    TestOnly,
    Unclassified,
    MissingModel,
}

impl ModelClassification {
    fn as_str(self) -> &'static str {
        match self {
            Self::Intrinsic => "intrinsic",
            Self::ModeledSpecNative => "modeled_spec_native",
            Self::TrustedGeneratedOpaque => "trusted_generated_opaque",
            Self::Trusted => "trusted",
            Self::TestOnly => "test_only",
            Self::Unclassified => "unclassified",
            Self::MissingModel => "missing_model",
        }
    }
}

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct PolicyFile {
    version: u32,
    #[serde(default)]
    rule: Vec<PolicyRule>,
}

#[derive(Debug, Clone, Deserialize)]
#[serde(deny_unknown_fields)]
struct PolicyRule {
    package: String,
    module: String,
    function: String,
    #[serde(default)]
    address: Option<String>,
    source: ModelSource,
    classification: ModelClassification,
    justification: String,
    #[serde(skip)]
    package_local: bool,
}

#[derive(Debug)]
struct NativeModelIdentity {
    fid: crate::ir::FunId,
    native: String,
    package: String,
    module: String,
    function: String,
    address: Option<String>,
    lean_model: String,
}

#[derive(Debug)]
struct ModelCandidate {
    model_file: String,
    source_path: PathBuf,
    module: String,
    declaration: String,
    shipped_prover: bool,
    package_overlay: bool,
}

#[derive(Debug)]
enum SelectedModel {
    Fixed(ModelSource),
    Candidate {
        candidate: ModelCandidate,
        observation: DeclarationObservation,
    },
    Missing,
}

impl SelectedModel {
    fn source(&self) -> ModelSource {
        match self {
            Self::Fixed(source) => *source,
            Self::Candidate {
                candidate,
                observation,
            } => {
                let accepted_kind = if candidate.shipped_prover {
                    observation.kind.is_definition()
                } else {
                    observation.kind.is_native_model()
                };
                if accepted_kind && observation.declared_in_expected_module {
                    ModelSource::Handwritten
                } else {
                    ModelSource::Missing
                }
            }
            Self::Missing => ModelSource::Missing,
        }
    }

    fn candidate(&self) -> Option<&ModelCandidate> {
        match self {
            Self::Candidate { candidate, .. } => Some(candidate),
            Self::Fixed(_) | Self::Missing => None,
        }
    }

    fn observation(&self) -> Option<&DeclarationObservation> {
        match self {
            Self::Candidate { observation, .. } => Some(observation),
            Self::Fixed(_) | Self::Missing => None,
        }
    }
}

#[derive(Debug)]
struct TrustDecision {
    classification: ModelClassification,
    justification: String,
}

#[derive(Debug)]
struct NativeModelPlanRow {
    identity: NativeModelIdentity,
    selected: SelectedModel,
    decision: TrustDecision,
}

impl NativeModelPlanRow {
    fn is_accepted(&self, mode: LoopMode) -> bool {
        let shared = matches!(
            self.decision.classification,
            ModelClassification::Intrinsic
                | ModelClassification::ModeledSpecNative
                | ModelClassification::Trusted
                | ModelClassification::TrustedGeneratedOpaque
        );
        shared
            || (matches!(mode, LoopMode::Test | LoopMode::Execution)
                && self.decision.classification == ModelClassification::TestOnly)
    }

    fn rejection(&self, mode: LoopMode) -> Option<String> {
        (!self.is_accepted(mode)).then(|| {
            format!(
                "{} ({})",
                self.identity.native,
                self.decision.classification.as_str()
            )
        })
    }

    fn write_manifest_entry(&self, output: &mut String) {
        output.push_str("\n[[model]]\n");
        output.push_str(&format!("fid = {}\n", self.identity.fid));
        output.push_str(&format!(
            "native = \"{}\"\n",
            toml_string(&self.identity.native)
        ));
        output.push_str(&format!(
            "package = \"{}\"\n",
            toml_string(&self.identity.package)
        ));
        output.push_str(&format!(
            "module = \"{}\"\n",
            toml_string(&self.identity.module)
        ));
        output.push_str(&format!(
            "function = \"{}\"\n",
            toml_string(&self.identity.function)
        ));
        if let Some(address) = &self.identity.address {
            output.push_str(&format!("address = \"{}\"\n", toml_string(address)));
        }
        output.push_str(&format!(
            "lean_model = \"{}\"\n",
            toml_string(&self.identity.lean_model)
        ));
        if let Some(candidate) = self.selected.candidate() {
            output.push_str(&format!(
                "model_file = \"{}\"\n",
                toml_string(&candidate.model_file)
            ));
        }
        if let Some(observation) = self.selected.observation() {
            output.push_str(&format!(
                "declaration_kind = \"{}\"\n",
                observation.kind.as_str()
            ));
            output.push_str(&format!(
                "declaration_module_matches = {}\n",
                observation.declared_in_expected_module
            ));
        }
        output.push_str(&format!(
            "source = \"{}\"\n",
            self.selected.source().as_str()
        ));
        output.push_str(&format!(
            "classification = \"{}\"\n",
            self.decision.classification.as_str()
        ));
        if !self.decision.justification.is_empty() {
            output.push_str(&format!(
                "justification = \"{}\"\n",
                toml_string(&self.decision.justification)
            ));
        }
    }
}

#[derive(Debug)]
struct NativeModelPlan {
    rows: Vec<NativeModelPlanRow>,
}

impl NativeModelPlan {
    fn build(
        program: &Program,
        output_dir: &Path,
        lemmas_dir: Option<&Path>,
        package_policy_dir: Option<&Path>,
        user_package: Option<&str>,
        root_package: Option<&str>,
        copied_model_files: &HashSet<PathBuf>,
        package_overlay_model_files: &HashSet<PathBuf>,
    ) -> RenderResult<Self> {
        let mut rules = Vec::new();
        if let Some(dir) = lemmas_dir {
            load_policy(&dir.join(POLICY_FILE), &mut rules, true)?;
        }
        if let Some(dir) = package_policy_dir {
            load_policy(&dir.join(POLICY_FILE), &mut rules, false)?;
        }

        let inputs = native_model_plan_inputs(
            program,
            output_dir,
            user_package,
            copied_model_files,
            package_overlay_model_files,
        )?;
        let observations = query_model_observations(program, output_dir, user_package, &inputs)?;
        let mut rows = Vec::with_capacity(inputs.len());
        for input in inputs {
            let NativeModelPlanInput {
                identity,
                unresolved,
            } = input;
            let selected = select_model(unresolved, &observations)?;
            let decision = trust_decision(program, &rules, root_package, &identity, &selected);
            rows.push(NativeModelPlanRow {
                identity,
                selected,
                decision,
            });
        }
        rows.sort_by(|left, right| {
            left.identity
                .native
                .cmp(&right.identity.native)
                .then_with(|| left.identity.fid.cmp(&right.identity.fid))
        });
        Ok(Self { rows })
    }

    fn manifest(&self) -> String {
        let mut output = String::from(
            "# Generated by lean-pipeline. Every native referenced by emitted IR is classified.\n\
             # Schema v1 readers must ignore unknown model keys; declaration_* fields are additive evidence.\n\
             version = 1\n",
        );
        for row in &self.rows {
            row.write_manifest_entry(&mut output);
        }
        output
    }

    fn write_manifest(&self, output_dir: &Path) -> RenderResult<()> {
        let path = output_dir.join(MANIFEST_FILE);
        fs::write(&path, self.manifest()).map_err(|error| RenderError::Io {
            what: format!("write({}): {}", path.display(), error),
        })
    }

    fn enforce(&self, output_dir: &Path, mode: LoopMode) -> RenderResult<()> {
        let rejected: Vec<String> = self
            .rows
            .iter()
            .filter_map(|row| row.rejection(mode))
            .collect();
        if rejected.is_empty() {
            return Ok(());
        }
        Err(RenderError::NativeModelPolicy {
            what: format!(
                "{} output references rejected native models: {}; see {}",
                match mode {
                    LoopMode::Proof => "proof",
                    LoopMode::Test => "test",
                    LoopMode::Execution => "execution",
                },
                rejected.join(", "),
                output_dir.join(MANIFEST_FILE).display()
            ),
        })
    }
}

#[derive(Debug)]
enum UnresolvedModel {
    Fixed(ModelSource),
    Candidate(ModelCandidate),
    Missing,
}

impl UnresolvedModel {
    fn candidate(&self) -> Option<&ModelCandidate> {
        match self {
            Self::Candidate(candidate) => Some(candidate),
            Self::Fixed(_) | Self::Missing => None,
        }
    }
}

#[derive(Debug)]
struct NativeModelPlanInput {
    identity: NativeModelIdentity,
    unresolved: UnresolvedModel,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct NativeForwardResolution {
    pub path: PathBuf,
    pub import: String,
}

pub(super) fn resolve_native_forward(
    output_dir: &Path,
    package: &str,
    module: &str,
    mut is_available: impl FnMut(&Path) -> bool,
) -> Option<NativeForwardResolution> {
    let namespace = super::escape::module_name_to_namespace(module);
    let sibling = output_dir
        .join(package)
        .join(format!("{}Natives.lean", namespace));
    if is_available(&sibling) {
        return Some(NativeForwardResolution {
            path: sibling,
            import: format!("{}.{}Natives", package, namespace),
        });
    }

    let mirror = output_dir
        .join("MoveStdlib")
        .join(format!("{}Natives.lean", namespace));
    // This fallback is intentionally package-agnostic: historically every
    // non-MoveStdlib package with a same-stem mirror has forwarded to it.
    if package != "MoveStdlib" && is_available(&mirror) {
        return Some(NativeForwardResolution {
            path: mirror,
            import: format!("MoveStdlib.{}Natives", namespace),
        });
    }

    None
}

fn native_model_plan_inputs(
    program: &Program,
    output_dir: &Path,
    user_package: Option<&str>,
    copied_model_files: &HashSet<PathBuf>,
    package_overlay_model_files: &HashSet<PathBuf>,
) -> RenderResult<Vec<NativeModelPlanInput>> {
    let referenced = referenced_native_fids(program, user_package);
    let generated_opaque_fids = trusted_generated_opaque_fids(program);
    let mut inputs = Vec::with_capacity(referenced.len());
    for fid in referenced {
        let decl = &program.natives.decls[&fid];
        let module = program
            .modules
            .get(&decl.module)
            .ok_or(RenderError::UnknownModId { id: decl.module })?;
        let package = if module.package_name.is_empty() {
            "NewPipeline"
        } else {
            &module.package_name
        };
        let native = format!("{}::{}::{}", package, module.name, decl.name);
        let address = canonical_addressed_module(module).and_then(|identity| {
            identity
                .split_once("::")
                .map(|(address, _)| address.to_string())
        });
        let mut lean_model = super::escape::escape_identifier(&decl.name);
        if program.ghost_vars.contains_key(&fid) {
            lean_model.push_str("__ghost");
        }
        let unresolved = if generated_opaque_fids.contains(&fid) {
            UnresolvedModel::Fixed(ModelSource::GeneratedOpaque)
        } else if is_intrinsic_decl(fid, decl, program) {
            UnresolvedModel::Fixed(ModelSource::Intrinsic)
        } else if is_renderer_owned_end_transaction_model(decl, program) {
            UnresolvedModel::Fixed(ModelSource::GeneratedTest)
        } else if let Some(candidate) = model_candidate(
            output_dir,
            package,
            &module.name,
            &decl.name,
            &lean_model,
            copied_model_files,
            package_overlay_model_files,
        )? {
            UnresolvedModel::Candidate(candidate)
        } else {
            UnresolvedModel::Missing
        };
        inputs.push(NativeModelPlanInput {
            identity: NativeModelIdentity {
                fid,
                native,
                package: package.to_string(),
                module: module.name.clone(),
                function: decl.name.clone(),
                address,
                lean_model,
            },
            unresolved,
        });
    }
    Ok(inputs)
}

fn query_model_observations(
    program: &Program,
    output_dir: &Path,
    user_package: Option<&str>,
    inputs: &[NativeModelPlanInput],
) -> RenderResult<BTreeMap<(String, String), DeclarationObservation>> {
    let mut grouped_queries: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
    for candidate in inputs
        .iter()
        .filter_map(|input| input.unresolved.candidate())
    {
        grouped_queries
            .entry(candidate.module.clone())
            .or_default()
            .insert(candidate.declaration.clone());
    }
    let queried_model_fids: BTreeSet<_> = inputs
        .iter()
        .filter(|input| input.unresolved.candidate().is_some())
        .map(|input| input.identity.fid)
        .collect();
    for function in program.functions.values() {
        let Some(module) = program.modules.get(&function.module) else {
            continue;
        };
        if user_package.is_some_and(|package| module.package_name != package && !module.is_native) {
            continue;
        }
        let callees = crate::stage_04_effects::common::collect_callees(&function.body);
        if !callees
            .iter()
            .any(|callee| queried_model_fids.contains(callee))
        {
            continue;
        }
        let location = super::module_render_location(&module.package_name, &module.name);
        if output_dir
            .join(&location.package)
            .join(format!("{}.lean", location.file_stem))
            .is_file()
        {
            grouped_queries.entry(location.import_path).or_default();
        }
    }
    let query_groups: Vec<DeclarationQueryGroup> = grouped_queries
        .into_iter()
        .map(|(module, declarations)| DeclarationQueryGroup {
            module,
            declarations: declarations
                .into_iter()
                .map(DeclarationQuery::untyped)
                .collect(),
        })
        .collect();
    let source_snapshots: BTreeMap<_, _> = inputs
        .iter()
        .filter_map(|input| input.unresolved.candidate())
        .map(|candidate| {
            read_model_source(&candidate.source_path)
                .map(|source| (candidate.source_path.clone(), source))
        })
        .collect::<RenderResult<_>>()?;
    let queried = query_declarations(output_dir, &query_groups, "native-model classification")?;
    for (path, expected) in &source_snapshots {
        if &read_model_source(path)? != expected {
            return Err(RenderError::LeanEnvironmentQuery {
                what: format!(
                    "native-model source changed while its elaborated declaration was queried: {}",
                    path.display()
                ),
            });
        }
    }
    let mut observations = BTreeMap::new();
    for (group, group_observations) in query_groups.iter().zip(queried) {
        for (declaration, observation) in group.declarations.iter().zip(group_observations) {
            observations.insert(
                (group.module.clone(), declaration.name.clone()),
                observation,
            );
        }
    }
    Ok(observations)
}

fn select_model(
    unresolved: UnresolvedModel,
    observations: &BTreeMap<(String, String), DeclarationObservation>,
) -> RenderResult<SelectedModel> {
    match unresolved {
        UnresolvedModel::Fixed(source) => Ok(SelectedModel::Fixed(source)),
        UnresolvedModel::Missing => Ok(SelectedModel::Missing),
        UnresolvedModel::Candidate(candidate) => {
            let observation = observations
                .get(&(candidate.module.clone(), candidate.declaration.clone()))
                .cloned()
                .ok_or_else(|| RenderError::LeanEnvironmentQuery {
                    what: format!(
                        "native-model classification returned no result for `{}` in `{}`",
                        candidate.declaration, candidate.module
                    ),
                })?;
            Ok(SelectedModel::Candidate {
                candidate,
                observation,
            })
        }
    }
}

fn trust_decision(
    program: &Program,
    rules: &[PolicyRule],
    root_package: Option<&str>,
    identity: &NativeModelIdentity,
    selected: &SelectedModel,
) -> TrustDecision {
    let source = selected.source();
    let is_concrete_definition = selected.observation().is_some_and(|observation| {
        observation.kind.is_definition() && observation.declared_in_expected_module
    });
    let matched = best_rule_with_filter(
        rules,
        &identity.package,
        &identity.module,
        &identity.function,
        source,
        |rule| {
            policy_native_identity_matches(program, identity, rule)
                && policy_origin_matches_model(rule, selected.candidate())
        },
    );
    let (classification, justification) = match source {
        ModelSource::Intrinsic => (
            ModelClassification::Intrinsic,
            "implemented directly by the renderer or Lean prelude".to_string(),
        ),
        ModelSource::GeneratedOpaque => (
            ModelClassification::TrustedGeneratedOpaque,
            "pipeline-generated opaque ghost output constrained by its trusted specification axiom"
                .to_string(),
        ),
        ModelSource::GeneratedTest => (
            ModelClassification::TestOnly,
            "renderer-owned executable test-harness semantics".to_string(),
        ),
        ModelSource::Handwritten => matched.map_or_else(
            || {
                if is_trusted_shipped_prover_decl(
                    program,
                    identity,
                    selected.candidate(),
                ) && is_concrete_definition
                {
                    (
                        ModelClassification::Trusted,
                        "shipped Prover native model with an elaborated concrete definition declared in its matching module"
                            .to_string(),
                    )
                } else if root_package == Some(identity.package.as_str())
                    && program.natives.decls[&identity.fid].user_native == Some(true)
                    && selected
                        .candidate()
                        .is_some_and(|candidate| candidate.package_overlay)
                    && is_concrete_definition
                {
                    (
                        ModelClassification::ModeledSpecNative,
                        "root-package spec-only native with an exact handwritten Lean definition"
                            .to_string(),
                    )
                } else {
                    (ModelClassification::Unclassified, String::new())
                }
            },
            |rule| (rule.classification, rule.justification.clone()),
        ),
        ModelSource::Missing => (ModelClassification::MissingModel, String::new()),
    };
    TrustDecision {
        classification,
        justification,
    }
}

pub(super) fn classify_and_write_with_overlays(
    program: &Program,
    output_dir: &Path,
    lemmas_dir: Option<&Path>,
    package_policy_dir: Option<&Path>,
    user_package: Option<&str>,
    root_package: Option<&str>,
    mode: LoopMode,
    copied_model_files: &HashSet<PathBuf>,
    package_overlay_model_files: &HashSet<PathBuf>,
) -> RenderResult<()> {
    let plan = NativeModelPlan::build(
        program,
        output_dir,
        lemmas_dir,
        package_policy_dir,
        user_package,
        root_package,
        copied_model_files,
        package_overlay_model_files,
    )?;
    plan.write_manifest(output_dir)?;
    plan.enforce(output_dir, mode)
}

#[cfg(test)]
fn classify_and_write(
    program: &Program,
    output_dir: &Path,
    lemmas_dir: Option<&Path>,
    package_policy_dir: Option<&Path>,
    user_package: Option<&str>,
    root_package: Option<&str>,
    mode: LoopMode,
    copied_model_files: &HashSet<PathBuf>,
) -> RenderResult<()> {
    classify_and_write_with_overlays(
        program,
        output_dir,
        lemmas_dir,
        package_policy_dir,
        user_package,
        root_package,
        mode,
        copied_model_files,
        copied_model_files,
    )
}

fn is_trusted_shipped_prover_decl(
    program: &Program,
    identity: &NativeModelIdentity,
    candidate: Option<&ModelCandidate>,
) -> bool {
    let Some(candidate) = candidate else {
        return false;
    };
    let Some(decl) = program.natives.decls.get(&identity.fid) else {
        return false;
    };
    let Some(module) = program.modules.get(&decl.module) else {
        return false;
    };
    let expected_module = match identity.module.as_str() {
        "prover" => "0x0::prover",
        "vector_iter" => "0x0::vector_iter",
        _ => return false,
    };
    candidate.shipped_prover
        && identity.package == "Prover"
        && decl.is_framework
        && decl.user_native.is_none()
        && module.is_native
        && canonical_addressed_module(module).as_deref() == Some(expected_module)
        && matches!(
            (identity.module.as_str(), identity.function.as_str()),
            (
                "prover",
                "type_inv"
                    | "drop"
                    | "fresh"
                    | "val"
                    | "ref"
                    | "requires"
                    | "ensures"
                    | "asserts"
                    | "invariant_begin"
                    | "invariant_end"
                    | "implies"
                    | "asserts_of"
                    | "boogie_split_here"
                    | "boogie_focus"
                    | "boogie_allow_path_isolation"
                    | "begin_forall_lambda"
                    | "end_forall_lambda"
                    | "begin_exists_lambda"
                    | "end_exists_lambda"
            ) | ("vector_iter", "range" | "slice" | "sum" | "sum_range")
        )
}

fn policy_native_identity_matches(
    program: &Program,
    identity: &NativeModelIdentity,
    rule: &PolicyRule,
) -> bool {
    let Some(decl) = program.natives.decls.get(&identity.fid) else {
        return false;
    };
    let Some(module) = program.modules.get(&decl.module) else {
        return false;
    };
    let Some(actual_module) = canonical_addressed_module(module) else {
        return false;
    };
    let reserved_address = match identity.package.as_str() {
        "MoveStdlib" => Some("0x1"),
        "Sui" => Some("0x2"),
        "SuiSystem" => Some("0x3"),
        "Prover" => Some("0x0"),
        _ => None,
    };
    if reserved_address
        .is_some_and(|address| actual_module != format!("{address}::{}", identity.module))
    {
        return false;
    }
    rule.address
        .as_deref()
        .is_none_or(|address| actual_module == format!("{address}::{}", identity.module))
}

fn policy_origin_matches_model(rule: &PolicyRule, candidate: Option<&ModelCandidate>) -> bool {
    candidate.is_none_or(|candidate| !candidate.package_overlay || rule.package_local)
}

pub(super) fn referenced_native_fids(
    program: &Program,
    user_package: Option<&str>,
) -> BTreeSet<crate::ir::FunId> {
    let mut referenced = BTreeSet::new();
    for function in program.functions.values().filter(|function| {
        user_package.is_none_or(|package| {
            program
                .modules
                .get(&function.module)
                .is_some_and(|module| module.package_name == package || module.is_native)
        })
    }) {
        referenced.extend(
            crate::stage_04_effects::common::collect_callees(&function.body)
                .into_iter()
                .filter(|callee| program.natives.decls.contains_key(callee)),
        );
    }
    referenced
}

fn trusted_generated_opaque_fids(program: &Program) -> BTreeSet<crate::ir::FunId> {
    let trusted_pairs: BTreeSet<_> = program
        .trusted_spec_to_impl
        .iter()
        .map(|(source, (target, _))| (*source, *target))
        .collect();
    let constrained_impls: BTreeSet<_> = program
        .functions
        .values()
        .filter_map(|function| match &function.kind {
            crate::ir::FunctionKind::Axiom { target, source, .. }
                if trusted_pairs.contains(&(*source, *target)) =>
            {
                Some(*target)
            }
            _ => None,
        })
        .collect();
    program
        .ghost_opaque_outputs
        .iter()
        .filter_map(|(impl_fid, outputs)| constrained_impls.contains(impl_fid).then_some(outputs))
        .flatten()
        .map(|(_, _, fid)| *fid)
        .collect()
}

fn model_candidate(
    output_dir: &Path,
    package: &str,
    module: &str,
    function: &str,
    lean_model: &str,
    copied_model_files: &HashSet<PathBuf>,
    package_overlay_model_files: &HashSet<PathBuf>,
) -> RenderResult<Option<ModelCandidate>> {
    let forward = resolve_native_forward(output_dir, package, module, |path| {
        copied_model_files.contains(path)
    });
    let shipped_prover = match (package, module) {
        ("Prover", "prover") => Some(output_dir.join("Prover").join("Prover.lean")),
        ("Prover", "vector_iter") => Some(output_dir.join("Prover").join("Vector_iter.lean")),
        _ => None,
    };
    let (candidate, shipped_prover) = if let Some(forward) = forward {
        (Some(forward.path), false)
    } else if let Some(path) = shipped_prover.filter(|path| copied_model_files.contains(path)) {
        (Some(path), true)
    } else {
        (None, false)
    };
    let Some(path) = candidate else {
        return Ok(None);
    };
    let relative = path
        .strip_prefix(output_dir)
        .unwrap_or(&path)
        .to_string_lossy()
        .replace('\\', "/");
    let query_module = relative
        .strip_suffix(".lean")
        .ok_or_else(|| RenderError::LeanEnvironmentQuery {
            what: format!("native model path is not a Lean source file: {relative}"),
        })?
        .replace('/', ".");
    let declaration = format!(
        "{}.{}",
        normalize_lean_name(&super::escape::module_render_namespace(package, module)),
        normalize_lean_name(lean_model)
    );
    let package_overlay = package_overlay_model_files.contains(&path);
    Ok(Some(ModelCandidate {
        model_file: relative,
        source_path: path,
        module: query_module,
        declaration,
        shipped_prover,
        package_overlay,
    }))
}

pub(super) fn is_renderer_owned_end_transaction_model(
    decl: &crate::ir::NativeDecl,
    program: &Program,
) -> bool {
    let Some(module) = program.modules.get(&decl.module) else {
        return false;
    };
    let Some(world_id) =
        program.struct_id_by_qualified_name(crate::stage_04_effects::WORLD_QUALIFIED_NAME)
    else {
        return false;
    };
    let [world_param] = decl.signature.params.as_slice() else {
        return false;
    };
    let crate::ir::Type::Tuple(results) = &decl.signature.return_type else {
        return false;
    };
    let [transaction_effects, returned_world] = results.as_slice() else {
        return false;
    };
    let crate::ir::Type::Struct {
        struct_id: transaction_effects_id,
        type_args,
    } = transaction_effects
    else {
        return false;
    };
    let exact_transaction_effects = type_args.is_empty()
        && program
            .structs
            .get(transaction_effects_id)
            .is_some_and(|structure| {
                structure.module_id == decl.module && structure.name == "TransactionEffects"
            });
    decl.name == "end_transaction"
        && decl.user_native == Some(false)
        && !decl.is_framework
        && decl.spec_target.is_none()
        && decl.effects == crate::ir::Effects::CONSERVATIVE
        && decl.signature.type_params.is_empty()
        && world_param.name == crate::stage_04_effects::common::WORLD_VAR
        && world_param.var == crate::stage_04_effects::common::world_varid()
        && crate::stage_04_effects::common::is_world_type(&world_param.ty, world_id)
        && exact_transaction_effects
        && crate::stage_04_effects::common::is_world_type(returned_world, world_id)
        && module.package_name == "Sui"
        && canonical_addressed_module(module).as_deref() == Some("0x2::test_scenario")
}

fn read_model_source(path: &Path) -> RenderResult<Vec<u8>> {
    let metadata =
        fs::symlink_metadata(path).map_err(|error| RenderError::LeanEnvironmentQuery {
            what: format!("inspect native-model source {}: {error}", path.display()),
        })?;
    if !metadata.is_file() || metadata.file_type().is_symlink() {
        return Err(RenderError::LeanEnvironmentQuery {
            what: format!(
                "native-model source must be a regular non-symlink file: {}",
                path.display()
            ),
        });
    }
    fs::read(path).map_err(|error| RenderError::LeanEnvironmentQuery {
        what: format!("read native-model source {}: {error}", path.display()),
    })
}

fn is_intrinsic_decl(
    fid: crate::ir::FunId,
    decl: &crate::ir::NativeDecl,
    program: &Program,
) -> bool {
    super::bounded_nat::is_intrinsic_decl(fid, decl, program)
        || is_connective_intrinsic(decl)
        || is_mutation_intrinsic(decl, program)
}

pub(super) fn is_bcs_to_bytes_model(program: &Program, fid: crate::ir::FunId) -> bool {
    let Some(decl) = program.natives.decls.get(&fid) else {
        return false;
    };
    let Some(module) = program.modules.get(&decl.module) else {
        return false;
    };
    let exact_module = matches!(
        (
            module.package_name.as_str(),
            canonical_addressed_module(module).as_deref()
        ),
        ("MoveStdlib", Some("0x1::bcs")) | ("Sui", Some("0x2::bcs"))
    );
    decl.name == "to_bytes"
        && decl.user_native.is_none()
        && decl.spec_target.is_none()
        && decl.effects == crate::ir::Effects::PURE
        && decl.signature.type_params.len() == 1
        && matches!(
            decl.signature.params.as_slice(),
            [crate::ir::Param {
                ty: crate::ir::Type::Reference(inner),
                ..
            }] if **inner == crate::ir::Type::TypeParam(0)
        )
        && decl.signature.return_type == crate::ir::Type::Vector(Box::new(crate::ir::Type::UInt(8)))
        && exact_module
}

fn is_connective_intrinsic(decl: &crate::ir::NativeDecl) -> bool {
    Connective::from_native_decl(decl).is_some()
}

fn is_mutation_intrinsic(decl: &crate::ir::NativeDecl, program: &Program) -> bool {
    let Some(module) = program.modules.get(&decl.module) else {
        return false;
    };
    decl.name == "Mutation.uninit"
        && module.package_name == "Prelude"
        && module.name == "Prelude"
        && module.is_native
        && decl.is_framework
        && decl.user_native.is_none()
        && !decl.explicit_pure
        && decl.effects == crate::ir::Effects::PURE
        && decl.spec_target.is_none()
        && decl.signature.type_params.len() == 1
        && decl.signature.type_params[0] == "T"
        && decl.signature.params.len() == 1
        && decl.signature.params[0].name == "i"
        && decl.signature.params[0].var == crate::ir::VarId::from("$t0")
        && decl.signature.params[0].ty == crate::ir::Type::UInt(64)
        && decl.signature.return_type
            == crate::ir::Type::MutableRef {
                inner: Box::new(crate::ir::Type::TypeParam(0)),
                root: Box::new(crate::ir::Type::TypeParam(0)),
            }
}

pub(super) fn normalize_lean_name(name: &str) -> String {
    name.replace(['«', '»'], "")
}

fn load_policy(
    path: &Path,
    rules: &mut Vec<PolicyRule>,
    allow_broad_trust: bool,
) -> RenderResult<()> {
    if !path.exists() {
        return Ok(());
    }
    let input = fs::read_to_string(path).map_err(|error| RenderError::NativeModelPolicy {
        what: format!("read {}: {}", path.display(), error),
    })?;
    let mut policy: PolicyFile =
        toml::from_str(&input).map_err(|error| RenderError::NativeModelPolicy {
            what: format!("parse {}: {}", path.display(), error),
        })?;
    validate_policy(path, &mut policy)?;
    if !allow_broad_trust {
        for (index, rule) in policy.rule.iter().enumerate() {
            if rule.classification == ModelClassification::Trusted
                && [&rule.package, &rule.module, &rule.function]
                    .into_iter()
                    .any(|selector| selector == "*")
            {
                return policy_error(
                    path,
                    format!(
                        "rule {} grants downstream trust with a wildcard; use an exact package, module, and function",
                        index + 1
                    ),
                );
            }
            if rule.address.is_none() {
                return policy_error(
                    path,
                    format!(
                        "rule {} is package-local and must pin the native module address",
                        index + 1
                    ),
                );
            }
        }
    }
    for rule in &mut policy.rule {
        rule.package_local = !allow_broad_trust;
    }
    rules.extend(policy.rule);
    Ok(())
}

fn validate_policy(path: &Path, policy: &mut PolicyFile) -> RenderResult<()> {
    if policy.version != 1 {
        return policy_error(path, format!("unsupported version {}", policy.version));
    }
    let mut selectors = BTreeSet::new();
    for (index, rule) in policy.rule.iter_mut().enumerate() {
        for (label, selector) in [
            ("package", &rule.package),
            ("module", &rule.module),
            ("function", &rule.function),
        ] {
            if selector.trim().is_empty()
                || selector.trim() != selector
                || (selector.contains('*') && selector != "*")
            {
                return policy_error(
                    path,
                    format!(
                        "rule {} has invalid {} selector {:?}",
                        index + 1,
                        label,
                        selector
                    ),
                );
            }
        }
        if let Some(address) = &rule.address {
            let digits = address.strip_prefix("0x").unwrap_or_default();
            if digits.is_empty()
                || !digits
                    .bytes()
                    .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
                || (digits.len() > 1 && digits.starts_with('0'))
            {
                return policy_error(
                    path,
                    format!(
                        "rule {} has non-canonical address {:?}; use lowercase 0x-prefixed hex without leading zeroes",
                        index + 1,
                        address
                    ),
                );
            }
        }
        if !matches!(
            rule.classification,
            ModelClassification::Trusted | ModelClassification::TestOnly
        ) {
            return policy_error(
                path,
                format!(
                    "rule {} cannot assign classification {}",
                    index + 1,
                    rule.classification.as_str()
                ),
            );
        }
        if rule.source != ModelSource::Handwritten {
            return policy_error(
                path,
                format!(
                    "rule {} cannot reclassify source {}",
                    index + 1,
                    rule.source.as_str()
                ),
            );
        }
        rule.justification = rule.justification.trim().to_string();
        if rule.justification.is_empty() {
            return policy_error(
                path,
                format!("rule {} has a blank justification", index + 1),
            );
        }
        let key = (
            rule.package.clone(),
            rule.module.clone(),
            rule.function.clone(),
            rule.address.clone(),
            rule.source,
        );
        if !selectors.insert(key) {
            return policy_error(path, format!("rule {} duplicates a selector", index + 1));
        }
    }
    Ok(())
}

fn policy_error<T>(path: &Path, message: String) -> RenderResult<T> {
    Err(RenderError::NativeModelPolicy {
        what: format!("invalid {}: {}", path.display(), message),
    })
}

fn best_rule<'a>(
    rules: &'a [PolicyRule],
    package: &str,
    module: &str,
    function: &str,
    source: ModelSource,
) -> Option<&'a PolicyRule> {
    best_rule_with_filter(rules, package, module, function, source, |_| true)
}

fn best_rule_with_filter<'a>(
    rules: &'a [PolicyRule],
    package: &str,
    module: &str,
    function: &str,
    source: ModelSource,
    mut additional_filter: impl FnMut(&PolicyRule) -> bool,
) -> Option<&'a PolicyRule> {
    rules
        .iter()
        .enumerate()
        .filter(|(_, rule)| {
            rule.source == source
                && selector_matches(&rule.package, package)
                && selector_matches(&rule.module, module)
                && selector_matches(&rule.function, function)
                && additional_filter(rule)
        })
        .max_by_key(|(index, rule)| {
            (
                usize::from(rule.classification == ModelClassification::TestOnly),
                specificity(rule),
                *index,
            )
        })
        .map(|(_, rule)| rule)
}

fn selector_matches(selector: &str, value: &str) -> bool {
    selector == "*" || selector == value
}

fn specificity(rule: &PolicyRule) -> usize {
    [&rule.package, &rule.module, &rule.function]
        .into_iter()
        .filter(|selector| selector.as_str() != "*")
        .count()
}

fn toml_string(value: &str) -> String {
    value.replace('\\', "\\\\").replace('"', "\\\"")
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::builder::{call, just};
    use crate::ir::{Effects, Function, FunctionKind, Module, NativeDecl, Signature, Struct, Type};

    fn parse_policy(input: &str) -> PolicyFile {
        toml::from_str(input).unwrap()
    }

    fn program_with_missing_native() -> Program {
        let mut program = Program::default();
        program.modules.insert(
            0,
            Module {
                name: "m".to_string(),
                package_name: "P".to_string(),
                address: String::new(),
                required_imports: Vec::new(),
                is_native: false,
            },
        );
        let signature = Signature {
            type_params: Vec::new(),
            params: Vec::new(),
            return_type: Type::Unit,
        };
        program.natives.decls.insert(
            2,
            NativeDecl {
                module: 0,
                name: "f".to_string(),
                signature: signature.clone(),
                effects: Effects::PURE,
                explicit_pure: true,
                is_framework: false,
                spec_target: None,
                user_native: None,
            },
        );
        program.functions.insert(
            0,
            Function {
                module: 0,
                name: "caller".to_string(),
                signature,
                body: just(call(2, Vec::new())),
                kind: FunctionKind::Source,
                effects: Effects::PURE,
                explicit_pure: true,
            },
        );
        program
    }

    fn native_identity(
        package: &str,
        module: &str,
        function: &str,
        address: Option<&str>,
    ) -> NativeModelIdentity {
        NativeModelIdentity {
            fid: 2,
            native: format!("{package}::{module}::{function}"),
            package: package.into(),
            module: module.into(),
            function: function.into(),
            address: address.map(str::to_string),
            lean_model: function.into(),
        }
    }

    #[test]
    fn native_model_plan_preserves_manifest_schema_v1_bytes() {
        let plan = NativeModelPlan {
            rows: vec![NativeModelPlanRow {
                identity: native_identity("Sui", "coin", "mint", Some("0x2")),
                selected: SelectedModel::Candidate {
                    candidate: ModelCandidate {
                        model_file: "Sui/CoinNatives.lean".into(),
                        source_path: PathBuf::from("Sui/CoinNatives.lean"),
                        module: "Sui.CoinNatives".into(),
                        declaration: "Coin.mint".into(),
                        shipped_prover: false,
                        package_overlay: false,
                    },
                    observation: DeclarationObservation {
                        kind: crate::render::environment::DeclarationKind::Definition,
                        declared_in_expected_module: true,
                    },
                },
                decision: TrustDecision {
                    classification: ModelClassification::Trusted,
                    justification: "Reviewed shipped model.".into(),
                },
            }],
        };

        assert_eq!(
            plan.manifest(),
            concat!(
                "# Generated by lean-pipeline. Every native referenced by emitted IR is classified.\n",
                "# Schema v1 readers must ignore unknown model keys; declaration_* fields are additive evidence.\n",
                "version = 1\n",
                "\n[[model]]\n",
                "fid = 2\n",
                "native = \"Sui::coin::mint\"\n",
                "package = \"Sui\"\n",
                "module = \"coin\"\n",
                "function = \"mint\"\n",
                "address = \"0x2\"\n",
                "lean_model = \"mint\"\n",
                "model_file = \"Sui/CoinNatives.lean\"\n",
                "declaration_kind = \"def\"\n",
                "declaration_module_matches = true\n",
                "source = \"handwritten\"\n",
                "classification = \"trusted\"\n",
                "justification = \"Reviewed shipped model.\"\n",
            )
        );
    }

    #[test]
    fn native_model_plan_owns_mode_specific_rejection() {
        let row = NativeModelPlanRow {
            identity: native_identity("Sui", "test_scenario", "take_from_sender", Some("0x2")),
            selected: SelectedModel::Fixed(ModelSource::GeneratedTest),
            decision: TrustDecision {
                classification: ModelClassification::TestOnly,
                justification: "Test harness model.".into(),
            },
        };

        assert!(row.is_accepted(LoopMode::Test));
        assert!(row.is_accepted(LoopMode::Execution));
        assert!(!row.is_accepted(LoopMode::Proof));
        assert_eq!(
            row.rejection(LoopMode::Proof).as_deref(),
            Some("Sui::test_scenario::take_from_sender (test_only)")
        );
        assert_eq!(row.rejection(LoopMode::Test), None);
        assert_eq!(row.rejection(LoopMode::Execution), None);
    }

    #[test]
    fn shipped_framework_policy_requires_canonical_address() {
        let mut program = program_with_missing_native();
        let module = program.modules.get_mut(&0).unwrap();
        module.package_name = "Sui".into();
        module.name = "coin".into();
        module.address = "3".into();
        let identity = native_identity("Sui", "coin", "f", Some("0x3"));
        let rule = PolicyRule {
            package: "Sui".into(),
            module: "*".into(),
            function: "*".into(),
            address: None,
            source: ModelSource::Handwritten,
            classification: ModelClassification::Trusted,
            justification: "shipped policy".into(),
            package_local: false,
        };
        assert!(!policy_native_identity_matches(&program, &identity, &rule));
        program.modules.get_mut(&0).unwrap().address = "2".into();
        assert!(policy_native_identity_matches(&program, &identity, &rule));

        let module = program.modules.get_mut(&0).unwrap();
        module.package_name = "Prover".into();
        module.name = "prover".into();
        module.address = "1".into();
        let identity = native_identity("Prover", "prover", "f", Some("0x0"));
        assert!(!policy_native_identity_matches(&program, &identity, &rule));
        program.modules.get_mut(&0).unwrap().address = "0".into();
        assert!(policy_native_identity_matches(&program, &identity, &rule));
    }

    #[test]
    fn sui_system_policy_requires_canonical_address() {
        let mut program = program_with_missing_native();
        let module = program.modules.get_mut(&0).unwrap();
        module.package_name = "SuiSystem".into();
        module.name = "validator".into();
        module.address = "2".into();
        let identity = native_identity(
            "SuiSystem",
            "validator",
            "validate_metadata_bcs",
            Some("0x2"),
        );
        let policy = parse_policy(
            r#"
version = 1

[[rule]]
package = "SuiSystem"
module = "validator"
function = "validate_metadata_bcs"
address = "0x3"
source = "handwritten"
classification = "trusted"
justification = "Reviewed native model."
"#,
        );
        assert!(best_rule(
            &policy.rule,
            &identity.package,
            &identity.module,
            &identity.function,
            ModelSource::Handwritten,
        )
        .filter(|rule| policy_native_identity_matches(&program, &identity, rule))
        .is_none());
        program.modules.get_mut(&0).unwrap().address = "3".into();
        assert!(best_rule(
            &policy.rule,
            &identity.package,
            &identity.module,
            &identity.function,
            ModelSource::Handwritten,
        )
        .filter(|rule| policy_native_identity_matches(&program, &identity, rule))
        .is_some());
    }

    #[test]
    fn wrong_address_rule_cannot_shadow_a_matching_rule() {
        let mut program = program_with_missing_native();
        let module = program.modules.get_mut(&0).unwrap();
        module.package_name = "SuiSystem".into();
        module.name = "validator".into();
        module.address = "3".into();
        let identity = native_identity(
            "SuiSystem",
            "validator",
            "validate_metadata_bcs",
            Some("0x3"),
        );
        let mut policy = parse_policy(
            r#"
version = 1

[[rule]]
package = "SuiSystem"
module = "validator"
function = "validate_metadata_bcs"
address = "0x3"
source = "handwritten"
classification = "trusted"
justification = "Matching identity."

[[rule]]
package = "SuiSystem"
module = "validator"
function = "validate_metadata_bcs"
address = "0x4"
source = "handwritten"
classification = "test_only"
justification = "Different deployment."
"#,
        );
        validate_policy(Path::new("policy.toml"), &mut policy).unwrap();

        let matched = best_rule_with_filter(
            &policy.rule,
            &identity.package,
            &identity.module,
            &identity.function,
            ModelSource::Handwritten,
            |rule| policy_native_identity_matches(&program, &identity, rule),
        )
        .unwrap();
        assert_eq!(matched.address.as_deref(), Some("0x3"));
        assert_eq!(matched.classification, ModelClassification::Trusted);
    }

    #[test]
    fn shipped_policy_cannot_classify_a_project_overlay() {
        let mut program = program_with_missing_native();
        let module = program.modules.get_mut(&0).unwrap();
        module.package_name = "Sui".into();
        module.name = "new_native_module".into();
        module.address = "2".into();
        let identity = native_identity("Sui", "new_native_module", "f", Some("0x2"));
        let candidate = ModelCandidate {
            model_file: "Sui/New_native_moduleNatives.lean".into(),
            source_path: PathBuf::from("Sui/New_native_moduleNatives.lean"),
            module: "Sui.New_native_moduleNatives".into(),
            declaration: "New_native_module.f".into(),
            shipped_prover: false,
            package_overlay: true,
        };
        let policy = parse_policy(
            r#"
version = 1

[[rule]]
package = "Sui"
module = "*"
function = "*"
source = "handwritten"
classification = "trusted"
justification = "Shipped Sui model library."
"#,
        );

        let matched = best_rule_with_filter(
            &policy.rule,
            &identity.package,
            &identity.module,
            &identity.function,
            ModelSource::Handwritten,
            |rule| {
                policy_native_identity_matches(&program, &identity, rule)
                    && policy_origin_matches_model(rule, Some(&candidate))
            },
        );
        assert!(matched.is_none());
    }

    #[test]
    fn end_transaction_is_an_exact_generated_test_model() {
        let mut program = program_with_missing_native();
        let module = program.modules.get_mut(&0).unwrap();
        module.package_name = "Sui".into();
        module.name = "test_scenario".into();
        module.address = "2".into();
        let decl = program.natives.decls.get_mut(&2).unwrap();
        decl.name = "end_transaction".into();
        decl.user_native = Some(false);
        decl.effects = Effects::CONSERVATIVE;
        program.modules.insert(
            1,
            Module {
                name: "world".into(),
                package_name: "Prover".into(),
                address: "0".into(),
                required_imports: Vec::new(),
                is_native: true,
            },
        );
        program.structs.insert(
            10,
            Struct {
                module_id: 1,
                name: "World".into(),
                qualified_name: crate::stage_04_effects::WORLD_QUALIFIED_NAME.into(),
                type_params: Vec::new(),
                fields: Vec::new(),
                variants: None,
                is_native: true,
            },
        );
        program.structs.insert(
            11,
            Struct {
                module_id: 0,
                name: "TransactionEffects".into(),
                qualified_name: "Sui::test_scenario::TransactionEffects".into(),
                type_params: Vec::new(),
                fields: Vec::new(),
                variants: None,
                is_native: false,
            },
        );
        let decl = program.natives.decls.get_mut(&2).unwrap();
        decl.signature = Signature {
            type_params: Vec::new(),
            params: vec![crate::ir::Param {
                name: crate::stage_04_effects::common::WORLD_VAR.into(),
                var: crate::stage_04_effects::common::world_varid(),
                ty: Type::Struct {
                    struct_id: 10,
                    type_args: Vec::new(),
                },
            }],
            return_type: Type::Tuple(vec![
                Type::Struct {
                    struct_id: 11,
                    type_args: Vec::new(),
                },
                Type::Struct {
                    struct_id: 10,
                    type_args: Vec::new(),
                },
            ]),
        };

        assert!(is_renderer_owned_end_transaction_model(
            &program.natives.decls[&2],
            &program
        ));

        let test_output = tempfile::tempdir().unwrap();
        classify_and_write(
            &program,
            test_output.path(),
            None,
            None,
            Some("Sui"),
            None,
            LoopMode::Test,
            &HashSet::new(),
        )
        .unwrap();
        let manifest = fs::read_to_string(test_output.path().join(MANIFEST_FILE)).unwrap();
        assert!(manifest.contains("native = \"Sui::test_scenario::end_transaction\""));
        assert!(manifest.contains("source = \"generated_test\""));
        assert!(manifest.contains("classification = \"test_only\""));

        let proof_output = tempfile::tempdir().unwrap();
        let error = classify_and_write(
            &program,
            proof_output.path(),
            None,
            None,
            Some("Sui"),
            None,
            LoopMode::Proof,
            &HashSet::new(),
        )
        .unwrap_err();
        assert!(matches!(
            error,
            RenderError::NativeModelPolicy { what }
                if what.contains("Sui::test_scenario::end_transaction (test_only)")
        ));

        program.modules.get_mut(&0).unwrap().address = "3".into();
        assert!(!is_renderer_owned_end_transaction_model(
            &program.natives.decls[&2],
            &program
        ));
        program.modules.get_mut(&0).unwrap().address = "2".into();
        program
            .natives
            .decls
            .get_mut(&2)
            .unwrap()
            .signature
            .return_type = Type::Unit;
        assert!(!is_renderer_owned_end_transaction_model(
            &program.natives.decls[&2],
            &program
        ));
    }

    #[test]
    fn reserved_looking_native_without_exact_identity_has_no_model() {
        let mut program = program_with_missing_native();
        {
            let decl = program.natives.decls.get_mut(&2).unwrap();
            decl.name = "Mutation.uninit".to_string();
            decl.is_framework = true;
        }

        assert!(!is_intrinsic_decl(2, &program.natives.decls[&2], &program));
        let output = tempfile::tempdir().unwrap();
        let error = classify_and_write(
            &program,
            output.path(),
            None,
            None,
            Some("P"),
            None,
            LoopMode::Test,
            &HashSet::new(),
        )
        .unwrap_err();
        assert!(matches!(
            error,
            RenderError::NativeModelPolicy { what }
                if what.contains("P::m::Mutation.uninit (missing_model)")
        ));
        let manifest = fs::read_to_string(output.path().join(MANIFEST_FILE)).unwrap();
        assert!(manifest.contains("source = \"missing\""));
        assert!(manifest.contains("classification = \"missing_model\""));
        assert!(!manifest.contains("source = \"intrinsic\""));
    }

    #[test]
    fn exact_mutation_native_identity_is_intrinsic() {
        let mut program = program_with_missing_native();
        program.modules.insert(
            1,
            Module {
                name: "Prelude".to_string(),
                package_name: "Prelude".to_string(),
                address: String::new(),
                required_imports: Vec::new(),
                is_native: true,
            },
        );
        let decl = program.natives.decls.get_mut(&2).unwrap();
        decl.module = 1;
        decl.name = "Mutation.uninit".to_string();
        decl.signature = Signature {
            type_params: vec!["T".to_string()],
            params: vec![crate::ir::Param {
                name: "i".to_string(),
                var: "$t0".into(),
                ty: Type::UInt(64),
            }],
            return_type: Type::MutableRef {
                inner: Box::new(Type::TypeParam(0)),
                root: Box::new(Type::TypeParam(0)),
            },
        };
        decl.effects = Effects::PURE;
        decl.explicit_pure = false;
        decl.is_framework = true;

        assert!(is_intrinsic_decl(2, &program.natives.decls[&2], &program));
        let output = tempfile::tempdir().unwrap();
        classify_and_write(
            &program,
            output.path(),
            None,
            None,
            Some("P"),
            None,
            LoopMode::Proof,
            &HashSet::new(),
        )
        .unwrap();
        let manifest = fs::read_to_string(output.path().join(MANIFEST_FILE)).unwrap();
        assert!(manifest.contains("source = \"intrinsic\""));
        assert!(manifest.contains("classification = \"intrinsic\""));
    }

    #[test]
    fn generated_ghost_opaque_has_exact_auditable_trust_classification() {
        let mut program = program_with_missing_native();
        program
            .ghost_opaque_outputs
            .insert(0, vec![(Type::Unit, Type::Unit, 2)]);

        let rejected_output = tempfile::tempdir().unwrap();
        let err = classify_and_write(
            &program,
            rejected_output.path(),
            None,
            None,
            Some("P"),
            None,
            LoopMode::Proof,
            &HashSet::new(),
        )
        .unwrap_err();
        assert!(matches!(
            err,
            RenderError::NativeModelPolicy { what }
                if what.contains("P::m::f (missing_model)")
        ));

        program
            .trusted_spec_to_impl
            .insert(99, (0, crate::ir::TrustReason::NonProve));
        let unconstrained_output = tempfile::tempdir().unwrap();
        let err = classify_and_write(
            &program,
            unconstrained_output.path(),
            None,
            None,
            Some("P"),
            None,
            LoopMode::Proof,
            &HashSet::new(),
        )
        .unwrap_err();
        assert!(matches!(
            err,
            RenderError::NativeModelPolicy { what }
                if what.contains("P::m::f (missing_model)")
        ));

        let signature = program.functions[&0].signature.clone();
        program.functions.insert(
            99,
            Function {
                module: 0,
                name: "caller_spec".to_string(),
                signature: signature.clone(),
                body: just(crate::ir::Expr::Unit),
                kind: FunctionKind::Source,
                effects: Effects::PURE,
                explicit_pure: true,
            },
        );
        program.functions.insert(
            3,
            Function {
                module: 0,
                name: "caller_ghost_constraint".to_string(),
                signature,
                body: just(call(2, Vec::new())),
                kind: FunctionKind::Axiom {
                    target: 0,
                    source: 99,
                    reason: crate::ir::TrustReason::NonProve,
                },
                effects: Effects::PURE,
                explicit_pure: true,
            },
        );

        let output = tempfile::tempdir().unwrap();
        classify_and_write(
            &program,
            output.path(),
            None,
            None,
            Some("P"),
            None,
            LoopMode::Proof,
            &HashSet::new(),
        )
        .unwrap();
        let manifest = fs::read_to_string(output.path().join(MANIFEST_FILE)).unwrap();
        assert!(manifest.contains("source = \"generated_opaque\""));
        assert!(manifest.contains("classification = \"trusted_generated_opaque\""));
        assert!(manifest.contains("constrained by its trusted specification axiom"));
    }

    #[test]
    fn copied_sibling_becomes_an_exact_environment_query_candidate() {
        let output = tempfile::tempdir().unwrap();
        let package_dir = output.path().join("P");
        fs::create_dir_all(&package_dir).unwrap();
        let sibling = package_dir.join("MNatives.lean");
        fs::write(&sibling, "namespace P.M\ndef f : Unit := ()\nend P.M\n").unwrap();
        let copied = HashSet::from([sibling.clone()]);
        let candidate =
            model_candidate(output.path(), "P", "m", "f", "f", &copied, &HashSet::new())
                .unwrap()
                .unwrap();
        assert_eq!(candidate.model_file, "P/MNatives.lean");
        assert_eq!(candidate.module, "P.MNatives");
        assert_eq!(candidate.declaration, "P.M.f");
        assert!(!candidate.shipped_prover);
    }

    #[test]
    fn same_package_sibling_wins_over_movestdlib_mirror() {
        let output = tempfile::tempdir().unwrap();
        let sibling = output.path().join("P/MNatives.lean");
        let mirror = output.path().join("MoveStdlib/MNatives.lean");
        let available = HashSet::from([sibling.clone(), mirror]);

        let resolution =
            resolve_native_forward(output.path(), "P", "m", |path| available.contains(path))
                .unwrap();

        assert_eq!(resolution.path, sibling);
        assert_eq!(resolution.import, "P.MNatives");
    }

    #[test]
    fn unrelated_package_keeps_the_broad_movestdlib_mirror_fallback() {
        let output = tempfile::tempdir().unwrap();
        let mirror_dir = output.path().join("MoveStdlib");
        fs::create_dir_all(&mirror_dir).unwrap();
        let mirror = mirror_dir.join("BcsNatives.lean");
        fs::write(&mirror, "namespace Bcs\ndef f : Unit := ()\nend Bcs\n").unwrap();
        let copied = HashSet::from([mirror]);

        let candidate = model_candidate(
            output.path(),
            "Unrelated",
            "bcs",
            "f",
            "f",
            &copied,
            &HashSet::new(),
        )
        .unwrap()
        .unwrap();
        assert_eq!(candidate.model_file, "MoveStdlib/BcsNatives.lean");
        assert_eq!(candidate.module, "MoveStdlib.BcsNatives");
        assert_eq!(candidate.declaration, "Unrelated.Bcs.f");
        assert!(!candidate.shipped_prover);
    }

    fn prover_program(module: &str, function: &str) -> Program {
        let mut program = program_with_missing_native();
        let module_decl = program.modules.get_mut(&0).unwrap();
        module_decl.name = module.to_string();
        module_decl.package_name = "Prover".to_string();
        module_decl.address = "0".to_string();
        module_decl.is_native = true;
        let native = program.natives.decls.get_mut(&2).unwrap();
        native.name = function.to_string();
        native.is_framework = true;
        program
    }

    fn write_prover_project(output: &Path, prover: &str, vector_iter: &str) -> HashSet<PathBuf> {
        fs::write(
            output.join("lakefile.lean"),
            r#"import Lake
open Lake DSL
package native_model_test
lean_lib Prover where
  roots := #[`Prover]
  globs := #[.submodules `Prover]
"#,
        )
        .unwrap();
        let package_dir = output.join("Prover");
        fs::create_dir_all(&package_dir).unwrap();
        let prover_path = package_dir.join("Prover.lean");
        let vector_iter_path = package_dir.join("Vector_iter.lean");
        fs::write(&prover_path, prover).unwrap();
        fs::write(&vector_iter_path, vector_iter).unwrap();
        HashSet::from([prover_path, vector_iter_path])
    }

    fn manifest_model<'a>(manifest: &'a str, native: &str) -> &'a str {
        let marker = format!("native = \"{native}\"");
        manifest
            .split("[[model]]")
            .find(|model| model.contains(&marker))
            .unwrap()
    }

    #[test]
    fn exact_copied_prover_modules_become_environment_query_candidates() {
        let output = tempfile::tempdir().unwrap();
        let copied = write_prover_project(output.path(), "", "");
        for (module, function, model_file, query_module, declaration) in [
            (
                "prover",
                "asserts_of",
                "Prover/Prover.lean",
                "Prover.Prover",
                "Prover.asserts_of",
            ),
            (
                "vector_iter",
                "range",
                "Prover/Vector_iter.lean",
                "Prover.Vector_iter",
                "Vector_iter.range",
            ),
        ] {
            let candidate = model_candidate(
                output.path(),
                "Prover",
                module,
                function,
                function,
                &copied,
                &HashSet::new(),
            )
            .unwrap()
            .unwrap();
            assert_eq!(candidate.model_file, model_file);
            assert_eq!(candidate.module, query_module);
            assert_eq!(candidate.declaration, declaration);
            assert!(candidate.shipped_prover);
        }
    }

    #[test]
    fn elaborated_shipped_prover_definition_is_trusted() {
        for (module, function, source, model_file) in [
            (
                "prover",
                "asserts_of",
                "namespace Prover\ndef asserts_of : Unit := ()\nend Prover\n",
                "Prover/Prover.lean",
            ),
            (
                "vector_iter",
                "range",
                "namespace Vector_iter\ndef range : Unit := ()\nend Vector_iter\n",
                "Prover/Vector_iter.lean",
            ),
            (
                "vector_iter",
                "sum",
                "namespace Vector_iter\ndef sum : Unit := ()\nend Vector_iter\n",
                "Prover/Vector_iter.lean",
            ),
        ] {
            let program = prover_program(module, function);
            let output = tempfile::tempdir().unwrap();
            let (prover, vector_iter) = if module == "prover" {
                (source, "")
            } else {
                ("", source)
            };
            let copied = write_prover_project(output.path(), prover, vector_iter);

            classify_and_write(
                &program,
                output.path(),
                None,
                None,
                Some("P"),
                None,
                LoopMode::Proof,
                &copied,
            )
            .unwrap();

            let manifest = fs::read_to_string(output.path().join(MANIFEST_FILE)).unwrap();
            let model = manifest_model(&manifest, &format!("Prover::{module}::{function}"));
            assert!(model.contains(&format!("model_file = \"{model_file}\"")));
            assert!(model.contains("declaration_kind = \"def\""));
            assert!(model.contains("declaration_module_matches = true"));
            assert!(model.contains("source = \"handwritten\""));
            assert!(model.contains("classification = \"trusted\""));
            assert!(model.contains("shipped Prover native model"));
        }
    }

    #[test]
    fn shipped_prover_auto_trust_rejects_spoofed_decl_identity() {
        for mutation in [
            "nonframework",
            "user-native",
            "unknown-function",
            "wrong-address",
        ] {
            let mut program = prover_program("prover", "asserts_of");
            let source = match mutation {
                "nonframework" => {
                    program.natives.decls.get_mut(&2).unwrap().is_framework = false;
                    "namespace Prover\ndef asserts_of : Unit := ()\nend Prover\n"
                }
                "user-native" => {
                    program.natives.decls.get_mut(&2).unwrap().user_native = Some(true);
                    "namespace Prover\ndef asserts_of : Unit := ()\nend Prover\n"
                }
                "unknown-function" => {
                    program.natives.decls.get_mut(&2).unwrap().name = "spoofed".into();
                    "namespace Prover\ndef spoofed : Unit := ()\nend Prover\n"
                }
                "wrong-address" => {
                    program.modules.get_mut(&0).unwrap().address = "1".into();
                    "namespace Prover\ndef asserts_of : Unit := ()\nend Prover\n"
                }
                _ => unreachable!(),
            };
            let output = tempfile::tempdir().unwrap();
            let copied = write_prover_project(output.path(), source, "");
            let error = classify_and_write(
                &program,
                output.path(),
                None,
                None,
                Some("P"),
                None,
                LoopMode::Proof,
                &copied,
            )
            .unwrap_err();
            assert!(matches!(
                error,
                RenderError::NativeModelPolicy { what } if what.contains("(unclassified)")
            ));
        }
    }

    #[test]
    fn imported_prover_definition_is_rejected() {
        let program = prover_program("prover", "asserts_of");
        let output = tempfile::tempdir().unwrap();
        let copied = write_prover_project(output.path(), "import Prover.Foreign\n", "");
        fs::write(
            output.path().join("Prover/Foreign.lean"),
            "namespace Prover\ndef asserts_of : Unit := ()\nend Prover\n",
        )
        .unwrap();

        let error = classify_and_write(
            &program,
            output.path(),
            None,
            None,
            Some("P"),
            None,
            LoopMode::Proof,
            &copied,
        )
        .unwrap_err();
        assert!(matches!(
            error,
            RenderError::NativeModelPolicy { what }
                if what.contains("Prover::prover::asserts_of (missing_model)")
        ));
        let manifest = fs::read_to_string(output.path().join(MANIFEST_FILE)).unwrap();
        let model = manifest_model(&manifest, "Prover::prover::asserts_of");
        assert!(model.contains("declaration_kind = \"def\""));
        assert!(model.contains("declaration_module_matches = false"));
        assert!(model.contains("source = \"missing\""));
        assert!(model.contains("classification = \"missing_model\""));
    }

    #[test]
    fn nonconcrete_prover_declaration_is_rejected() {
        let program = prover_program("prover", "asserts_of");
        let output = tempfile::tempdir().unwrap();
        let copied = write_prover_project(
            output.path(),
            "namespace Prover\naxiom asserts_of : Unit\nend Prover\n",
            "",
        );

        let error = classify_and_write(
            &program,
            output.path(),
            None,
            None,
            Some("P"),
            None,
            LoopMode::Proof,
            &copied,
        )
        .unwrap_err();
        assert!(matches!(
            error,
            RenderError::NativeModelPolicy { what }
                if what.contains("Prover::prover::asserts_of (missing_model)")
        ));
        let manifest = fs::read_to_string(output.path().join(MANIFEST_FILE)).unwrap();
        let model = manifest_model(&manifest, "Prover::prover::asserts_of");
        assert!(model.contains("declaration_kind = \"axiom\""));
        assert!(model.contains("declaration_module_matches = true"));
        assert!(model.contains("source = \"missing\""));
        assert!(model.contains("classification = \"missing_model\""));
    }

    fn copied_user_native_model(output: &Path, declaration: &str) -> HashSet<PathBuf> {
        fs::write(
            output.join("lakefile.lean"),
            "import Lake\nopen Lake DSL\npackage native_model_test\nlean_lib P\n",
        )
        .unwrap();
        let package_dir = output.join("P");
        fs::create_dir_all(&package_dir).unwrap();
        let model = package_dir.join("MNatives.lean");
        fs::write(&model, format!("namespace P.M\n{declaration}\nend P.M\n")).unwrap();
        HashSet::from([model])
    }

    #[test]
    fn root_spec_native_definition_is_accepted_without_policy() {
        let mut program = program_with_missing_native();
        program.natives.decls.get_mut(&2).unwrap().user_native = Some(true);
        let output = tempfile::tempdir().unwrap();
        let copied = copied_user_native_model(output.path(), "def f : Unit := ()");

        classify_and_write(
            &program,
            output.path(),
            None,
            None,
            Some("P"),
            Some("P"),
            LoopMode::Proof,
            &copied,
        )
        .unwrap();

        let manifest = fs::read_to_string(output.path().join(MANIFEST_FILE)).unwrap();
        assert!(manifest.contains("native = \"P::m::f\""));
        assert!(manifest.contains("model_file = \"P/MNatives.lean\""));
        assert!(manifest.contains("source = \"handwritten\""));
        assert!(manifest.contains("classification = \"modeled_spec_native\""));
        assert!(manifest.contains("root-package spec-only native"));
    }

    #[test]
    fn root_spec_native_cannot_auto_trust_a_non_overlay_model() {
        let mut program = program_with_missing_native();
        program.natives.decls.get_mut(&2).unwrap().user_native = Some(true);
        let output = tempfile::tempdir().unwrap();
        let copied = copied_user_native_model(output.path(), "def f : Unit := ()");

        let error = classify_and_write_with_overlays(
            &program,
            output.path(),
            None,
            None,
            Some("P"),
            Some("P"),
            LoopMode::Proof,
            &copied,
            &HashSet::new(),
        )
        .unwrap_err();

        assert!(matches!(
            error,
            RenderError::NativeModelPolicy { what } if what.contains("P::m::f (unclassified)")
        ));
    }

    #[test]
    fn automatic_spec_native_classification_stays_fail_closed() {
        for (spec_only, root_package, declaration, rejected_classification) in [
            (false, Some("P"), "def f : Unit := ()", "unclassified"),
            (true, Some("Other"), "def f : Unit := ()", "unclassified"),
            (true, Some("P"), "axiom f : Unit", "unclassified"),
            (
                true,
                Some("P"),
                "structure f where\n  value : Nat",
                "missing_model",
            ),
            (true, Some("P"), "def other : Unit := ()", "missing_model"),
        ] {
            let mut program = program_with_missing_native();
            program.natives.decls.get_mut(&2).unwrap().user_native = Some(spec_only);
            let output = tempfile::tempdir().unwrap();
            let copied = copied_user_native_model(output.path(), declaration);

            let error = classify_and_write(
                &program,
                output.path(),
                None,
                None,
                Some("P"),
                root_package,
                LoopMode::Proof,
                &copied,
            )
            .unwrap_err();
            assert!(matches!(
                error,
                RenderError::NativeModelPolicy { what }
                    if what.contains(&format!("P::m::f ({rejected_classification})"))
            ));
        }
    }

    #[test]
    fn exact_policy_can_still_trust_a_handwritten_axiom() {
        let mut program = program_with_missing_native();
        program.modules.get_mut(&0).unwrap().address = "42".into();
        let output = tempfile::tempdir().unwrap();
        let copied = copied_user_native_model(output.path(), "axiom f : Unit");
        let policy_dir = tempfile::tempdir().unwrap();
        fs::write(
            policy_dir.path().join(POLICY_FILE),
            r#"
version = 1

[[rule]]
package = "P"
module = "m"
function = "f"
address = "0x42"
source = "handwritten"
classification = "trusted"
justification = "This exact axiom is an explicitly reviewed trust boundary."
"#,
        )
        .unwrap();

        classify_and_write(
            &program,
            output.path(),
            None,
            Some(policy_dir.path()),
            Some("P"),
            Some("P"),
            LoopMode::Proof,
            &copied,
        )
        .unwrap();

        let manifest = fs::read_to_string(output.path().join(MANIFEST_FILE)).unwrap();
        assert!(manifest.contains("declaration_kind = \"axiom\""));
        assert!(manifest.contains("declaration_module_matches = true"));
        assert!(manifest.contains("source = \"handwritten\""));
        assert!(manifest.contains("classification = \"trusted\""));
    }

    #[test]
    fn spec_native_needs_a_current_model_and_respects_test_only_policy() {
        let mut program = program_with_missing_native();
        program.natives.decls.get_mut(&2).unwrap().user_native = Some(true);
        program.modules.get_mut(&0).unwrap().address = "42".into();

        let missing_output = tempfile::tempdir().unwrap();
        let error = classify_and_write(
            &program,
            missing_output.path(),
            None,
            None,
            Some("P"),
            Some("P"),
            LoopMode::Proof,
            &HashSet::new(),
        )
        .unwrap_err();
        assert!(matches!(
            error,
            RenderError::NativeModelPolicy { what }
                if what.contains("P::m::f (missing_model)")
        ));

        let output = tempfile::tempdir().unwrap();
        let copied = copied_user_native_model(output.path(), "def f : Unit := ()");
        let policy_dir = tempfile::tempdir().unwrap();
        fs::write(
            policy_dir.path().join(POLICY_FILE),
            r#"
version = 1

[[rule]]
package = "P"
module = "m"
function = "f"
address = "0x42"
source = "handwritten"
classification = "test_only"
justification = "This model is executable test vocabulary only."
"#,
        )
        .unwrap();
        let error = classify_and_write(
            &program,
            output.path(),
            None,
            Some(policy_dir.path()),
            Some("P"),
            Some("P"),
            LoopMode::Proof,
            &copied,
        )
        .unwrap_err();
        assert!(matches!(
            error,
            RenderError::NativeModelPolicy { what }
                if what.contains("P::m::f (test_only)")
        ));
    }

    #[test]
    fn missing_model_policy_override_is_rejected() {
        let mut policy = parse_policy(
            r#"
version = 1

[[rule]]
package = "P"
module = "m"
function = "f"
source = "missing"
classification = "trusted"
justification = "Missing implementations cannot be trusted into existence."
"#,
        );
        let error = validate_policy(Path::new("policy.toml"), &mut policy).unwrap_err();
        assert!(matches!(
            error,
            RenderError::NativeModelPolicy { what } if what.contains("cannot reclassify source missing")
        ));
    }

    #[test]
    fn downstream_handwritten_trust_must_name_one_exact_native() {
        let dir = tempfile::tempdir().unwrap();
        fs::write(
            dir.path().join(POLICY_FILE),
            r#"
version = 1

[[rule]]
package = "P"
module = "m"
function = "*"
source = "handwritten"
classification = "trusted"
justification = "Too broad for a package-local trust override."
"#,
        )
        .unwrap();
        let error = load_policy(&dir.path().join(POLICY_FILE), &mut Vec::new(), false).unwrap_err();
        assert!(matches!(
            error,
            RenderError::NativeModelPolicy { what }
                if what.contains("downstream trust with a wildcard")
        ));
    }

    #[test]
    fn package_local_native_policy_must_pin_an_address() {
        let dir = tempfile::tempdir().unwrap();
        fs::write(
            dir.path().join(POLICY_FILE),
            r#"
version = 1

[[rule]]
package = "P"
module = "m"
function = "f"
source = "handwritten"
classification = "trusted"
justification = "Exact name without an address is not an exact Move identity."
"#,
        )
        .unwrap();
        let error = load_policy(&dir.path().join(POLICY_FILE), &mut Vec::new(), false).unwrap_err();
        assert!(matches!(
            error,
            RenderError::NativeModelPolicy { what }
                if what.contains("must pin the native module address")
        ));
    }

    #[test]
    fn blank_justification_is_rejected() {
        let mut policy = parse_policy(
            r#"
version = 1

[[rule]]
package = "Sui"
module = "*"
function = "*"
source = "handwritten"
classification = "trusted"
justification = "   "
"#,
        );
        let error = validate_policy(Path::new("policy.toml"), &mut policy).unwrap_err();
        assert!(matches!(
            error,
            RenderError::NativeModelPolicy { what } if what.contains("blank justification")
        ));
    }

    #[test]
    fn exact_rule_overrides_a_broader_migration_rule() {
        let mut policy = parse_policy(
            r#"
version = 1

[[rule]]
package = "Sui"
module = "*"
function = "*"
source = "handwritten"
classification = "trusted"
justification = "Migration trust."

[[rule]]
package = "Sui"
module = "test_scenario"
function = "take_from_sender"
source = "handwritten"
classification = "test_only"
justification = "Test harness model."
"#,
        );
        validate_policy(Path::new("policy.toml"), &mut policy).unwrap();
        let rule = best_rule(
            &policy.rule,
            "Sui",
            "test_scenario",
            "take_from_sender",
            ModelSource::Handwritten,
        )
        .unwrap();
        assert_eq!(rule.classification, ModelClassification::TestOnly);
    }

    #[test]
    fn test_only_denials_cannot_be_overridden_by_downstream_trust() {
        let mut policy = parse_policy(
            r#"
version = 1

[[rule]]
package = "Sui"
module = "test_scenario"
function = "*"
source = "handwritten"
classification = "test_only"
justification = "Test harness model."

[[rule]]
package = "Sui"
module = "test_scenario"
function = "take_from_sender"
source = "handwritten"
classification = "trusted"
justification = "Downstream attempted promotion."
"#,
        );
        validate_policy(Path::new("policy.toml"), &mut policy).unwrap();
        let rule = best_rule(
            &policy.rule,
            "Sui",
            "test_scenario",
            "take_from_sender",
            ModelSource::Handwritten,
        )
        .unwrap();
        assert_eq!(rule.classification, ModelClassification::TestOnly);
    }

    fn shipped_policy_rules() -> Vec<PolicyRule> {
        let path = Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("lemmas")
            .join(POLICY_FILE);
        assert!(
            path.is_file(),
            "shipped native-model policy missing at {}",
            path.display()
        );
        let mut rules = Vec::new();
        load_policy(&path, &mut rules, true).unwrap();
        rules
    }

    /// A plan row whose classification comes from the SHIPPED policy file,
    /// for a framework native with an elaborated handwritten model at its
    /// canonical address. Deliberately not a package overlay: an overlay
    /// candidate can never match a shipped rule.
    fn shipped_policy_row(
        package: &str,
        module: &str,
        function: &str,
        address: &str,
    ) -> NativeModelPlanRow {
        let mut program = program_with_missing_native();
        let declared = program.modules.get_mut(&0).unwrap();
        declared.package_name = package.to_string();
        declared.name = module.to_string();
        declared.address = address.trim_start_matches("0x").to_string();
        let decl = program.natives.decls.get_mut(&2).unwrap();
        decl.name = function.to_string();
        decl.is_framework = true;

        let identity = native_identity(package, module, function, Some(address));
        let namespace = crate::render::escape::module_render_namespace(package, module);
        let file_stem = crate::render::escape::module_name_to_namespace(module);
        let model_file = format!("{package}/{file_stem}Natives.lean");
        let selected = SelectedModel::Candidate {
            candidate: ModelCandidate {
                module: format!("{package}.{file_stem}Natives"),
                declaration: format!(
                    "{}.{}",
                    normalize_lean_name(&namespace),
                    normalize_lean_name(function)
                ),
                source_path: PathBuf::from(&model_file),
                model_file,
                shipped_prover: false,
                package_overlay: false,
            },
            observation: DeclarationObservation {
                kind: crate::render::environment::DeclarationKind::Definition,
                declared_in_expected_module: true,
            },
        };
        let decision = trust_decision(
            &program,
            &shipped_policy_rules(),
            None,
            &identity,
            &selected,
        );
        NativeModelPlanRow {
            identity,
            selected,
            decision,
        }
    }

    /// The gate must keep biting for a native a USER package can genuinely
    /// reach. Every row here is a shipped model an ordinary client calls
    /// (`test_scenario` / `unit_test` / `test_utils` appear in real test
    /// code), classified straight out of `lemmas/native_model_policy.toml`
    /// with its broad `Sui`/`MoveStdlib` migration-trust wildcards loaded
    /// alongside -- so this also pins that a `test_only` denial still wins
    /// over them. "Securitize is green" is not evidence for any of this.
    #[test]
    fn shipped_policy_keeps_the_proof_gate_armed_for_test_harness_models() {
        let output = tempfile::tempdir().unwrap();
        for (package, module, function, address) in [
            ("Sui", "test_scenario", "return_shared", "0x2"),
            ("Sui", "test_scenario", "return_to_address", "0x2"),
            ("Sui", "test_utils", "create_one_time_witness", "0x2"),
            ("MoveStdlib", "unit_test", "poison", "0x1"),
        ] {
            let row = shipped_policy_row(package, module, function, address);
            assert_eq!(
                row.decision.classification,
                ModelClassification::TestOnly,
                "shipped policy stopped denying {package}::{module}::{function}"
            );
            assert!(row.is_accepted(LoopMode::Test));
            assert!(!row.is_accepted(LoopMode::Proof));

            let plan = NativeModelPlan { rows: vec![row] };
            plan.enforce(output.path(), LoopMode::Test).unwrap();
            let error = plan.enforce(output.path(), LoopMode::Proof).unwrap_err();
            assert!(matches!(
                error,
                RenderError::NativeModelPolicy { what }
                    if what.contains(&format!("{package}::{module}::{function} (test_only)"))
            ));
        }
    }

    /// `sui::accumulator::emit_{deposit,withdraw}_event` are trusted on an
    /// exact rule, not on the broad `Sui` migration wildcard: the VM native
    /// appends to `accumulator_events`, never to the user-event vector
    /// `num_user_events` counts, so the identity model is the faithful one.
    /// The justification is asserted because falling through to the
    /// migration wildcard would silently trust them for the wrong reason.
    #[test]
    fn shipped_policy_trusts_the_accumulator_event_emitters_on_an_exact_rule() {
        let output = tempfile::tempdir().unwrap();
        for function in ["emit_deposit_event", "emit_withdraw_event"] {
            let row = shipped_policy_row("Sui", "accumulator", function, "0x2");
            assert_eq!(row.decision.classification, ModelClassification::Trusted);
            assert!(
                row.decision.justification.contains("accumulator_events"),
                "{function} is trusted by the broad migration wildcard, not by its own \
                 evidence-bearing rule: {}",
                row.decision.justification
            );
            assert!(row.is_accepted(LoopMode::Proof));
            NativeModelPlan { rows: vec![row] }
                .enforce(output.path(), LoopMode::Proof)
                .unwrap();
        }
    }

    #[test]
    fn proof_and_test_reject_missing_native_models() {
        let program = program_with_missing_native();
        let proof_output = tempfile::tempdir().unwrap();
        let error = classify_and_write(
            &program,
            proof_output.path(),
            None,
            None,
            None,
            None,
            LoopMode::Proof,
            &HashSet::new(),
        )
        .unwrap_err();
        assert!(matches!(
            error,
            RenderError::NativeModelPolicy { what }
                if what.contains("P::m::f (missing_model)")
        ));
        let manifest = fs::read_to_string(proof_output.path().join(MANIFEST_FILE)).unwrap();
        assert!(manifest.contains("classification = \"missing_model\""));

        let test_output = tempfile::tempdir().unwrap();
        let error = classify_and_write(
            &program,
            test_output.path(),
            None,
            None,
            None,
            None,
            LoopMode::Test,
            &HashSet::new(),
        )
        .unwrap_err();
        assert!(matches!(
            error,
            RenderError::NativeModelPolicy { what }
                if what.contains("P::m::f (missing_model)")
        ));
        let manifest = fs::read_to_string(test_output.path().join(MANIFEST_FILE)).unwrap();
        assert!(manifest.contains("classification = \"missing_model\""));
    }
}
