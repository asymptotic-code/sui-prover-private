//! `--audit-proofs`: post-build axiom + statement audit of every stage-12
//! obligation.
//!
//! Joins the generated `obligations.toml` manifest against the BUILT Lean
//! environment: a generated, isolated Lean query loads each freshly built
//! target OLean with `Lean.withImportModules` and collects each obligation
//! declaration's transitive axiom footprint
//! (`Lean.collectAxioms`) AND compares the declaration's TYPE against the
//! obligation prop's eta-expected statement (`forall xs, <prop> xs` built
//! from the prop def's own telescope), and the Rust side classifies each
//! obligation:
//!
//! * `proven`  -- the statement matches exactly (`isDefEq` against the
//!   eta-expected statement) and every axiom in the footprint is expected:
//!   Lean's own
//!   (`propext`, `Classical.choice`, `Quot.sound`, `Lean.ofReduceBool`,
//!   `Lean.trustCompiler`); a `native_decide` synthetic, recognised by
//!   its `@Eq Bool _ Bool.true` TYPE (read from the real Environment), its
//!   exact compiler name shape, and a source scan that rejects any
//!   hand-authored axiom under that namespace; a manifest-declared trusted
//!   axiom matched as a (name, declaring-module) PAIR; or an axiom shipped
//!   in the trusted lemma base (declared under a `Prelude` / `Sui` /
//!   `MoveStdlib` / `Prover` / `Generated` module that is NOT shadowed by
//!   a file in the package's own overlay).
//!
//! Trust is keyed on facts the metaprogram reads from the built
//! Environment (axiom type shape, declaring module, the module the
//! obligation decl itself resolves in) plus a complete source-tree scan
//! at the few compiler-name trust boundaries. A hand-declared axiom cannot
//! be trusted by mimicking a compiler/lemma-lib name. The protocol channel is guarded
//! three ways: a per-run nonce prefix, a mandatory completion sentinel,
//! and a trusted query file that imports only bundled `Lean` before
//! loading proof OLeans as data. `scan_overlay_for_import_time_execution`
//! additionally rejects proof initializers at this trust boundary.
//! Audit subprocesses clear ambient Lean selector/search/sysroot/githash
//! overrides and disable Lake artifact caches. The isolated query uses the
//! absolute Lake and Lean executables selected by the output project's
//! toolchain.
//! The proof overlay is snapshotted before the build and rechecked after
//! all environment queries. A persistent concurrent source change fails
//! the audit; the retained overlay lock coordinates pipeline writers.
//!
//! * `conditional` -- the proof declaration's conclusion IS the obligation
//!   prop (applied to an in-order subset of the proof's binders), but the
//!   proof carries EXTRA hypotheses beyond the prop's own telescope. The
//!   obligation is only proven under those side conditions; they are
//!   listed in `proof_status.toml` as `extra_hypotheses`. Non-fatal by
//!   default; `--audit-strict-statements` makes it fatal.
//! * `statement_mismatch` -- the proof declaration's type neither matches
//!   the eta-expected statement nor concludes the prop at all (renamed /
//!   repurposed / specialized declaration): an integrity failure, fatal
//!   like `suspicious`.
//! * `statement_unverified` -- the statement check itself did not complete
//!   (deterministic timeout or any other elaboration error) inside the
//!   budget the metaprogram rebases on every obligation. The audit does not
//!   know whether the statement matches, so it never passes: fatal like
//!   `statement_mismatch`, with the Lean error kept as `statement_note`.
//!   Isolating the budget per obligation is what keeps ONE expensive
//!   statement from aborting the whole run and suppressing the report.
//! * `trusted` -- the obligation IS a manifest trusted axiom: assumed by
//!   design; the audit verifies the declaration exists and that its
//!   declared type matches the prop's eta-expected statement exactly
//!   (both are generator-emitted, so any deviation is drift ->
//!   `statement_mismatch`).
//! * `sorry`   -- the footprint contains `sorryAx` (an unproven or
//!   partially-proven obligation, including sorries pulled in
//!   TRANSITIVELY through helper lemmas in other files -- the case a
//!   build-log grep cannot see).
//! * `declared` -- proven modulo axioms the package EXPLICITLY declares
//!   in `<package-root>/lean/trusted_axioms.toml` (committed next to the
//!   proofs; every entry carries a mandatory justification). This is how
//!   deliberate proof-side assumptions (e.g. a totality lemma awaiting a
//!   renderer fix) stay visible and reviewable instead of implicit.
//! * `smt_trusted` -- the exact vendored lean-auto `autoSMTSorry` axiom,
//!   declared in `Auto.Solver.SMT`, appears in the footprint. This records
//!   use of the controlled MoveAuto Z3 path, not a reconstructed kernel
//!   proof. Every transitive oracle occurrence must sit beneath the query
//!   and explicit-call markers. The dependency paths, vendored and local
//!   source closures, no-download patch, and absence of source shadows are
//!   checked before this classification is available.
//! * `missing` -- the manifest names a declaration the environment lacks
//!   (deleted proof, renamed obligation): an integrity failure.
//! * `suspicious` -- a declaration with the wrong kind or module, or any
//!   footprint axiom outside all of the above (e.g. an `axiom` smuggled
//!   into a proofs file): an integrity failure.
//!
//! Status precedence per obligation: `missing` >
//! wrong-module/wrong-kind/unexpected-axiom `suspicious` >
//! `statement_mismatch` > `statement_unverified` > `sorry` > `conditional` > `declared` >
//! `smt_trusted` > `proven`
//! -- so a conditional proof containing `sorryAx` reports as `sorry` (the
//! axiom classification stays orthogonal), and a statement problem never
//! hides a smuggled axiom.
//!
//! Writes `proof_status.toml` next to the manifest and returns a
//! summary; the caller fails the run on integrity failures or sorries
//! (the report file carries the detail either way). Unused
//! `trusted_axioms.toml` entries are warned about so the allowlist
//! cannot silently accumulate stale trust.
//!
//! # Artifact provenance: cached by default, clean-room on request
//!
//! Everything above -- every classification, every scan, every protocol
//! guard -- runs identically regardless of where the OLeans came from.
//! `AuditMode` selects only that: who compiled them.
//!
//! By default (`AuditMode::Cached`) the audit skips any reconstruction: it
//! brings the project's OWN build up to date with an incremental
//! `lake build --rehash` and audits that. There is no isolated copy, no
//! content key and no separate store -- "cache" here means the OLeans your
//! build already produced.
//!
//! That build step is mandatory, not a formality: without it, editing a proof
//! and forgetting to rebuild would read as green off a stale OLean, which is
//! the stale-artifact trap in its purest form. `--rehash` is what keeps the
//! staleness check content-based rather than mtime-based.
//!
//! `--audit-clean-room` (`AuditMode::CleanRoom`) instead copies the generated
//! project and the vendored automation layer into a throwaway directory
//! WITHOUT any `.lake`, and rebuilds from cold under `--no-cache`. Retained
//! OLeans are not trusted at all; the audit produces its own.
//!
//! The trade is stated plainly: the cached default trusts Lake's incremental
//! correctness, which is exactly what clean-room refuses to trust. It answers
//! *"do my proofs discharge the obligations, assuming the build is current"*,
//! and does not answer *"is this corpus verified"* off a warm cache -- though
//! it does whenever the build cannot be stale (a fresh CI runner has no prior
//! build to trust, so there cached and clean-room coincide). Policy: cached is
//! the default; reach for clean-room to quote a result as verification off a
//! warm local cache. The mode is written into `proof_status.toml` as
//! `audit_mode` and printed inside the summary line as `proof audit [cached]:`
//! / `proof audit [clean-room]:`, because that line is what gets quoted into
//! commit messages and reports.
//!
//! # Concurrency
//!
//! Both per-group loops (elaboration, environment query) fan out under a
//! bound taken from `SUI_LEAN_AUDIT_ELABORATION_JOBS` /
//! `SUI_LEAN_AUDIT_QUERY_JOBS` (default 3). The bound exists for MEMORY, not
//! throughput: a single query holds ~3.6-3.8 GB RSS even on the smallest
//! sui-system group. Groups are mutually independent -- separate processes,
//! separate scratch dirs, separate nonces, joined afterwards on
//! `(group import, lean_decl)` -- so completion order carries no meaning.
//! Per-phase `[timing]` lines are printed for each elaboration, each query,
//! and the audit as a whole.

use std::collections::{BTreeMap, BTreeSet};
use std::ffi::OsStr;
use std::path::{Path, PathBuf};
use std::time::Instant;

use anyhow::Context;
use futures::stream::StreamExt;
use futures::stream::TryStreamExt;
use sha2::{Digest, Sha256};

/// Lean core's own axioms plus the two `native_decide` introduces. Any
/// other axiom must be justified by the manifest or the lemma base.
const LEAN_CORE_AXIOMS: [&str; 5] = [
    "propext",
    "Classical.choice",
    "Quot.sound",
    "Lean.ofReduceBool",
    "Lean.trustCompiler",
];

/// Module roots of the shipped trusted base (`lemmas/` copies + the
/// generated universe files). An axiom DECLARED under one of these is
/// part of the model's trust surface, reviewed with the lemma files.
/// Axioms declared anywhere else -- notably the `SourceProofs` overlay
/// (proof files, `Proofs.*` helpers, `Termination.*`) -- are suspicious.
const TRUSTED_LIB_ROOTS: [&str; 5] = ["Prelude", "Sui", "MoveStdlib", "Prover", "Generated"];
const SMT_TRUSTED_AXIOM: &str = "autoSMTSorry";
const SMT_TRUSTED_MODULE: &str = "Auto.Solver.SMT";
const SMT_ORACLE_MARKER: &str = "Prover.MoveAuto.z3OracleResult";
const SMT_EXPLICIT_MARKER: &str = "Prover.MoveAuto.explicitZ3OracleResult";
const RESERVED_LEAN_MODULE_ROOTS: [&str; 7] =
    ["Aesop", "Auto", "Batteries", "Init", "Lake", "Lean", "Std"];
// `LEMMA_BUNDLE_FILES`: every file of the Lean model bundle
// (`lean-pipeline/lemmas/`) as `(bundle-relative path, bytes)`, embedded by
// `build.rs` at compile time. This is the binary's MODEL half of the
// world-threading contract; the renderer is its EMISSION half. A binary paired
// with a bundle from a different checkout emits calls the model cannot type,
// which is what `--audit-proofs` bundle verification exists to catch.
include!(concat!(env!("OUT_DIR"), "/lemma_bundle.rs"));

/// Directories `build.rs` refuses to embed and the audit therefore does not
/// report as unpinned: build output and version control. `vendor/` is a
/// separate trust surface, pinned by `dependency_source_digest`.
const UNBUNDLED_DIRS: [&str; 3] = [".git", ".lake", "vendor"];

/// The subset the generated output carries verbatim, as
/// `(bundle-relative, output-relative)`. `natives/<lib>/` is promoted to a
/// top-level `<lib>/` on the way out, so the two halves differ.
const PINNED_OUTPUT_SOURCES: [(&str, &str); 5] = [
    ("natives/Prover/MoveAuto.lean", "Prover/MoveAuto.lean"),
    (
        "natives/Prover/MoveAutoAttr.lean",
        "Prover/MoveAutoAttr.lean",
    ),
    ("Prelude/Mutation.lean", "Prelude/Mutation.lean"),
    ("Prelude/Helpers.lean", "Prelude/Helpers.lean"),
    ("Prelude/BoundedNat.lean", "Prelude/BoundedNat.lean"),
];
const AUTOMATION_DEPENDENCIES: [(&str, &str, &str, &str); 3] = [
    (
        "batteries",
        "batteries",
        "lakefile.toml",
        "89cee974f9d29c2d69ae06213486eb6bfb22759c8d59d4a24baffcd2e2dfb720",
    ),
    (
        "aesop",
        "aesop",
        "lakefile.toml",
        "dd0cbd5eeded70f9d95998a48fa906a3460f8b40cd8d7b21a15503af756bf09f",
    ),
    (
        "auto",
        "lean-auto",
        "lakefile.lean",
        "987229cd4ff1f32413ed9b903bcacaa19b560b89768bbbc7acb6ba6e40fcf19d",
    ),
];

#[derive(Debug, serde::Deserialize)]
struct Manifest {
    #[serde(default)]
    obligation: Vec<Obligation>,
    /// Declared `#[spec(prove)]` wrappers that emitted NO obligation.
    /// Not a per-obligation row -- there is no declaration to classify --
    /// so it is carried straight through to the `spec_no_obligation`
    /// counter. `#[serde(default)]`: manifests rendered before the field
    /// existed read back as an empty list, which is honest (an older
    /// renderer could not have measured it) rather than a fabricated 0.
    #[serde(default)]
    spec_no_obligation: Vec<SpecNoObligation>,
}

#[derive(Debug, serde::Deserialize)]
struct SpecNoObligation {
    source: String,
    #[serde(default)]
    reason: Option<String>,
}

#[derive(Debug, serde::Deserialize)]
struct Obligation {
    name: String,
    ir_name: String,
    kind: String,
    #[serde(default)]
    reason: Option<String>,
    module: String,
    prop: String,
    lean_decl: String,
    #[allow(dead_code)]
    target: String,
    target_source: String,
    source: String,
}

#[derive(Debug, serde::Deserialize)]
struct ExpectedManifest {
    version: u32,
    #[serde(default)]
    expected: Vec<ExpectedSource>,
}

#[derive(Debug, serde::Deserialize)]
struct ExpectedSource {
    source: String,
    target: String,
    kind: String,
    #[serde(default)]
    reason: Option<String>,
    #[serde(default)]
    obligations: Vec<String>,
}

#[derive(Debug, serde::Deserialize)]
struct DeclaredAxioms {
    #[serde(default)]
    axiom: Vec<DeclaredAxiom>,
}

#[derive(Debug, serde::Deserialize)]
struct DeclaredAxiom {
    name: String,
    justification: String,
}

#[derive(Debug, Default)]
pub struct AuditSummary {
    pub proven: usize,
    pub conditional: usize,
    pub declared: usize,
    pub trusted: usize,
    pub smt_trusted: usize,
    pub sorry: usize,
    pub suspicious: usize,
    pub missing: usize,
    pub statement_mismatch: usize,
    pub statement_unverified: usize,
    /// Declared `#[spec(prove)]` wrappers that emitted no obligation at
    /// all. NOT a classification of a proof -- it counts declarations
    /// that never reached the proof layer, which every other counter here
    /// is structurally blind to. Deliberately NOT part of
    /// [`Self::is_clean`]: it is a visibility guard, and one legitimate
    /// member remains (a prove-spec with a target but no `ensures`, whose
    /// abort face `ignore_abort` also removes). Making it fatal would
    /// convert a reporting fix into a gate change.
    pub spec_no_obligation: usize,
}

#[derive(Debug, serde::Deserialize, serde::Serialize, PartialEq, Eq)]
struct ProofStatusDocument {
    /// The artifact-provenance regime this report was produced under:
    /// `clean-room` (`--audit-clean-room`: every OLean compiled from these
    /// bytes during the run) or `cached` (the default: compilation artifacts
    /// reused from the project's own build). Always written, and always echoed in the
    /// `proof audit [<mode>]:` line, so a report can never be mistaken for
    /// one produced under the other regime. Reports written before the flag
    /// existed have no field and read back as empty.
    #[serde(default)]
    audit_mode: String,
    proven: usize,
    conditional: usize,
    declared: usize,
    trusted: usize,
    #[serde(default)]
    smt_trusted: usize,
    sorry: usize,
    suspicious: usize,
    missing: usize,
    statement_mismatch: usize,
    #[serde(default)]
    statement_unverified: usize,
    #[serde(default)]
    spec_no_obligation: usize,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    warnings: Vec<String>,
    #[serde(
        default,
        rename = "unproduced_obligation",
        skip_serializing_if = "Vec::is_empty"
    )]
    unproduced_obligations: Vec<ProofStatusUnproducedObligation>,
    #[serde(default, rename = "obligation", skip_serializing_if = "Vec::is_empty")]
    obligations: Vec<ProofStatusObligation>,
}

/// One `[[unproduced_obligation]]` row: a declared `#[spec(prove)]`
/// wrapper that emitted nothing. It has no Lean declaration, no status
/// and no axiom footprint -- naming it is the whole report.
#[derive(Debug, serde::Deserialize, serde::Serialize, PartialEq, Eq)]
struct ProofStatusUnproducedObligation {
    source: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    reason: Option<String>,
}

#[derive(Debug, serde::Deserialize, serde::Serialize, PartialEq, Eq)]
struct ProofStatusObligation {
    name: String,
    module: String,
    kind: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    reason: Option<String>,
    status: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    statement_note: Option<String>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    extra_hypotheses: Vec<String>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    declared_axioms: Vec<String>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    smt_trusted_axioms: Vec<String>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    unexpected_axioms: Vec<String>,
}

impl ProofStatusDocument {
    fn new(
        mode: AuditMode,
        summary: &AuditSummary,
        warnings: Vec<String>,
        obligations: Vec<ProofStatusObligation>,
        unproduced_obligations: Vec<ProofStatusUnproducedObligation>,
    ) -> Self {
        Self {
            audit_mode: mode.label().to_string(),
            proven: summary.proven,
            conditional: summary.conditional,
            declared: summary.declared,
            trusted: summary.trusted,
            smt_trusted: summary.smt_trusted,
            sorry: summary.sorry,
            suspicious: summary.suspicious,
            missing: summary.missing,
            statement_mismatch: summary.statement_mismatch,
            statement_unverified: summary.statement_unverified,
            spec_no_obligation: summary.spec_no_obligation,
            warnings,
            unproduced_obligations,
            obligations,
        }
    }
}

const PROOF_STATUS_HEADER: &str =
    "# Generated by sui-lean --audit-proofs: per-obligation axiom-footprint +\n\
     # statement classification against obligations.toml. `suspicious` /\n\
     # `missing` / `statement_mismatch` fail the run; `sorry` counts unproven\n\
     # obligations (incl. transitive sorries); `conditional` proofs carry\n\
     # extra hypotheses beyond the obligation prop; `smt_trusted` records\n\
     # Z3 oracle closes separately from kernel-checked proofs;\n\
     # `statement_unverified` marks a statement check that did not complete\n\
     # within its per-obligation budget -- never a pass.\n\
     # `spec_no_obligation` counts declared `#[spec(prove)]` wrappers that\n\
     # produced NO obligation, so no proof of them can exist and every\n\
     # other counter here is blind to them; each is listed under\n\
     # [[unproduced_obligation]]. It does not fail the run -- it exists so\n\
     # the class can never again be zero-by-absence under a `0 missing`\n\
     # header. A non-zero value means verification was declared and\n\
     # nothing in the corpus discharges it.\n\
     # `audit_mode` records where the Lean artifacts came from -- NOT what\n\
     # was checked, which is identical either way. `clean-room`\n\
     # (--audit-clean-room) means every OLean the audit read was compiled from\n\
     # these exact source bytes during this run, in a project that started with\n\
     # no build directory. `cached` (the default) means compilation\n\
     # artifacts were reused from the project's own build and may predate this\n\
     # run; the key covers the generated tree, the proof overlay, the pinned\n\
     # vendored dependencies and the toolchain binaries, but nothing\n\
     # re-verifies the stored artifacts themselves.\n";

fn write_proof_status(
    path: &Path,
    mode: AuditMode,
    summary: &AuditSummary,
    warnings: Vec<String>,
    obligations: Vec<ProofStatusObligation>,
    unproduced_obligations: Vec<ProofStatusUnproducedObligation>,
) -> anyhow::Result<()> {
    let document =
        ProofStatusDocument::new(mode, summary, warnings, obligations, unproduced_obligations);
    let serialized = toml::to_string_pretty(&document).context("serializing proof status")?;
    std::fs::write(path, format!("{PROOF_STATUS_HEADER}{serialized}"))
        .with_context(|| format!("writing {}", path.display()))
}

impl AuditSummary {
    pub fn is_clean(&self) -> bool {
        self.sorry == 0
            && self.suspicious == 0
            && self.missing == 0
            && self.statement_mismatch == 0
            && self.statement_unverified == 0
    }

    fn bump(&mut self, status: &str) {
        match status {
            "proven" => self.proven += 1,
            "conditional" => self.conditional += 1,
            "declared" => self.declared += 1,
            "trusted" => self.trusted += 1,
            "smt_trusted" => self.smt_trusted += 1,
            "sorry" => self.sorry += 1,
            "suspicious" => self.suspicious += 1,
            "missing" => self.missing += 1,
            "statement_mismatch" => self.statement_mismatch += 1,
            "statement_unverified" => self.statement_unverified += 1,
            other => unreachable!("unknown audit status `{other}`"),
        }
    }
}

/// Status of a theorem obligation, by fixed precedence: integrity
/// failures first (unexpected axioms, then a statement that is not the
/// obligation), then unproven (`sorry`), then the proven-modulo classes
/// (`conditional` extra hypotheses, `declared` axioms, trusted SMT), then
/// `proven`.
/// The axiom classification stays orthogonal to the statement check --
/// a conditional proof containing `sorryAx` reports as `sorry`.
fn theorem_status(
    has_unexpected_axioms: bool,
    statement_verdict: &str,
    has_sorry: bool,
    has_declared: bool,
    has_smt_trusted: bool,
) -> &'static str {
    if has_unexpected_axioms {
        "suspicious"
    } else if statement_verdict == "mismatch" {
        "statement_mismatch"
    } else if statement_verdict == "unverified" {
        "statement_unverified"
    } else if has_sorry {
        "sorry"
    } else if statement_verdict == "conditional" {
        "conditional"
    } else if has_declared {
        "declared"
    } else if has_smt_trusted {
        "smt_trusted"
    } else {
        "proven"
    }
}

fn expected_declaration_kind(obligation_kind: &str) -> Option<&'static str> {
    match obligation_kind {
        "theorem" => Some("theorem"),
        "trusted_axiom" => Some("axiom"),
        _ => None,
    }
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

fn obligation_audit_import(obligation: &Obligation) -> anyhow::Result<String> {
    match obligation.kind.as_str() {
        "theorem" => Ok(format!(
            "{}_Proofs.{}",
            obligation.module,
            proof_shard_stem(&obligation.ir_name)
        )),
        "trusted_axiom" => Ok(obligation.module.clone()),
        other => anyhow::bail!(
            "obligations.toml: unknown kind `{}` for `{}`",
            other,
            obligation.name
        ),
    }
}

/// A per-run token embedded in the isolated `ProofAudit.lean`, which the
/// audited module never imports or parses. The Rust parser accepts only
/// nonce-prefixed lines and requires the completion sentinel. The nonce is
/// not cryptographic; the trusted query boundary is the primary defense.
fn audit_nonce() -> String {
    let nanos = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_nanos())
        .unwrap_or(0);
    format!("AUDIT_{:x}_{:x}", std::process::id(), nanos)
}

fn is_lean_identifier_byte(byte: u8) -> bool {
    byte.is_ascii_alphanumeric() || matches!(byte, b'_' | b'\'' | b'?' | b'!') || !byte.is_ascii()
}

fn find_lean_token(input: &str, token: &str) -> Option<usize> {
    input.match_indices(token).find_map(|(index, _)| {
        let bytes = input.as_bytes();
        let before = index.checked_sub(1).map(|offset| bytes[offset]);
        let after = bytes.get(index + token.len()).copied();
        (!before.is_some_and(is_lean_identifier_byte)
            && !after.is_some_and(is_lean_identifier_byte))
        .then_some(index)
    })
}

fn find_lean_name_reference(input: &str, name: &str) -> Option<usize> {
    let quoted = format!("«{name}»");
    [
        find_lean_token(input, name),
        input.match_indices(&quoted).next().map(|(index, _)| index),
    ]
    .into_iter()
    .flatten()
    .min()
}

fn find_lean_name_sequence(input: &str, components: &[&str]) -> Option<usize> {
    let mut spellings = vec![String::new()];
    for component in components {
        let mut next = Vec::with_capacity(spellings.len() * 2);
        for prefix in spellings {
            let separator = if prefix.is_empty() { "" } else { "." };
            next.push(format!("{prefix}{separator}{component}"));
            next.push(format!("{prefix}{separator}«{component}»"));
        }
        spellings = next;
    }
    if components.len() > 1 {
        spellings.push(format!("«{}»", components.join(".")));
    }
    spellings
        .into_iter()
        .filter_map(|spelling| find_lean_token(input, &spelling))
        .min()
}

fn lean_attribute_end(input: &str) -> Option<usize> {
    let bytes = input.as_bytes();
    let mut depth = 1usize;
    let mut index = 0usize;
    let mut in_string = false;
    let mut escaped = false;
    while index < bytes.len() {
        let byte = bytes[index];
        if in_string {
            if escaped {
                escaped = false;
            } else if byte == b'\\' {
                escaped = true;
            } else if byte == b'"' {
                in_string = false;
            }
        } else if byte == b'"' {
            in_string = true;
        } else if byte == b'[' {
            depth += 1;
        } else if byte == b']' {
            depth -= 1;
            if depth == 0 {
                return Some(index);
            }
        }
        index += 1;
    }
    None
}

fn find_initializer_attribute(input: &str) -> Option<(usize, &'static str)> {
    input.match_indices("@[").find_map(|(attribute_start, _)| {
        let body = &input[attribute_start + 2..];
        let attribute_end = lean_attribute_end(body)?;
        let body = &body[..attribute_end];
        [
            find_lean_token(body, "init").map(|_| "@[init]"),
            find_lean_token(body, "builtin_init").map(|_| "@[builtin_init]"),
            body.contains("«init»").then_some("@[«init»]"),
            body.contains("«builtin_init»")
                .then_some("@[«builtin_init»]"),
        ]
        .into_iter()
        .flatten()
        .next()
        .map(|token| (attribute_start, token))
    })
}

fn forbidden_import_time_construct(input: &str) -> Option<(usize, &'static str)> {
    [
        input
            .match_indices("#eval")
            .next()
            .map(|(index, _)| (index, "#eval")),
        find_lean_token(input, "initialize").map(|index| (index, "initialize")),
        find_lean_token(input, "builtin_initialize").map(|index| (index, "builtin_initialize")),
        find_initializer_attribute(input),
    ]
    .into_iter()
    .flatten()
    .min_by_key(|(index, _)| *index)
}

fn forbidden_z3_trust_construct(input: &str) -> Option<(usize, &'static str)> {
    [
        find_lean_name_reference(input, "autoSMTSorry").map(|index| (index, "autoSMTSorry")),
        find_lean_name_reference(input, "z3OracleResult").map(|index| (index, "z3OracleResult")),
        find_lean_name_reference(input, "explicitZ3OracleResult")
            .map(|index| (index, "explicitZ3OracleResult")),
        find_lean_name_reference(input, "move_z3").map(|index| (index, "move_z3")),
        find_lean_name_sequence(input, &["auto", "smt", "trust"])
            .map(|index| (index, "auto.smt.trust")),
    ]
    .into_iter()
    .flatten()
    .min_by_key(|(index, _)| *index)
}

fn lean_code_without_comments_and_strings(input: &str) -> String {
    let bytes = input.as_bytes();
    let mut output = bytes.to_vec();
    let mut index = 0usize;
    let mut block_depth = 0usize;
    let mut line_comment = false;
    let mut string = false;
    let mut escaped = false;
    while index < bytes.len() {
        if line_comment {
            if bytes[index] == b'\n' {
                line_comment = false;
            } else {
                output[index] = b' ';
            }
            index += 1;
            continue;
        }
        if block_depth > 0 {
            if bytes[index..].starts_with(b"/-") {
                output[index] = b' ';
                output[index + 1] = b' ';
                block_depth += 1;
                index += 2;
            } else if bytes[index..].starts_with(b"-/") {
                output[index] = b' ';
                output[index + 1] = b' ';
                block_depth -= 1;
                index += 2;
            } else {
                if bytes[index] != b'\n' {
                    output[index] = b' ';
                }
                index += 1;
            }
            continue;
        }
        if string {
            if bytes[index] != b'\n' {
                output[index] = b' ';
            }
            if escaped {
                escaped = false;
            } else if bytes[index] == b'\\' {
                escaped = true;
            } else if bytes[index] == b'"' {
                string = false;
            }
            index += 1;
            continue;
        }
        if bytes[index..].starts_with(b"--") {
            output[index] = b' ';
            output[index + 1] = b' ';
            line_comment = true;
            index += 2;
        } else if bytes[index..].starts_with(b"/-") {
            output[index] = b' ';
            output[index + 1] = b' ';
            block_depth = 1;
            index += 2;
        } else if bytes[index] == b'"' {
            output[index] = b' ';
            string = true;
            index += 1;
        } else {
            index += 1;
        }
    }
    String::from_utf8(output).expect("masking preserves the input's UTF-8 bytes")
}

fn forbidden_proof_metaprogram_construct(input: &str) -> Option<(usize, &'static str)> {
    let code = lean_code_without_comments_and_strings(input);
    [
        find_lean_token(&code, "unsafe").map(|index| (index, "unsafe")),
        find_lean_token(&code, "elab").map(|index| (index, "elab")),
        find_lean_token(&code, "elab_rules").map(|index| (index, "elab_rules")),
        find_lean_token(&code, "macro").map(|index| (index, "macro")),
        find_lean_token(&code, "macro_rules").map(|index| (index, "macro_rules")),
        find_lean_token(&code, "syntax").map(|index| (index, "syntax")),
        find_lean_token(&code, "run_tac").map(|index| (index, "run_tac")),
        find_lean_token(&code, "by_elab").map(|index| (index, "by_elab")),
        find_lean_token(&code, "run_cmd").map(|index| (index, "run_cmd")),
        find_lean_name_reference(&code, "fromMetaTactic").map(|index| (index, "fromMetaTactic")),
        find_lean_name_reference(&code, "getExprAndApply").map(|index| (index, "getExprAndApply")),
        find_lean_token(&code, "declare_rebindable").map(|index| (index, "declare_rebindable")),
        find_lean_token(&code, "eval_rebind").map(|index| (index, "eval_rebind")),
        find_lean_token(&code, "tactic").map(|index| (index, "tactic")),
        find_lean_token(&code, "meta").map(|index| (index, "meta")),
        find_lean_name_reference(&code, "MetaM").map(|index| (index, "MetaM")),
        find_lean_name_reference(&code, "TermElabM").map(|index| (index, "TermElabM")),
        find_lean_name_reference(&code, "TacticM").map(|index| (index, "TacticM")),
        find_lean_name_reference(&code, "MVarId").map(|index| (index, "MVarId")),
        find_lean_name_reference(&code, "RuleTac").map(|index| (index, "RuleTac")),
        find_lean_name_reference(&code, "TacGen").map(|index| (index, "TacGen")),
    ]
    .into_iter()
    .flatten()
    .min_by_key(|(index, _)| *index)
}

fn forbidden_native_decide_axiom_construct(input: &str) -> Option<(usize, &'static str)> {
    let code = lean_code_without_comments_and_strings(input);
    let axiom = find_lean_token(&code, "axiom")?;
    find_lean_name_reference(&code, "_native")?;
    find_lean_name_reference(&code, "native_decide")?;
    Some((axiom, "axiom + _native + native_decide"))
}

fn embedded_lemma_source(relative: &str) -> Option<&'static [u8]> {
    LEMMA_BUNDLE_FILES
        .iter()
        .find(|(path, _)| *path == relative)
        .map(|(_, bytes)| *bytes)
}

fn pinned_move_auto_sources(output_dir: &Path) -> bool {
    PINNED_OUTPUT_SOURCES
        .into_iter()
        .all(|(bundle_relative, output_relative)| {
            let Some(expected) = embedded_lemma_source(bundle_relative) else {
                return false;
            };
            let path = output_dir.join(output_relative);
            std::fs::symlink_metadata(&path).is_ok_and(|metadata| {
                metadata.is_file()
                    && !metadata.file_type().is_symlink()
                    && std::fs::read(path).is_ok_and(|source| source == expected)
            })
        })
}

#[derive(Debug, Default, PartialEq, Eq)]
struct LemmaBundleComparison {
    matched: Vec<String>,
    mismatched: Vec<String>,
    missing: Vec<String>,
    extra: Vec<String>,
}

fn compare_lemma_bundle(
    embedded: &[(&str, &[u8])],
    bundle_dir: &Path,
) -> anyhow::Result<LemmaBundleComparison> {
    let mut comparison = LemmaBundleComparison::default();
    for (relative, expected) in embedded {
        let path = bundle_dir.join(relative);
        let metadata = match std::fs::symlink_metadata(&path) {
            Ok(metadata) => metadata,
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => {
                comparison.missing.push((*relative).to_string());
                continue;
            }
            Err(error) => {
                return Err(error)
                    .with_context(|| format!("inspecting bundle file {}", path.display()));
            }
        };
        if !metadata.is_file() || metadata.file_type().is_symlink() {
            comparison.mismatched.push((*relative).to_string());
            continue;
        }
        let actual = std::fs::read(&path)
            .with_context(|| format!("reading bundle file {}", path.display()))?;
        if actual == *expected {
            comparison.matched.push((*relative).to_string());
        } else {
            comparison.mismatched.push((*relative).to_string());
        }
    }

    let pinned = embedded
        .iter()
        .map(|(relative, _)| *relative)
        .collect::<BTreeSet<_>>();
    let mut stack = vec![bundle_dir.to_path_buf()];
    while let Some(dir) = stack.pop() {
        let entries = match std::fs::read_dir(&dir) {
            Ok(entries) => entries,
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => continue,
            Err(error) => {
                return Err(error).with_context(|| format!("read_dir({})", dir.display()));
            }
        };
        for entry in entries {
            let entry = entry.with_context(|| format!("read entry under {}", dir.display()))?;
            let path = entry.path();
            let name = path.file_name().and_then(|name| name.to_str());
            if name.is_some_and(|name| UNBUNDLED_DIRS.contains(&name)) {
                continue;
            }
            let metadata = std::fs::symlink_metadata(&path)
                .with_context(|| format!("metadata({})", path.display()))?;
            if metadata.is_dir() {
                stack.push(path);
                continue;
            }
            let Ok(relative) = path.strip_prefix(bundle_dir) else {
                continue;
            };
            let relative = relative.to_string_lossy().replace('\\', "/");
            if !pinned.contains(relative.as_str()) {
                comparison.extra.push(relative);
            }
        }
    }

    comparison.matched.sort();
    comparison.mismatched.sort();
    comparison.missing.sort();
    comparison.extra.sort();
    Ok(comparison)
}

fn render_bundle_file_list(label: &str, files: &[String]) -> String {
    if files.is_empty() {
        return String::new();
    }
    let mut rendered = format!("\n  {label} ({}):", files.len());
    for file in files {
        rendered.push_str(&format!("\n    {file}"));
    }
    rendered
}

/// Byte-compare EVERY file of the resolved Lean model bundle against the copy
/// this binary embedded at compile time. Audit-only: plain generation still
/// runs against whatever bundle it resolves, and the dev loop of editing a
/// lemma file and re-rendering without rebuilding stays intact.
pub fn verify_pinned_lemma_bundle(bundle_dir: &Path) -> anyhow::Result<()> {
    let comparison = compare_lemma_bundle(LEMMA_BUNDLE_FILES, bundle_dir)?;
    if !comparison.extra.is_empty() {
        eprintln!(
            "proof audit: warning: {} file(s) under the resolved Lean model bundle {} are not \
             pinned by this sui-lean binary (inert for generated imports, but unreviewed):{}",
            comparison.extra.len(),
            bundle_dir.display(),
            render_bundle_file_list("unpinned", &comparison.extra)
        );
    }
    anyhow::ensure!(
        comparison.mismatched.is_empty() && comparison.missing.is_empty(),
        "proof audit: the Lean model bundle does not match the running sui-lean binary\n  \
         resolved bundle: {}\n  pinned files: {} ({} matched){}{}",
        bundle_dir.display(),
        LEMMA_BUNDLE_FILES.len(),
        comparison.matched.len(),
        render_bundle_file_list("mismatched", &comparison.mismatched),
        render_bundle_file_list("missing", &comparison.missing)
    );
    Ok(())
}

#[derive(Debug, PartialEq, Eq)]
enum ToolchainVerdict {
    Matched,
    Mismatched(String),
    Missing,
}

fn compare_lean_toolchain(project_dir: &Path) -> anyhow::Result<ToolchainVerdict> {
    let path = project_dir.join("lean-toolchain");
    let found = match std::fs::read_to_string(&path) {
        Ok(found) => found,
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => {
            return Ok(ToolchainVerdict::Missing);
        }
        Err(error) => {
            return Err(error).with_context(|| format!("reading {}", path.display()));
        }
    };
    if found == lean_pipeline::render::GENERATED_LEAN_TOOLCHAIN {
        Ok(ToolchainVerdict::Matched)
    } else {
        Ok(ToolchainVerdict::Mismatched(found))
    }
}

/// Verify the audited project pins the one Lean this binary generates for, and
/// return that pin for the audit's own reporting. Without a `lean-toolchain`
/// lake resolves Lean by walking the project's ANCESTORS, so a stray file above
/// a temp dir -- or the elan default -- silently decides which Lean checked the
/// proofs. Audit-only, like the bundle pin.
pub fn verify_pinned_lean_toolchain(project_dir: &Path) -> anyhow::Result<&'static str> {
    let expected = lean_pipeline::render::GENERATED_LEAN_TOOLCHAIN.trim();
    match compare_lean_toolchain(project_dir)? {
        ToolchainVerdict::Matched => Ok(expected),
        ToolchainVerdict::Mismatched(found) => anyhow::bail!(
            "proof audit: the audited Lean project does not pin the Lean toolchain this \
             sui-lean binary generates for\n  toolchain file: {}\n  expected: {}\n  found: {}",
            project_dir.join("lean-toolchain").display(),
            expected,
            found.trim()
        ),
        ToolchainVerdict::Missing => anyhow::bail!(
            "proof audit: the audited Lean project has no lean-toolchain, so lake resolves Lean \
             by walking ancestors\n  toolchain file: {}\n  expected: {}",
            project_dir.join("lean-toolchain").display(),
            expected
        ),
    }
}

fn reject_reserved_module_collisions(root: &Path, source_kind: &str) -> anyhow::Result<()> {
    if !root.is_dir() {
        return Ok(());
    }
    for module_root in RESERVED_LEAN_MODULE_ROOTS {
        for path in [
            root.join(module_root),
            root.join(format!("{module_root}.lean")),
        ] {
            match std::fs::symlink_metadata(&path) {
                Ok(_) => anyhow::bail!(
                    "proof audit: {source_kind} path {} shadows reserved Lean module root `{module_root}`",
                    path.display()
                ),
                Err(error) if error.kind() == std::io::ErrorKind::NotFound => {}
                Err(error) => {
                    return Err(error).with_context(|| {
                        format!(
                            "proof audit: cannot inspect {source_kind} path {}",
                            path.display()
                        )
                    });
                }
            }
        }
    }
    Ok(())
}

fn scan_generated_sources_for_z3_bypasses(output_dir: &Path) -> anyhow::Result<()> {
    reject_reserved_module_collisions(output_dir, "generated")?;
    if !output_dir.join("Prover/MoveAuto.lean").is_file() {
        return Ok(());
    }
    anyhow::ensure!(
        pinned_move_auto_sources(output_dir),
        "proof audit: generated Prover.MoveAuto sources do not match the running sui-lean binary"
    );
    let move_auto = Path::new("Prover/MoveAuto.lean");
    let mut stack = vec![output_dir.to_path_buf()];
    while let Some(dir) = stack.pop() {
        for entry in
            std::fs::read_dir(&dir).with_context(|| format!("read_dir({})", dir.display()))?
        {
            let entry = entry.with_context(|| format!("read entry under {}", dir.display()))?;
            let path = entry.path();
            let relative = path
                .strip_prefix(output_dir)
                .expect("generated source is beneath the output root");
            if relative
                .components()
                .any(|component| matches!(component.as_os_str().to_str(), Some(".lake" | "vendor")))
            {
                continue;
            }
            let metadata = std::fs::symlink_metadata(&path)
                .with_context(|| format!("metadata({})", path.display()))?;
            anyhow::ensure!(
                !metadata.file_type().is_symlink(),
                "generated audit source is a symlink: {}",
                path.display()
            );
            if metadata.is_dir() {
                stack.push(path);
                continue;
            }
            if relative == move_auto
                || path.extension().and_then(|extension| extension.to_str()) != Some("lean")
            {
                continue;
            }
            let text = std::fs::read_to_string(&path)
                .with_context(|| format!("read {}", path.display()))?;
            let forbidden = forbidden_import_time_construct(&text)
                .or_else(|| forbidden_z3_trust_construct(&text))
                .or_else(|| forbidden_native_decide_axiom_construct(&text))
                .or_else(|| forbidden_proof_metaprogram_construct(&text));
            if let Some((offset, token)) = forbidden {
                let line = text[..offset].bytes().filter(|byte| *byte == b'\n').count() + 1;
                anyhow::bail!(
                    "proof audit: refusing generated source {}:{} with reserved import-time \
                     execution, proof metaprogram, or Z3-trust token `{}`",
                    path.display(),
                    line,
                    token
                );
            }
        }
    }
    Ok(())
}

/// Reject any `.lean` file under the proof overlay that may execute code at
/// import time. The reserved token patterns are rejected even in comments or
/// strings: accepting a false positive is safer than maintaining a partial
/// Lean lexer at this trust boundary.
fn scan_overlay_for_import_time_execution(overlay_root: &Path) -> anyhow::Result<()> {
    if !overlay_root.is_dir() {
        return Ok(());
    }
    let mut stack = vec![overlay_root.to_path_buf()];
    while let Some(dir) = stack.pop() {
        for entry in
            std::fs::read_dir(&dir).with_context(|| format!("read_dir({})", dir.display()))?
        {
            let entry = entry.with_context(|| format!("read entry under {}", dir.display()))?;
            let path = entry.path();
            if path.is_dir() {
                stack.push(path);
                continue;
            }
            if path.extension().and_then(|e| e.to_str()) != Some("lean") {
                continue;
            }
            let text = std::fs::read_to_string(&path)
                .with_context(|| format!("read {}", path.display()))?;
            if let Some((offset, token)) = forbidden_import_time_construct(&text) {
                let line = text[..offset].bytes().filter(|byte| *byte == b'\n').count() + 1;
                anyhow::bail!(
                    "proof audit: refusing to audit -- {}:{} contains reserved import-time \
                     execution token `{}`. Proof overlay files must not contain \
                     `#eval`, `initialize`, `builtin_initialize`, `@[init]`, or `@[builtin_init]` \
                     (including quoted spellings, comments, and strings); remove it before auditing.",
                    path.display(),
                    line,
                    token
                );
            }
            if let Some((offset, token)) = forbidden_z3_trust_construct(&text) {
                let line = text[..offset].bytes().filter(|byte| *byte == b'\n').count() + 1;
                anyhow::bail!(
                    "proof audit: refusing to audit -- {}:{} contains reserved Z3 trust \
                     token `{}`. Use `move_auto`; direct solver, oracle, and \
                     attestation access is forbidden.",
                    path.display(),
                    line,
                    token
                );
            }
            if let Some((offset, token)) = forbidden_native_decide_axiom_construct(&text) {
                let line = text[..offset].bytes().filter(|byte| *byte == b'\n').count() + 1;
                anyhow::bail!(
                    "proof audit: refusing to audit -- {}:{} contains forged native_decide \
                     provenance `{}`. Hand-authored axioms may not use the compiler-reserved \
                     `_native.native_decide` namespace.",
                    path.display(),
                    line,
                    token
                );
            }
            if let Some((offset, token)) = forbidden_proof_metaprogram_construct(&text) {
                let line = text[..offset].bytes().filter(|byte| *byte == b'\n').count() + 1;
                anyhow::bail!(
                    "proof audit: refusing to audit -- {}:{} contains reserved proof \
                     metaprogram token `{}`. Proof overlays may contain theorem terms and \
                     tactics, but may not define or execute custom elaborators.",
                    path.display(),
                    line,
                    token
                );
            }
        }
    }
    Ok(())
}

fn proof_overlay_snapshot(overlay_root: &Path) -> anyhow::Result<Vec<(PathBuf, Vec<u8>)>> {
    let root_metadata = match std::fs::symlink_metadata(overlay_root) {
        Ok(metadata) => metadata,
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => return Ok(Vec::new()),
        Err(error) => {
            return Err(error).with_context(|| format!("metadata({})", overlay_root.display()));
        }
    };
    anyhow::ensure!(
        root_metadata.is_dir() && !root_metadata.file_type().is_symlink(),
        "proof overlay must be a non-symlink directory: {}",
        overlay_root.display()
    );
    let mut files = Vec::new();
    let mut stack = vec![overlay_root.to_path_buf()];
    while let Some(dir) = stack.pop() {
        let mut entries = std::fs::read_dir(&dir)
            .with_context(|| format!("read_dir({})", dir.display()))?
            .collect::<Result<Vec<_>, _>>()
            .with_context(|| format!("read entries under {}", dir.display()))?;
        entries.sort_by_key(std::fs::DirEntry::file_name);
        for entry in entries {
            let path = entry.path();
            let metadata = std::fs::symlink_metadata(&path)
                .with_context(|| format!("metadata({})", path.display()))?;
            anyhow::ensure!(
                !metadata.file_type().is_symlink(),
                "proof overlay entries must not be symlinks: {}",
                path.display()
            );
            if metadata.is_dir() {
                stack.push(path);
            } else if metadata.is_file() {
                files.push((
                    path.strip_prefix(overlay_root)
                        .expect("snapshot path is beneath its root")
                        .to_path_buf(),
                    std::fs::read(&path).with_context(|| format!("read {}", path.display()))?,
                ));
            } else {
                anyhow::bail!(
                    "proof overlay entries must be regular files or directories: {}",
                    path.display()
                );
            }
        }
    }
    files.sort_by(|left, right| left.0.cmp(&right.0));
    Ok(files)
}

/// Load the package's committed axiom allowlist
/// (`<package-root>/lean/trusted_axioms.toml`), if any. Every entry
/// must carry a non-empty justification -- the file IS the reviewable
/// trust declaration, not a mute name list.
fn load_declared_axioms(package_dir: &Path) -> anyhow::Result<Vec<DeclaredAxiom>> {
    let path = package_dir.join("lean").join("trusted_axioms.toml");
    let Ok(raw) = std::fs::read_to_string(&path) else {
        return Ok(Vec::new());
    };
    let parsed: DeclaredAxioms =
        toml::from_str(&raw).with_context(|| format!("parsing {}", path.display()))?;
    for ax in &parsed.axiom {
        anyhow::ensure!(
            !ax.justification.trim().is_empty(),
            "{}: axiom `{}` needs a justification",
            path.display(),
            ax.name
        );
    }
    Ok(parsed.axiom)
}

#[derive(Debug, Default, PartialEq, Eq)]
struct AuditGroupOutput {
    found: BTreeMap<String, (bool, String, String)>,
    statements: BTreeMap<String, (String, usize)>,
    /// Why an `unverified` statement check did not complete. Present for
    /// exactly the `unverified` verdicts; display-only, never a trust input.
    statement_notes: BTreeMap<String, String>,
    hypotheses: BTreeMap<String, Vec<String>>,
    axioms: BTreeMap<String, Vec<(String, String, bool)>>,
    z3_oracle_attested: BTreeMap<String, bool>,
}

fn parse_audit_group_output(
    nonce: &str,
    import: &str,
    obligations: &[&Obligation],
    stdout: &str,
) -> anyhow::Result<AuditGroupOutput> {
    let expected: BTreeSet<&str> = obligations
        .iter()
        .map(|obligation| obligation.lean_decl.as_str())
        .collect();
    anyhow::ensure!(
        expected.len() == obligations.len(),
        "audit group `{import}` contains duplicate declaration labels"
    );
    let prefix = format!("{nonce}|");
    let mut output = AuditGroupOutput::default();
    let mut completed = false;

    for line in stdout.lines() {
        let Some(row) = line.strip_prefix(&prefix) else {
            continue;
        };
        anyhow::ensure!(
            !completed,
            "audit group `{import}` emitted a protocol row after END: `{line}`"
        );
        if let Some(payload) = row.strip_prefix("OB|") {
            let fields: Vec<_> = payload.splitn(4, '|').collect();
            anyhow::ensure!(fields.len() == 4, "malformed OB row: `{line}`");
            let label = fields[0];
            anyhow::ensure!(
                expected.contains(label),
                "audit group `{import}` emitted OB for unknown label `{label}`"
            );
            let found = match fields[1] {
                "ok" => true,
                "missing" => false,
                status => anyhow::bail!("invalid OB status `{status}` in `{line}`"),
            };
            if found {
                anyhow::ensure!(
                    matches!(
                        fields[2],
                        "def" | "abbrev" | "opaque" | "theorem" | "axiom" | "other"
                    ),
                    "present OB row has invalid declaration kind: `{line}`"
                );
                anyhow::ensure!(
                    !fields[3].is_empty() && fields[3] != "-",
                    "present OB row has invalid declaring module: `{line}`"
                );
            } else {
                anyhow::ensure!(
                    fields[2] == "-" && fields[3] == "-",
                    "missing OB row must use kind and declaring module `-`: `{line}`"
                );
            }
            anyhow::ensure!(
                output
                    .found
                    .insert(
                        label.to_string(),
                        (found, fields[2].to_string(), fields[3].to_string()),
                    )
                    .is_none(),
                "duplicate OB row for `{label}` in audit group `{import}`"
            );
        } else if let Some(payload) = row.strip_prefix("ST|") {
            let fields: Vec<_> = payload.splitn(4, '|').collect();
            anyhow::ensure!(fields.len() == 4, "malformed ST row: `{line}`");
            let label = fields[0];
            anyhow::ensure!(
                expected.contains(label),
                "audit group `{import}` emitted ST for unknown label `{label}`"
            );
            anyhow::ensure!(
                matches!(
                    fields[1],
                    "exact" | "conditional" | "mismatch" | "prop_missing" | "unverified"
                ),
                "invalid ST verdict `{}` in `{line}`",
                fields[1]
            );
            let count: usize = fields[2]
                .parse()
                .with_context(|| format!("invalid ST hypothesis count in `{line}`"))?;
            // The note is the free-form LAST field, `-` for every verdict that
            // completed. A missing reason on `unverified` would hide why the
            // check failed, so demand one; a reason on any other verdict means
            // the metaprogram and this parser disagree.
            if fields[1] == "unverified" {
                anyhow::ensure!(
                    !fields[3].is_empty() && fields[3] != "-",
                    "unverified ST row for `{label}` carries no reason: `{line}`"
                );
                output
                    .statement_notes
                    .insert(label.to_string(), fields[3].to_string());
            } else {
                anyhow::ensure!(
                    fields[3] == "-",
                    "completed ST row for `{label}` carries a reason: `{line}`"
                );
            }
            anyhow::ensure!(
                output
                    .statements
                    .insert(label.to_string(), (fields[1].to_string(), count))
                    .is_none(),
                "duplicate ST row for `{label}` in audit group `{import}`"
            );
        } else if let Some(payload) = row.strip_prefix("HYP|") {
            let fields: Vec<_> = payload.splitn(2, '|').collect();
            anyhow::ensure!(fields.len() == 2, "malformed HYP row: `{line}`");
            let label = fields[0];
            anyhow::ensure!(
                expected.contains(label),
                "audit group `{import}` emitted HYP for unknown label `{label}`"
            );
            output
                .hypotheses
                .entry(label.to_string())
                .or_default()
                .push(fields[1].to_string());
        } else if let Some(payload) = row.strip_prefix("AX|") {
            let fields: Vec<_> = payload.splitn(4, '|').collect();
            anyhow::ensure!(fields.len() == 4, "malformed AX row: `{line}`");
            let label = fields[0];
            anyhow::ensure!(
                expected.contains(label),
                "audit group `{import}` emitted AX for unknown label `{label}`"
            );
            let native_decide_shape = match fields[1] {
                "0" => false,
                "1" => true,
                flag => anyhow::bail!("invalid AX native_decide flag `{flag}` in `{line}`"),
            };
            anyhow::ensure!(
                !fields[2].is_empty() && !fields[3].is_empty(),
                "AX row has an empty module or axiom name: `{line}`"
            );
            let axiom = (
                fields[3].to_string(),
                fields[2].to_string(),
                native_decide_shape,
            );
            let axioms = output.axioms.entry(label.to_string()).or_default();
            anyhow::ensure!(
                !axioms.contains(&axiom),
                "duplicate AX row for `{label}` in audit group `{import}`"
            );
            axioms.push(axiom);
        } else if let Some(payload) = row.strip_prefix("Z3|") {
            let fields: Vec<_> = payload.splitn(2, '|').collect();
            anyhow::ensure!(fields.len() == 2, "malformed Z3 row: `{line}`");
            let label = fields[0];
            anyhow::ensure!(
                expected.contains(label),
                "audit group `{import}` emitted Z3 for unknown label `{label}`"
            );
            let attested = match fields[1] {
                "0" => false,
                "1" => true,
                flag => anyhow::bail!("invalid Z3 attestation flag `{flag}` in `{line}`"),
            };
            anyhow::ensure!(
                output
                    .z3_oracle_attested
                    .insert(label.to_string(), attested)
                    .is_none(),
                "duplicate Z3 row for `{label}` in audit group `{import}`"
            );
        } else if let Some(payload) = row.strip_prefix("END|") {
            anyhow::ensure!(
                !payload.contains('|'),
                "malformed END row for audit group `{import}`: `{line}`"
            );
            let count: usize = payload
                .parse()
                .with_context(|| format!("invalid END count in `{line}`"))?;
            anyhow::ensure!(
                count == obligations.len(),
                "audit sentinel count {count} != {} obligations for group {import}",
                obligations.len()
            );
            completed = true;
        } else {
            anyhow::bail!("unknown nonce-prefixed audit row: `{line}`");
        }
    }

    anyhow::ensure!(
        completed,
        "audit metaprogram emitted no completion sentinel for group {import}"
    );
    for label in expected {
        let (found, kind, module) = output
            .found
            .get(label)
            .with_context(|| format!("audit output missing OB row for `{label}`"))?;
        if *found {
            anyhow::ensure!(kind != "-", "present declaration `{label}` has no kind");
            anyhow::ensure!(module != "-", "present declaration `{label}` has no module");
            let (verdict, expected_hypotheses) = output
                .statements
                .get(label)
                .with_context(|| format!("audit output missing ST row for `{label}`"))?;
            let actual_hypotheses = output.hypotheses.get(label).map_or(0, Vec::len);
            anyhow::ensure!(
                actual_hypotheses == *expected_hypotheses,
                "audit declared {expected_hypotheses} extra hypotheses for `{label}` but \
                 {actual_hypotheses} HYP rows arrived"
            );
            if verdict == "conditional" {
                anyhow::ensure!(
                    *expected_hypotheses > 0,
                    "conditional ST row for `{label}` declared no hypotheses"
                );
            } else {
                anyhow::ensure!(
                    *expected_hypotheses == 0,
                    "non-conditional ST row for `{label}` declared hypotheses"
                );
            }
            anyhow::ensure!(
                output.z3_oracle_attested.contains_key(label),
                "audit output missing Z3 row for `{label}`"
            );
        } else {
            anyhow::ensure!(
                kind == "-" && module == "-",
                "missing declaration `{label}` has a kind or module"
            );
            anyhow::ensure!(
                !output.statements.contains_key(label)
                    && !output.hypotheses.contains_key(label)
                    && !output.axioms.contains_key(label)
                    && !output.z3_oracle_attested.contains_key(label),
                "missing declaration `{label}` has trailing ST/HYP/AX/Z3 rows"
            );
        }
    }

    Ok(output)
}

fn copy_audit_source_tree(source: &Path, destination: &Path) -> anyhow::Result<()> {
    std::fs::create_dir_all(destination)
        .with_context(|| format!("creating {}", destination.display()))?;
    let mut entries = std::fs::read_dir(source)
        .with_context(|| format!("read_dir({})", source.display()))?
        .collect::<Result<Vec<_>, _>>()
        .with_context(|| format!("reading {}", source.display()))?;
    entries.sort_by_key(std::fs::DirEntry::file_name);
    for entry in entries {
        let path = entry.path();
        if matches!(entry.file_name().to_str(), Some(".git" | ".lake")) {
            continue;
        }
        let target = destination.join(entry.file_name());
        let metadata = std::fs::symlink_metadata(&path)
            .with_context(|| format!("metadata({})", path.display()))?;
        if metadata.file_type().is_symlink() {
            let link = std::fs::read_link(&path)
                .with_context(|| format!("read_link({})", path.display()))?;
            #[cfg(unix)]
            std::os::unix::fs::symlink(&link, &target)
                .with_context(|| format!("symlinking {}", target.display()))?;
            #[cfg(windows)]
            {
                let resolved = path
                    .canonicalize()
                    .with_context(|| format!("canonicalizing {}", path.display()))?;
                if resolved.is_dir() {
                    std::os::windows::fs::symlink_dir(&link, &target)
                } else {
                    std::os::windows::fs::symlink_file(&link, &target)
                }
                .with_context(|| format!("symlinking {}", target.display()))?;
            }
        } else if metadata.is_dir() {
            copy_audit_source_tree(&path, &target)?;
        } else if metadata.is_file() {
            std::fs::copy(&path, &target)
                .with_context(|| format!("copying {} to {}", path.display(), target.display()))?;
        } else {
            anyhow::bail!("unsupported audit source entry: {}", path.display());
        }
    }
    Ok(())
}

/// Opt-in triage escape hatch: keep the throwaway audit project and the
/// per-group `ProofAudit.lean` query directories instead of deleting them
/// when the run ends. The audit's temporaries are exactly what a failing
/// run needs to reproduce, and they vanish with the process otherwise.
const KEEP_AUDIT_PROJECT_ENV: &str = "SUI_LEAN_KEEP_AUDIT_PROJECT";

fn keep_audit_temporaries() -> bool {
    std::env::var_os(KEEP_AUDIT_PROJECT_ENV).is_some_and(|value| !value.is_empty() && value != "0")
}

/// Deterministic-timeout budget the metaprogram rebases on EVERY obligation's
/// statement check, in Lean's raw heartbeat unit. The env override is given in
/// the same units as `set_option maxHeartbeats`, which Lean stores scaled by
/// `HEARTBEATS_PER_OPTION_UNIT`; the default is the historical
/// `set_option maxHeartbeats 2000000`.
const STATEMENT_HEARTBEATS_ENV: &str = "SUI_LEAN_AUDIT_STATEMENT_HEARTBEATS";
const HEARTBEATS_PER_OPTION_UNIT: u64 = 1_000;
const DEFAULT_STATEMENT_HEARTBEATS: u64 = 2_000_000 * HEARTBEATS_PER_OPTION_UNIT;

/// Overriding the budget can only make the audit stricter: a smaller budget
/// turns slow checks into the fatal `statement_unverified` class, and no
/// budget can turn a mismatch into a pass. Malformed values are rejected
/// rather than silently ignored.
fn parse_statement_heartbeats(raw: Option<&str>) -> anyhow::Result<u64> {
    let Some(raw) = raw else {
        return Ok(DEFAULT_STATEMENT_HEARTBEATS);
    };
    raw.trim()
        .parse::<u64>()
        .with_context(|| format!("{STATEMENT_HEARTBEATS_ENV} must be a non-negative integer"))?
        .checked_mul(HEARTBEATS_PER_OPTION_UNIT)
        .with_context(|| format!("{STATEMENT_HEARTBEATS_ENV} is too large"))
}

fn statement_heartbeat_budget() -> anyhow::Result<u64> {
    let Some(raw) = std::env::var_os(STATEMENT_HEARTBEATS_ENV) else {
        return Ok(DEFAULT_STATEMENT_HEARTBEATS);
    };
    let raw = raw
        .to_str()
        .with_context(|| format!("{STATEMENT_HEARTBEATS_ENV} is not valid UTF-8"))?;
    parse_statement_heartbeats(Some(raw))
}

/// Which *artifact-provenance* regime the audit runs under. It changes
/// nothing about WHAT is checked -- statement matching, axiom collection,
/// sorry detection and provenance run identically and in full under both --
/// only who compiled the Lean artifacts the checks read.
///
/// `Cached` (the default) reuses the OLeans the project's own build already
/// produced. It brings them up to date with an ordinary INCREMENTAL
/// `lake build --rehash` in the project directory, then runs the checks against
/// that environment -- no isolated copy, no cold rebuild, no separate store.
///
/// It answers *"do my proofs discharge the obligations, assuming the build is
/// current"*. It does NOT answer *"is this corpus verified"* off a warm cache:
/// it inherits whatever `.lake` state the working tree carries and relies on
/// Lake's incremental invalidation, which is precisely what `CleanRoom` refuses
/// to rely on -- though when the build cannot be stale (a fresh CI runner has
/// no prior build), the two coincide. Hence `[cached]` in the audit line and
/// `audit_mode = "cached"` in the report -- a result produced this way must
/// never be readable as a clean-room one.
///
/// `CleanRoom` (reachable via `--audit-clean-room`) instead guarantees that
/// every OLean the audit inspects was compiled from the audited source bytes,
/// by the pinned toolchain, DURING THIS RUN, in a throwaway project that
/// started with no `.lake` anywhere.
///
/// Policy: cached is the default; reach for clean-room to quote a result as
/// verification off a warm local cache.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AuditMode {
    CleanRoom,
    Cached,
}

impl AuditMode {
    /// The token that goes verbatim into the audit line and into
    /// `proof_status.toml`. A quoted audit line must state its own
    /// provenance -- three months later, in a commit message, nobody can
    /// recover it from context.
    pub fn label(self) -> &'static str {
        match self {
            Self::CleanRoom => "clean-room",
            Self::Cached => "cached",
        }
    }

    /// Whether this mode audits the project's existing build rather than a
    /// freshly reconstructed one.
    fn reuses_existing_build(self) -> bool {
        matches!(self, Self::Cached)
    }
}

/// Bounded concurrency for the two per-group loops. Both are capped by
/// MEMORY, not by cores: a single audit query holds 3.6-3.8 GB RSS even on
/// the smallest sui-system group, and an unbounded fan-out has already been
/// observed to OOM this corpus (`EXIT=137`). The default is deliberately
/// far below the core count.
const QUERY_JOBS_ENV: &str = "SUI_LEAN_AUDIT_QUERY_JOBS";
const ELABORATION_JOBS_ENV: &str = "SUI_LEAN_AUDIT_ELABORATION_JOBS";
const DEFAULT_AUDIT_JOBS: usize = 3;

fn parse_audit_jobs(name: &str, raw: Option<&str>) -> anyhow::Result<usize> {
    let Some(raw) = raw else {
        return Ok(DEFAULT_AUDIT_JOBS);
    };
    let parsed = raw
        .trim()
        .parse::<usize>()
        .with_context(|| format!("{name} must be a positive integer"))?;
    anyhow::ensure!(parsed > 0, "{name} must be at least 1");
    Ok(parsed)
}

fn audit_jobs(name: &str) -> anyhow::Result<usize> {
    let Some(raw) = std::env::var_os(name) else {
        return Ok(DEFAULT_AUDIT_JOBS);
    };
    let raw = raw
        .to_str()
        .with_context(|| format!("{name} is not valid UTF-8"))?;
    parse_audit_jobs(name, Some(raw))
}

/// Either a `TempDir` that deletes on drop, or a leaked path retained for
/// triage under `SUI_LEAN_KEEP_AUDIT_PROJECT`.
enum AuditScratchDir {
    Temporary(tempfile::TempDir),
    Retained(PathBuf),
}

impl AuditScratchDir {
    fn new(purpose: &str) -> anyhow::Result<Self> {
        let temporary =
            tempfile::tempdir().with_context(|| format!("creating {purpose} directory"))?;
        if keep_audit_temporaries() {
            let path = temporary.keep();
            eprintln!("proof audit: retained {purpose} at {}", path.display());
            Ok(Self::Retained(path))
        } else {
            Ok(Self::Temporary(temporary))
        }
    }

    fn path(&self) -> &Path {
        match self {
            Self::Temporary(temporary) => temporary.path(),
            Self::Retained(path) => path.as_path(),
        }
    }
}

/// The clean-room project: a fresh tempdir that never contains a `.lake` when
/// the build starts, so any artifact present afterwards was produced by this
/// run. Only `AuditMode::CleanRoom` builds one.
struct IsolatedAuditProject {
    _temporary: AuditScratchDir,
    root: PathBuf,
}

fn rebase_source_proofs_src_dir(lakefile: &str, overlay_root: &Path) -> anyhow::Result<String> {
    if !lakefile
        .lines()
        .any(|line| line.trim_start().starts_with("lean_lib SourceProofs "))
    {
        return Ok(lakefile.to_string());
    }
    let overlay_root = overlay_root
        .canonicalize()
        .with_context(|| format!("canonicalizing {}", overlay_root.display()))?;
    let mut in_source_proofs = false;
    let mut saw_source_proofs = false;
    let mut replacements = 0usize;
    let lines = lakefile
        .lines()
        .map(|line| {
            let trimmed = line.trim_start();
            if trimmed.starts_with("lean_lib ") {
                in_source_proofs = trimmed.starts_with("lean_lib SourceProofs ");
                saw_source_proofs |= in_source_proofs;
            }
            if in_source_proofs && trimmed.starts_with("srcDir :=") {
                replacements += 1;
                let indentation = &line[..line.len() - trimmed.len()];
                format!(
                    "{indentation}srcDir := {}",
                    lean_string(&overlay_root.to_string_lossy())
                )
            } else {
                line.to_string()
            }
        })
        .collect::<Vec<_>>();
    anyhow::ensure!(
        !saw_source_proofs || replacements == 1,
        "SourceProofs must declare exactly one srcDir for proof-audit isolation"
    );
    Ok(lines.join("\n"))
}

impl IsolatedAuditProject {
    fn new(output_dir: &Path, overlay_root: &Path) -> anyhow::Result<Self> {
        let dependencies = validated_automation_dependencies(output_dir)?;
        let temporary = AuditScratchDir::new("fresh proof-audit project")?;
        let root = temporary.path().join("project");
        std::fs::create_dir_all(&root).context("creating isolated proof-audit root")?;
        for entry in std::fs::read_dir(output_dir)
            .with_context(|| format!("read_dir({})", output_dir.display()))?
        {
            let entry =
                entry.with_context(|| format!("reading entry under {}", output_dir.display()))?;
            let name = entry.file_name();
            if matches!(
                name.to_str(),
                Some(".lake" | "lakefile.lean" | "lake-manifest.json" | "vendor")
            ) {
                continue;
            }
            let source = entry.path();
            let destination = root.join(&name);
            let metadata = std::fs::symlink_metadata(&source)
                .with_context(|| format!("metadata({})", source.display()))?;
            anyhow::ensure!(
                !metadata.file_type().is_symlink(),
                "generated audit project contains a symlink: {}",
                source.display()
            );
            if metadata.is_dir() {
                copy_audit_source_tree(&source, &destination)?;
            } else if metadata.is_file() {
                std::fs::copy(&source, &destination).with_context(|| {
                    format!(
                        "copying generated audit source {} to {}",
                        source.display(),
                        destination.display()
                    )
                })?;
            } else {
                anyhow::bail!("unsupported generated audit entry: {}", source.display());
            }
        }

        let vendor = root.join("vendor");
        let mut isolated_dependencies = BTreeMap::new();
        for (name, source) in &dependencies {
            let (_, folder, _, _) = AUTOMATION_DEPENDENCIES
                .iter()
                .find(|(expected, _, _, _)| expected == name)
                .expect("validated dependency has a pinned specification");
            let destination = vendor.join(folder);
            copy_audit_source_tree(source, &destination)?;
            isolated_dependencies.insert(name.clone(), destination.canonicalize()?);
        }
        if let Some(source) = dependencies.values().next() {
            std::fs::create_dir_all(&vendor)?;
            std::fs::copy(
                source
                    .parent()
                    .context("automation dependency has no vendor parent")?
                    .join("VERSIONS.md"),
                vendor.join("VERSIONS.md"),
            )
            .context("copying automation dependency versions")?;
        }

        let mut lakefile = std::fs::read_to_string(output_dir.join("lakefile.lean"))
            .context("reading generated lakefile for audit isolation")?;
        for (name, directory) in &isolated_dependencies {
            let prefix = format!("require {name} from ");
            let mut count = 0;
            lakefile = lakefile
                .lines()
                .map(|line| {
                    if line.trim().starts_with(&prefix) {
                        count += 1;
                        let directory = lake_path_literal(directory);
                        format!("require {name} from \"{directory}\"")
                    } else {
                        line.to_string()
                    }
                })
                .collect::<Vec<_>>()
                .join("\n");
            anyhow::ensure!(
                count == 1,
                "could not isolate Lake dependency `{name}` in root lakefile"
            );
        }
        lakefile = rebase_source_proofs_src_dir(&lakefile, overlay_root)?;
        lakefile.push('\n');
        std::fs::write(root.join("lakefile.lean"), lakefile)
            .context("writing isolated proof-audit lakefile")?;

        let manifest_path = output_dir.join("lake-manifest.json");
        if manifest_path.is_file() {
            let mut manifest: serde_json::Value = serde_json::from_str(
                &std::fs::read_to_string(&manifest_path)
                    .with_context(|| format!("reading {}", manifest_path.display()))?,
            )
            .with_context(|| format!("parsing {}", manifest_path.display()))?;
            let packages = manifest
                .get_mut("packages")
                .and_then(|value| value.as_array_mut())
                .context("Lake manifest has no mutable package array")?;
            for package in packages {
                let name = package
                    .get("name")
                    .and_then(|value| value.as_str())
                    .context("Lake manifest package has no name")?;
                package["dir"] = serde_json::Value::String(
                    isolated_dependencies
                        .get(name)
                        .with_context(|| format!("unvalidated Lake dependency `{name}`"))?
                        .to_string_lossy()
                        .into_owned(),
                );
            }
            std::fs::write(
                root.join("lake-manifest.json"),
                serde_json::to_vec_pretty(&manifest)
                    .context("serializing isolated Lake manifest")?,
            )
            .context("writing isolated proof-audit Lake manifest")?;
        }
        Ok(Self {
            _temporary: temporary,
            root,
        })
    }
}

/// Lake 4.17 writes root OLeans under `.lake/build/lib`; newer Lake versions
/// use `.lake/build/lib/lean`. `None` before anything has been built.
fn audit_artifact_root(output_dir: &Path) -> Option<PathBuf> {
    [
        output_dir.join(".lake/build/lib/lean"),
        output_dir.join(".lake/build/lib"),
    ]
    .into_iter()
    .find(|path| path.is_dir())
}

/// One audit group's query, staged on disk and waiting to run. `weight` is a
/// scheduling hint only (longest-processing-time-first); nothing depends on
/// its accuracy. `query_dir` must outlive the run -- dropping it deletes the
/// generated `ProofAudit.lean`.
struct PreparedQuery<'a> {
    import: &'a str,
    obligations: &'a [&'a Obligation],
    nonce: String,
    query_dir: AuditScratchDir,
    weight: u64,
}

/// Per-phase cost of the rebuild, for the `[timing]` line. `audit.rs` used
/// to print nothing at all, which left the largest block of the audit's
/// wall clock (the Lake build plus the elaboration loop) indistinguishable
/// after the fact -- both are `lake` subprocesses and nothing in the process
/// tree separates them.
#[derive(Debug, Default)]
struct RebuildTimings {
    deps_build_ms: u128,
    elaborate_ms: u128,
    elaborated: usize,
    reused: usize,
}

/// Resolve, and bounds-check, the OLean path of one audited module beneath
/// the fresh artifact directory.
fn audited_module_artifact(root_artifact_dir: &Path, module: &str) -> anyhow::Result<PathBuf> {
    let artifact = lean_module_file(root_artifact_dir, module, "olean")?;
    std::fs::create_dir_all(
        artifact
            .parent()
            .expect("a Lean module artifact always has a parent"),
    )
    .with_context(|| format!("creating artifact directory for `{module}`"))?;
    let artifact_parent = artifact
        .parent()
        .expect("a Lean module artifact always has a parent")
        .canonicalize()
        .with_context(|| format!("canonicalizing artifact directory for `{module}`"))?;
    anyhow::ensure!(
        artifact_parent.starts_with(root_artifact_dir),
        "audited module artifact directory {} escapes {}",
        artifact_parent.display(),
        root_artifact_dir.display()
    );
    let artifact = artifact_parent.join(
        artifact
            .file_name()
            .expect("a Lean module artifact always has a file name"),
    );
    anyhow::ensure!(
        artifact.starts_with(root_artifact_dir),
        "audited module artifact {} escapes {}",
        artifact.display(),
        root_artifact_dir.display()
    );
    Ok(artifact)
}

/// `--audit-in-place`: bring the project's OWN build up to date, incrementally,
/// and audit that.
///
/// This build is not a formality and must never be skipped. Without it the
/// audit would read whatever OLeans happen to be lying in `.lake` --
/// edit-a-proof, forget-to-rebuild, see-green is the stale-artifact trap in
/// its purest form, and on this project that class of bug has already cost
/// days (an old linked artifact once made a whole corpus render without abort
/// guards and read as client drift). A few seconds of incremental build closes
/// it. `--rehash` is what makes the closure content-based rather than
/// mtime-based: Lake re-hashes sources instead of trusting `.hash` sidecars,
/// so a file restored with an old mtime still invalidates.
///
/// Unlike the clean-room path this asks for the audited modules THEMSELVES
/// (default `leanArts` facet), not just `:deps`, because there is no separate
/// elaboration step -- the in-place artifacts are the ones the query reads.
/// Emitting C here is deliberate: this is the developer's own build directory,
/// their own `lake build` produces the same artifacts, and using a different
/// facet would fight their incremental state instead of sharing it.
async fn build_audit_modules_in_place(
    lake_executable: &Path,
    output_dir: &Path,
    modules: &[(String, PathBuf, PathBuf)],
) -> anyhow::Result<(PathBuf, RebuildTimings)> {
    let started = Instant::now();
    let build = move_prover_lean_backend::run_audit_lake_command(
        lake_executable,
        output_dir,
        ["--reconfigure", "--rehash", "build"],
    )
    .await
    .context("bringing the in-place Lake build up to date before auditing")?;
    let build_ms = started.elapsed().as_millis();
    let stderr = String::from_utf8_lossy(&build.stderr);
    anyhow::ensure!(
        build.status.success() && !stderr.contains(": error") && !stderr.contains("error:"),
        "in-place proof-audit build failed -- the audit refuses to inspect an environment \
         that does not currently compile:\n{}\n{}",
        String::from_utf8_lossy(&build.stdout),
        stderr
    );

    let root_artifact_dir = audit_artifact_root(output_dir)
        .with_context(|| {
            format!(
                "locating the in-place Lean artifact directory under {}",
                output_dir.display()
            )
        })?
        .canonicalize()
        .context("canonicalizing the in-place Lean artifact directory")?;
    // Post-condition: the build must actually have produced every audited
    // module, or the query would silently resolve against nothing.
    for (module, _, _) in modules {
        let artifact = audited_module_artifact(&root_artifact_dir, module)?;
        anyhow::ensure!(
            artifact.is_file(),
            "in-place build did not produce {} for audited module `{module}`",
            artifact.display()
        );
    }
    Ok((
        root_artifact_dir,
        RebuildTimings {
            deps_build_ms: build_ms,
            elaborate_ms: 0,
            elaborated: 0,
            reused: modules.len(),
        },
    ))
}

#[cfg(windows)]
fn lean_cli_path(path: &Path) -> PathBuf {
    let raw = path.to_string_lossy();
    if let Some(rest) = raw.strip_prefix(r"\\?\UNC\") {
        PathBuf::from(format!(r"\\{rest}"))
    } else if let Some(rest) = raw.strip_prefix(r"\\?\") {
        PathBuf::from(rest)
    } else {
        path.to_path_buf()
    }
}

#[cfg(not(windows))]
fn lean_cli_path(path: &Path) -> PathBuf {
    path.to_path_buf()
}

async fn rebuild_audit_modules(
    lake_executable: &Path,
    output_dir: &Path,
    modules: &[(String, PathBuf, PathBuf)],
    elaboration_jobs: usize,
) -> anyhow::Result<(PathBuf, RebuildTimings)> {
    let modules = modules
        .iter()
        .map(|(module, source, source_root)| {
            let source_root = source_root
                .canonicalize()
                .with_context(|| format!("canonicalizing source root for `{module}`"))?;
            anyhow::ensure!(
                source_root.is_dir(),
                "audited module source root is not a directory: {}",
                source_root.display()
            );
            let source = source
                .canonicalize()
                .with_context(|| format!("canonicalizing source for `{module}`"))?;
            anyhow::ensure!(
                source.is_file() && source.starts_with(&source_root),
                "audited module source {} is not a file beneath {}",
                source.display(),
                source_root.display()
            );
            Ok((module.clone(), source, source_root))
        })
        .collect::<anyhow::Result<Vec<_>>>()?;
    // There is deliberately no `lake clean` here any more. It used to run
    // first so that Lake's unqualified `clean` would not recursively delete
    // every path dependency's build directory -- a hazard of auditing IN
    // PLACE. The audit does not audit in place: `IsolatedAuditProject::new`
    // builds a private copy and `copy_audit_source_tree` skips `.lake`, so a
    // clean-room project provably has nothing to clean, and the very next
    // command passes `--reconfigure` regardless. In cached mode cleaning
    // would destroy exactly the artifacts that mode exists to retain.

    // Record which audited targets already had an OLean BEFORE this build.
    // In clean-room mode this is always empty (the copied tree carries no
    // `.lake`), which is what lets the elaboration step below conclude that
    // an OLean present afterwards was produced by THIS build.
    let mut pre_existing_artifacts: BTreeSet<String> = BTreeSet::new();
    if let Some(root) = audit_artifact_root(output_dir) {
        for (module, _, _) in &modules {
            if lean_module_file(&root, module, "olean")?.is_file() {
                pre_existing_artifacts.insert(module.clone());
            }
        }
    }
    anyhow::ensure!(
        pre_existing_artifacts.is_empty(),
        "clean-room proof audit found pre-existing Lake artifacts in {} -- the isolated project \
         must start with no build directory",
        output_dir.display()
    );

    // Lake's default module facet is `leanArts`, which emits an OLean, ILean,
    // and generated C for every audited target. The audit only consumes the
    // OLean. Build all import closures in one Lake invocation, then elaborate
    // the audited sources directly below. A target that is itself in another
    // target's import closure may still be built there with its normal facets.
    //
    // Adding the audited targets themselves to this invocation (`+M:olean`)
    // would fold the elaboration loop into the one parallel build, but it
    // would also undo `d79861fe1 perf(lean): avoid C emission in proof
    // audits`. On the pinned Lake 5.0.0, `Module.oleanFacetConfig` is
    // `fetchOLeanCore "olean" (·.olean)`, which fetches `mod.leanArts`, and
    // `Module.mkArtifacts` sets `c? := mod.cFile` unconditionally: the
    // `olean` facet selects which artifact Lake REPORTS, not which ones it
    // PRODUCES. So the loop stays -- but it runs concurrently, and it skips
    // the targets this same build already produced as somebody's dependency.
    let dependency_targets = modules
        .iter()
        .map(|(module, _, _)| format!("+{module}:deps"))
        .collect::<Vec<_>>();
    let deps_build_started = Instant::now();
    let build = move_prover_lean_backend::run_audit_lake_command(
        lake_executable,
        output_dir,
        ["--reconfigure", "--rehash", "--no-cache", "build"]
            .into_iter()
            .chain(dependency_targets.iter().map(String::as_str)),
    )
    .await
    .context("building audited module dependencies from a clean Lake environment")?;
    let deps_build_ms = deps_build_started.elapsed().as_millis();
    let stderr = String::from_utf8_lossy(&build.stderr);
    anyhow::ensure!(
        build.status.success() && !stderr.contains(": error") && !stderr.contains("error:"),
        "fresh proof-audit dependency build failed:\n{}\n{}",
        String::from_utf8_lossy(&build.stdout),
        stderr
    );

    // Lake 4.17 writes root OLeans under `.lake/build/lib`; newer Lake
    // versions use `.lake/build/lib/lean`. The dependency build above creates
    // exactly the layout selected by the audited project's pinned toolchain.
    let root_artifact_dir = audit_artifact_root(output_dir)
        .with_context(|| {
            format!(
                "locating the fresh proof-audit artifact directory under {}",
                output_dir.display()
            )
        })?
        .canonicalize()
        .context("canonicalizing the fresh proof-audit artifact directory")?;
    anyhow::ensure!(
        root_artifact_dir.is_dir(),
        "fresh proof-audit artifact directory is not a directory: {}",
        root_artifact_dir.display()
    );

    // Split the audited targets into the ones the dependency build already
    // compiled and the ones still to elaborate.
    //
    // Reuse is sound exactly when the OLean was produced by THIS run's build:
    // seven of sui-system's eighteen group modules are in another group
    // module's import closure, so the parallel build above already compiled
    // them -- from the same isolated tree, by the same pinned toolchain,
    // under the same `--no-cache` environment, and with the same
    // "stderr must contain no error" post-condition. Elaborating them a
    // second time recomputes an identical artifact; it proves nothing extra.
    // `pre_existing_artifacts` is what keeps that argument honest: it is
    // asserted empty above, so "the artifact exists now" means "this build
    // just produced it" and nothing else.
    let mut pending = Vec::new();
    let mut reused = 0usize;
    for (module, source, source_root) in &modules {
        let artifact = audited_module_artifact(&root_artifact_dir, module)?;
        if artifact.is_file() {
            reused += 1;
            continue;
        }
        match std::fs::remove_file(&artifact) {
            Ok(()) => {}
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => {}
            Err(error) => {
                return Err(error)
                    .with_context(|| format!("removing stale {}", artifact.display()));
            }
        }
        pending.push((
            module.clone(),
            lean_cli_path(source),
            source_root.clone(),
            artifact,
        ));
    }

    // Each elaboration is an independent `lean` process writing to its own
    // artifact path, so they can run concurrently -- capped by memory, not
    // cores: these are the corpus's heaviest source files.
    let elaborate_started = Instant::now();
    futures::stream::iter(
        pending
            .iter()
            .map(|(module, source, source_root, artifact)| {
                async move {
                    let started = Instant::now();
                    // Lean 4.17 derives the target module name relative to its
                    // process directory and rejects source files outside it. Run from
                    // the owning source root while selecting the isolated Lake
                    // project explicitly.
                    let compile = move_prover_lean_backend::run_audit_lake_command(
                        lake_executable,
                        source_root,
                        [
                            OsStr::new("--dir"),
                            output_dir.as_os_str(),
                            OsStr::new("lean"),
                            source.as_os_str(),
                            OsStr::new("--"),
                            OsStr::new("-o"),
                            artifact.as_os_str(),
                        ],
                    )
                    .await
                    .with_context(|| format!("elaborating audited module `{module}`"))?;
                    let stderr = String::from_utf8_lossy(&compile.stderr);
                    anyhow::ensure!(
                        compile.status.success()
                            && !stderr.contains(": error")
                            && !stderr.contains("error:"),
                        "fresh proof-audit elaboration failed for `{module}`:\n{}\n{}",
                        String::from_utf8_lossy(&compile.stdout),
                        stderr
                    );
                    anyhow::ensure!(
                        artifact.is_file(),
                        "fresh proof-audit elaboration did not emit {}",
                        artifact.display()
                    );
                    eprintln!(
                        "[timing] proof audit elaborate `{module}` took: {}ms",
                        started.elapsed().as_millis()
                    );
                    Ok(())
                }
            }),
    )
    .buffer_unordered(elaboration_jobs)
    .try_collect::<Vec<()>>()
    .await?;
    let elaborate_ms = elaborate_started.elapsed().as_millis();

    Ok((
        root_artifact_dir,
        RebuildTimings {
            deps_build_ms,
            elaborate_ms,
            elaborated: pending.len(),
            reused,
        },
    ))
}

/// Run the audit against `<output_dir>` (an `--generation-mode all`
/// new-pipeline project with an `obligations.toml`). Builds exactly the
/// audited modules in an isolated copy of the project, then executes an
/// isolated direct-Lean environment query over those artifacts.
///
/// `mode` selects only the artifact-provenance regime -- see `AuditMode`.
/// Every check runs identically under both.
pub async fn run_proof_audit(
    output_dir: &Path,
    package_dir: &Path,
    mode: AuditMode,
) -> anyhow::Result<AuditSummary> {
    run_proof_audit_with_statement_budget(
        output_dir,
        package_dir,
        statement_heartbeat_budget()?,
        mode,
    )
    .await
}

async fn run_proof_audit_with_statement_budget(
    output_dir: &Path,
    package_dir: &Path,
    statement_heartbeats: u64,
    mode: AuditMode,
) -> anyhow::Result<AuditSummary> {
    let total_started = Instant::now();
    let preflight_started = Instant::now();
    let elaboration_jobs = audit_jobs(ELABORATION_JOBS_ENV)?;
    let query_jobs = audit_jobs(QUERY_JOBS_ENV)?;
    // Retire any previous report BEFORE anything can fail. `proof_status.toml`
    // is only ever written on the success path, so an audit that dies in its
    // dependency build -- the failure mode a bad merge produces -- used to
    // leave the PREVIOUS run's file in place. That file has already sat
    // showing a green result for hours after an audit that classified zero
    // obligations, twice in this campaign. Absent is unambiguous; stale-green
    // is not. This only ever removes information about a run that is over.
    let status_path = output_dir.join("proof_status.toml");
    match std::fs::remove_file(&status_path) {
        Ok(()) => {}
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => {}
        Err(error) => {
            return Err(error).with_context(|| {
                format!(
                    "retiring the previous {} before auditing",
                    status_path.display()
                )
            });
        }
    }

    let overlay_root = package_dir.join("lean");
    let overlay_snapshot = proof_overlay_snapshot(&overlay_root)?;
    let declared_axioms = load_declared_axioms(package_dir)?;
    reject_reserved_module_collisions(&overlay_root, "proof-overlay")?;
    scan_overlay_for_import_time_execution(&overlay_root)?;
    let manifest_path = output_dir.join("obligations.toml");
    let raw = std::fs::read_to_string(&manifest_path).with_context(|| {
        format!(
            "reading {} -- generate with --new-pipeline first",
            manifest_path.display()
        )
    })?;
    let manifest: Manifest = toml::from_str(&raw).context("parsing obligations.toml")?;
    validate_expected_obligations(output_dir, &manifest)?;

    // Carried verbatim from the manifest, not derived here: the audit
    // sees Lean declarations, and these have none by definition -- the
    // renderer is the only stage that can compare the declared prove
    // roster against what stage 12 actually emitted. Counted on BOTH
    // exits below, including the empty-manifest one: a run whose every
    // prove-spec produced nothing is exactly when the number matters.
    let unproduced_obligations: Vec<ProofStatusUnproducedObligation> = manifest
        .spec_no_obligation
        .iter()
        .map(|row| ProofStatusUnproducedObligation {
            source: row.source.clone(),
            reason: row.reason.clone(),
        })
        .collect();

    if manifest.obligation.is_empty() {
        let summary = AuditSummary {
            spec_no_obligation: unproduced_obligations.len(),
            ..AuditSummary::default()
        };
        write_proof_status(
            &status_path,
            mode,
            &summary,
            Vec::new(),
            Vec::new(),
            unproduced_obligations,
        )?;
        return Ok(summary);
    }

    // Group obligations by the ONE module the audit must load to see
    // their declaration: the exact per-obligation proof shard for prove
    // obligations, and the generated module itself for trusted axioms (the
    // `_holds` axiom lives in that module file). One isolated environment per
    // group keeps repeated bare declaration names unambiguous.
    let mut groups: BTreeMap<String, Vec<&Obligation>> = BTreeMap::new();
    for ob in &manifest.obligation {
        let import = obligation_audit_import(ob)?;
        groups.entry(import).or_default().push(ob);
    }
    for (import, obs) in &groups {
        let mut seen = BTreeSet::new();
        for ob in obs {
            anyhow::ensure!(
                seen.insert(ob.lean_decl.as_str()),
                "obligations.toml: duplicate lean_decl `{}` within audit group `{}`",
                ob.lean_decl,
                import
            );
        }
    }

    let lake_executable = move_prover_lean_backend::resolve_audit_lake_executable(output_dir)
        .await
        .context("resolving the Lake executable selected by the audited project")?;
    scan_generated_sources_for_z3_bypasses(output_dir)?;
    let preflight_elapsed = preflight_started.elapsed();

    let isolate_started = Instant::now();
    if mode.reuses_existing_build() {
        // Printed on EVERY cached run -- which is the default -- immediately
        // above the numbers it produced. This result must not be quoted as
        // verification off a warm cache; stderr is where that warning lives.
        eprintln!(
            "proof audit: MODE=cached (default) -- auditing this project's own Lake build at {}.\n\
             proof audit: every CHECK still runs in full (statement match, sorry, axiom \
             footprint, declaration provenance, overlay snapshot); the build is brought up to \
             date incrementally first, so a forgotten rebuild cannot read as green.\n\
             proof audit: TRUST DELTA vs a clean-room run (--audit-clean-room): nothing is \
             isolated or rebuilt from cold. This reuses the OLeans your build produced, so it \
             trusts Lake's incremental correctness -- exactly what clean-room refuses to trust. \
             It answers \"do my proofs discharge the obligations, assuming the build is \
             current\"; it does NOT answer \"is this corpus verified\" off a warm cache.\n\
             proof audit: this result will be stamped `proof audit [cached]:` and \
             `audit_mode = \"cached\"`. Pass --audit-clean-room for the isolated cold rebuild \
             when you need verification off a warm cache.",
            output_dir.display()
        );
    }
    let isolated_project = match mode {
        AuditMode::CleanRoom => Some(IsolatedAuditProject::new(output_dir, &overlay_root)?),
        AuditMode::Cached => None,
    };
    let audit_output_dir: &Path = match &isolated_project {
        Some(project) => &project.root,
        None => output_dir,
    };
    let smt_trust_is_source_backed =
        pinned_smt_trust_is_source_backed(audit_output_dir, &overlay_root);
    // Build every audited module from a clean root project (a direct Lean
    // query does not build unbuilt imports, and retained OLeans are not
    // authoritative evidence for the current source snapshot). Lake builds
    // all import closures together, then directly elaborates each target to
    // OLean. Lake can still materialize a target's C when another audited
    // target imports it as a dependency.
    let audited_modules = groups
        .iter()
        .map(|(import, obligations)| {
            let all_theorems = obligations
                .iter()
                .all(|obligation| obligation.kind == "theorem");
            let all_trusted_axioms = obligations
                .iter()
                .all(|obligation| obligation.kind == "trusted_axiom");
            anyhow::ensure!(
                all_theorems || all_trusted_axioms,
                "audit group `{import}` mixes proof and trusted-axiom modules"
            );
            let source_root = if all_theorems {
                &overlay_root
            } else {
                audit_output_dir
            };
            let source = lean_module_file(source_root, import, "lean")?;
            anyhow::ensure!(
                source.is_file(),
                "audited module source does not exist: {}",
                source.display()
            );
            Ok((import.clone(), source, source_root.to_path_buf()))
        })
        .collect::<anyhow::Result<Vec<_>>>()?;
    let isolate_elapsed = isolate_started.elapsed();
    let (root_artifact_dir, rebuild) = if mode.reuses_existing_build() {
        build_audit_modules_in_place(&lake_executable, audit_output_dir, &audited_modules).await?
    } else {
        rebuild_audit_modules(
            &lake_executable,
            audit_output_dir,
            &audited_modules,
            elaboration_jobs,
        )
        .await?
    };
    let lean_setup_started = Instant::now();
    let lean_executable =
        move_prover_lean_backend::resolve_audit_lean_executable(&lake_executable, audit_output_dir)
            .await
            .context("resolving the Lean executable used by the audited project")?;
    let artifact_dirs = audit_artifact_directories(audit_output_dir, root_artifact_dir.clone())?;
    let lean_setup_elapsed = lean_setup_started.elapsed();

    // Per-group environment inspection, accumulating a nonce-prefixed protocol
    // emitted by the trusted `ProofAudit.lean` metaprogram (facts read
    // from the real `Environment` -- the untrusted proofs module cannot
    // lie about them):
    //   <nonce>|OB|<lean_decl>|<ok|missing>|<kind>|<declaring module>
    //   <nonce>|ST|<lean_decl>|<exact|conditional|mismatch|prop_missing|unverified>|<extra count>|<reason>
    //   <nonce>|HYP|<lean_decl>|<pretty-printed extra binder>
    //   <nonce>|AX|<lean_decl>|<nd_shape 0|1>|<declaring module>|<axiom>
    //   <nonce>|Z3|<lean_decl>|<oracle marker 0|1>
    //   <nonce>|END|<obligation count>
    // `nd_shape=1` marks an axiom whose TYPE is `@Eq Bool _ Bool.true`
    // (the native_decide synthetic shape) -- checked against the real
    // Environment, not the printed name. `ST` is the statement verdict:
    // the metaprogram compares the resolved declaration's TYPE against
    // the obligation prop's eta-expected statement (both names come from
    // the generator-owned manifest); `conditional` carries one `HYP`
    // line per extra binder (free-form pretty-printed text, LAST field,
    // newline-collapsed -- display-only, never a trust input). `unverified`
    // is the statement check that did not complete inside its own
    // per-obligation heartbeat budget; its `<reason>` is the Lean error,
    // likewise display-only, and the class is fatal. Every other verdict
    // carries `-` there. Keys are
    // (group import, lean_decl), unique by the check above. Non-nonce
    // lines are ignored. Nonce-prefixed rows are parsed fail-closed: labels,
    // enums, uniqueness, HYP counts, and the single terminal END sentinel
    // must all match the generator-owned roster.
    //
    // The groups are mutually independent: each is one `lean` process with
    // its own scratch directory, its own nonce, and its own transcript,
    // joined afterwards on `(group import, lean_decl)`. Nothing is shared,
    // and results land in a `BTreeMap` keyed by import, so completion order
    // is irrelevant. They therefore run concurrently -- but capped by MEMORY
    // rather than by cores (`SUI_LEAN_AUDIT_QUERY_JOBS`, default 3): even
    // sui-system's smallest group peaks at ~3.6 GB RSS holding its imported
    // environment, and an unbounded fan-out on this corpus has already been
    // observed to OOM. Largest-first scheduling keeps the tail short; the
    // weight is only a scheduling hint and nothing depends on its accuracy.
    let query_started = Instant::now();
    let mut prepared = Vec::with_capacity(groups.len());
    for (import, obs) in &groups {
        let nonce = audit_nonce();
        let query_dir = AuditScratchDir::new(&format!("proof-audit query dir for `{import}`"))?;
        let audit_path = query_dir.path().join("ProofAudit.lean");
        std::fs::write(
            &audit_path,
            audit_lean_source(&nonce, &artifact_dirs, import, obs, statement_heartbeats),
        )
        .with_context(|| format!("writing {}", audit_path.display()))?;
        // Fitted cost model from the measured probe:
        // `cpu_s ~ 1.83 + 0.0430*oleanMB + 0.598*obligations`, i.e. one
        // obligation is worth roughly 14 MB of imported OLean.
        let weight = std::fs::metadata(lean_module_file(&root_artifact_dir, import, "olean")?)
            .with_context(|| format!("sizing the built artifact for `{import}`"))?
            .len()
            + (obs.len() as u64) * 14_000_000;
        prepared.push(PreparedQuery {
            import: import.as_str(),
            obligations: obs.as_slice(),
            nonce,
            query_dir,
            weight,
        });
    }
    prepared.sort_by(|left, right| {
        right
            .weight
            .cmp(&left.weight)
            .then_with(|| left.import.cmp(right.import))
    });
    let lean_executable = &lean_executable;
    let query_results = futures::stream::iter(prepared.iter().map(|prepared| async move {
        let import = prepared.import;
        let started = Instant::now();
        let mut attempt = 0usize;
        let out = loop {
            attempt += 1;
            let out = move_prover_lean_backend::run_audit_lean_command(
                lean_executable,
                prepared.query_dir.path(),
                ["ProofAudit.lean"],
            )
            .await
            .context("running isolated direct-Lean proof audit")?;
            if out.status.success()
                || attempt >= 3
                || !out.stdout.is_empty()
                || !out.stderr.is_empty()
            {
                break out;
            }
            eprintln!(
                "proof audit: retrying `{import}` after direct Lean exited with no diagnostic (attempt {attempt}/3)"
            );
        };
        let stdout = String::from_utf8_lossy(&out.stdout).to_string();
        if !out.status.success() {
            anyhow::bail!(
                "ProofAudit.lean (loading {}) failed:\n{}\n{}",
                import,
                stdout,
                String::from_utf8_lossy(&out.stderr)
            );
        }
        let parsed =
            parse_audit_group_output(&prepared.nonce, import, prepared.obligations, &stdout)
                .with_context(|| format!("parsing audit transcript for `{import}`"))?;
        eprintln!(
            "[timing] proof audit query `{import}` took: {}ms (obligations={})",
            started.elapsed().as_millis(),
            prepared.obligations.len()
        );
        Ok((import.to_string(), parsed))
    }))
    .buffer_unordered(query_jobs)
    .try_collect::<Vec<_>>()
    .await?;
    let query_elapsed = query_started.elapsed();
    let mut audit_outputs = BTreeMap::new();
    for (import, parsed) in query_results {
        anyhow::ensure!(
            audit_outputs.insert(import.clone(), parsed).is_none(),
            "duplicate audit output group `{import}`"
        );
    }
    let report_started = Instant::now();
    anyhow::ensure!(
        proof_overlay_snapshot(&overlay_root)? == overlay_snapshot,
        "proof overlay changed while its built Lean environment was audited: {}",
        overlay_root.display()
    );

    // Trusted `_holds` axioms are trusted as a (name, declaring-module)
    // PAIR, not by name alone: a proofs file could otherwise hand-declare
    // an axiom reproducing another module's committed `_holds` name (read
    // from the manifest) and ride on its trust. The genuine `_holds` is
    // emitted by stage 12 into exactly `ob.module`.
    let trusted_pairs: BTreeSet<(&str, &str)> = manifest
        .obligation
        .iter()
        .filter(|ob| ob.kind == "trusted_axiom")
        .map(|ob| (ob.lean_decl.as_str(), ob.module.as_str()))
        .collect();

    let mut summary = AuditSummary::default();
    let declared_names: BTreeSet<&str> = declared_axioms.iter().map(|d| d.name.as_str()).collect();
    let mut declared_used: BTreeSet<String> = BTreeSet::new();
    let mut status_obligations = Vec::with_capacity(manifest.obligation.len());
    for ob in &manifest.obligation {
        let import = obligation_audit_import(ob)?;
        let group_output = audit_outputs
            .get(&import)
            .with_context(|| format!("audit output missing group `{import}`"))?;
        let (is_found, declaration_kind, resolved_module) =
            group_output
                .found
                .get(&ob.lean_decl)
                .with_context(|| format!("audit output missing entry for `{}`", ob.lean_decl))?;
        let mut unexpected: Vec<String> = Vec::new();
        let mut on_declared: Vec<String> = Vec::new();
        let mut on_smt_trusted: Vec<String> = Vec::new();
        let mut extra_hypotheses: Vec<String> = Vec::new();
        let status = if !is_found {
            "missing"
        } else if resolved_module != &import {
            // The bare lean_decl resolved to a homonymous declaration in
            // a DIFFERENT module than the obligation's own proofs/module
            // -- the intended obligation is absent and a same-named decl
            // elsewhere in the import closure was picked up. Never trust
            // that.
            unexpected.push(format!(
                "obligation decl resolved in `{resolved_module}`, expected `{import}`"
            ));
            "suspicious"
        } else if declaration_kind
            != expected_declaration_kind(&ob.kind)
                .expect("manifest kinds were validated while constructing audit groups")
        {
            let expected_kind = expected_declaration_kind(&ob.kind)
                .expect("manifest kinds were validated while constructing audit groups");
            unexpected.push(format!(
                "obligation decl has kind `{declaration_kind}`, expected `{}`",
                expected_kind
            ));
            "suspicious"
        } else {
            let (verdict, _) = group_output
                .statements
                .get(&ob.lean_decl)
                .with_context(|| {
                    format!(
                        "audit output missing statement verdict for `{}`",
                        ob.lean_decl
                    )
                })?;
            let verdict = verdict.as_str();
            anyhow::ensure!(
                verdict != "prop_missing",
                "obligations.toml prop `{}` (obligation `{}`) is absent from the built \
                 environment -- manifest/generator drift",
                ob.prop,
                ob.name
            );
            extra_hypotheses = group_output
                .hypotheses
                .get(&ob.lean_decl)
                .cloned()
                .unwrap_or_default();
            if ob.kind == "trusted_axiom" {
                // Both the prop and the `_holds` axiom are generator-
                // emitted into the same module file; anything but an
                // exact statement match is stale-output drift.
                if verdict == "exact" {
                    "trusted"
                } else if verdict == "unverified" {
                    "statement_unverified"
                } else {
                    unexpected.push(format!(
                        "trusted axiom type does not match the obligation prop `{}`",
                        ob.prop
                    ));
                    "statement_mismatch"
                }
            } else {
                let footprint = group_output
                    .axioms
                    .get(&ob.lean_decl)
                    .cloned()
                    .unwrap_or_default();
                let has_sorry = footprint.iter().any(|(a, _, _)| a == "sorryAx");
                let z3_oracle_attested = group_output
                    .z3_oracle_attested
                    .get(&ob.lean_decl)
                    .copied()
                    .unwrap_or(false);
                for (a, m, nd_shape) in &footprint {
                    if smt_trust_is_source_backed
                        && z3_oracle_attested
                        && a == SMT_TRUSTED_AXIOM
                        && m == SMT_TRUSTED_MODULE
                    {
                        on_smt_trusted.push(a.clone());
                        continue;
                    }
                    if a == "sorryAx"
                        || axiom_allowed(a, m, *nd_shape, &trusted_pairs, &overlay_root)
                    {
                        continue;
                    }
                    if declared_names.contains(a.as_str()) {
                        declared_used.insert(a.clone());
                        on_declared.push(a.clone());
                    } else {
                        unexpected.push(format!("{a} (declared in {m})"));
                    }
                }
                theorem_status(
                    !unexpected.is_empty(),
                    verdict,
                    has_sorry,
                    !on_declared.is_empty(),
                    !on_smt_trusted.is_empty(),
                )
            }
        };
        summary.bump(status);
        status_obligations.push(ProofStatusObligation {
            name: ob.name.clone(),
            module: ob.module.clone(),
            kind: ob.kind.clone(),
            reason: ob.reason.clone(),
            status: status.to_string(),
            statement_note: group_output.statement_notes.get(&ob.lean_decl).cloned(),
            extra_hypotheses,
            declared_axioms: on_declared,
            smt_trusted_axioms: on_smt_trusted,
            unexpected_axioms: unexpected,
        });
    }
    // Stale allowlist entries must stay visible: an axiom that no
    // obligation depends on anymore should be deleted from
    // trusted_axioms.toml, not linger as latent trust.
    let mut warnings = Vec::new();
    for d in &declared_axioms {
        if !declared_used.contains(&d.name) {
            let note = format!(
                "unused trusted_axioms.toml entry `{}` -- delete it or re-justify",
                d.name
            );
            eprintln!("proof audit: WARNING: {note}");
            warnings.push(note);
        }
    }
    summary.spec_no_obligation = unproduced_obligations.len();
    for row in &unproduced_obligations {
        eprintln!(
            "proof audit: NO OBLIGATION EMITTED for declared prove spec `{}`{} -- \
             nothing in the corpus proves it",
            row.source,
            row.reason
                .as_deref()
                .map(|r| format!(" ({r})"))
                .unwrap_or_default()
        );
    }
    write_proof_status(
        &status_path,
        mode,
        &summary,
        warnings,
        status_obligations,
        unproduced_obligations,
    )?;
    let report_elapsed = report_started.elapsed();

    eprintln!(
        "[timing] proof audit took: {}ms (preflight={}ms isolate={}ms deps_build={}ms \
         elaborate={}ms lean_setup={}ms query={}ms report={}ms; groups={} obligations={} \
         elaborated={} artifacts_reused={} elab_jobs={} query_jobs={} mode={})",
        total_started.elapsed().as_millis(),
        preflight_elapsed.as_millis(),
        isolate_elapsed.as_millis(),
        rebuild.deps_build_ms,
        rebuild.elaborate_ms,
        lean_setup_elapsed.as_millis(),
        query_elapsed.as_millis(),
        report_elapsed.as_millis(),
        groups.len(),
        manifest.obligation.len(),
        rebuild.elaborated,
        rebuild.reused,
        elaboration_jobs,
        query_jobs,
        mode.label(),
    );

    Ok(summary)
}

fn validate_expected_obligations(output_dir: &Path, manifest: &Manifest) -> anyhow::Result<()> {
    let path = output_dir.join("expected_obligations.toml");
    let raw = std::fs::read_to_string(&path).with_context(|| {
        format!(
            "reading {} -- regenerate with current sui-lean before auditing",
            path.display()
        )
    })?;
    let expected: ExpectedManifest =
        toml::from_str(&raw).with_context(|| format!("parsing {}", path.display()))?;
    anyhow::ensure!(
        expected.version == 1,
        "{}: unsupported expected-obligation roster version {}",
        path.display(),
        expected.version
    );

    let mut expected_by_source = BTreeMap::new();
    for row in &expected.expected {
        anyhow::ensure!(
            row.obligations
                .iter()
                .all(|name| !name.trim().is_empty() && name.trim() == name),
            "{}: `{}` has a blank or untrimmed obligation name",
            path.display(),
            row.source
        );
        let unique: BTreeSet<_> = row.obligations.iter().collect();
        anyhow::ensure!(
            unique.len() == row.obligations.len(),
            "{}: `{}` has duplicate expected obligation names",
            path.display(),
            row.source
        );
        anyhow::ensure!(
            matches!(row.kind.as_str(), "theorem" | "trusted_axiom"),
            "{}: `{}` has unknown kind `{}`",
            path.display(),
            row.source,
            row.kind
        );
        anyhow::ensure!(
            expected_by_source
                .insert(row.source.as_str(), row)
                .is_none(),
            "{}: duplicate source `{}`",
            path.display(),
            row.source
        );
    }

    let mut actual_by_source: BTreeMap<&str, Vec<&Obligation>> = BTreeMap::new();
    for obligation in &manifest.obligation {
        actual_by_source
            .entry(obligation.source.as_str())
            .or_default()
            .push(obligation);
    }

    let mut failures = Vec::new();
    for (source, obligations) in &actual_by_source {
        if !expected_by_source.contains_key(*source) {
            failures.push(format!(
                "actual source `{source}` is absent from the authoritative roster (obligations: {})",
                obligations
                    .iter()
                    .map(|obligation| obligation.name.as_str())
                    .collect::<Vec<_>>()
                    .join(", ")
            ));
        }
    }
    for (source, row) in expected_by_source {
        let actual = actual_by_source
            .get(source)
            .map(Vec::as_slice)
            .unwrap_or(&[]);
        let mut expected_names = row.obligations.clone();
        expected_names.sort();
        let mut actual_names: Vec<_> = actual
            .iter()
            .map(|obligation| obligation.ir_name.clone())
            .collect();
        actual_names.sort();
        if actual_names != expected_names {
            failures.push(format!(
                "`{source}` expected obligations {:?}, found {:?}",
                expected_names, actual_names
            ));
        }
        for obligation in actual {
            if obligation.target_source != row.target {
                failures.push(format!(
                    "`{source}` expected target `{}`, found `{}` on `{}`",
                    row.target, obligation.target_source, obligation.name
                ));
            }
            if obligation.kind != row.kind {
                failures.push(format!(
                    "`{source}` expected kind `{}`, found `{}` on `{}`",
                    row.kind, obligation.kind, obligation.name
                ));
            }
            if row.kind == "trusted_axiom" && obligation.reason != row.reason {
                failures.push(format!(
                    "`{source}` expected trust reason {:?}, found {:?} on `{}`",
                    row.reason, obligation.reason, obligation.name
                ));
            }
        }
    }
    anyhow::ensure!(
        failures.is_empty(),
        "proof obligation manifest is incomplete or misclassified:\n  - {}",
        failures.join("\n  - ")
    );
    Ok(())
}

fn native_decide_axiom_name(name: &str) -> bool {
    let components = name.split('.').collect::<Vec<_>>();
    if components.len() < 4
        || components[components.len() - 3] != "_native"
        || components[components.len() - 2] != "native_decide"
    {
        return false;
    }
    let Some(indices) = components[components.len() - 1].strip_prefix("ax_") else {
        return false;
    };
    let indices = indices.split('_').collect::<Vec<_>>();
    indices.len() == 2
        && indices
            .iter()
            .all(|index| !index.is_empty() && index.bytes().all(|byte| byte.is_ascii_digit()))
}

fn axiom_allowed(
    name: &str,
    declared_in: &str,
    nd_shape: bool,
    trusted_pairs: &BTreeSet<(&str, &str)>,
    overlay_root: &Path,
) -> bool {
    LEAN_CORE_AXIOMS.contains(&name)
        // `native_decide` materializes one compiler-generated synthetic
        // axiom per call site (`<decl>._native.native_decide.ax_N_M`).
        // Trust it only when its Environment type is `@Eq Bool _ Bool.true`
        // and the name has the exact pinned compiler suffix. The complete
        // generated + overlay source scan independently rejects every
        // hand-authored `axiom` that mentions this reserved namespace.
        || (nd_shape && native_decide_axiom_name(name))
        // Trusted `_holds` axioms: match the (name, declaring-module)
        // PAIR from the manifest so a reproduced name in the wrong module
        // is not trusted.
        || trusted_pairs.contains(&(name, declared_in))
        || (TRUSTED_LIB_ROOTS
            .iter()
            .any(|root| declared_in == *root || declared_in.starts_with(&format!("{root}.")))
            // Module NAMES don't certify origin: a proof-overlay file at
            // `lean/Sui/X.lean` gets module name `Sui.X` and would
            // otherwise inherit lemma-base trust. Lib-root trust applies
            // only when the module does NOT resolve to a file under the
            // package's own overlay.
            && !module_file_in_overlay(declared_in, overlay_root))
}

/// True iff Lean module `module` corresponds to a `.lean` file under the
/// package's proof overlay (`<package-root>/lean/`) -- i.e. it is
/// user-tree code regardless of what its name claims.
fn module_file_in_overlay(module: &str, overlay_root: &Path) -> bool {
    let mut path = overlay_root.to_path_buf();
    for comp in module.split('.') {
        path.push(comp);
    }
    path.set_extension("lean");
    path.is_file()
}

fn lean_module_file(root: &Path, module: &str, extension: &str) -> anyhow::Result<PathBuf> {
    let mut path = root.to_path_buf();
    let components = name_components(module);
    anyhow::ensure!(!components.is_empty(), "Lean module name is empty");
    for component in components {
        let path_component = Path::new(&component);
        let mut path_components = path_component.components();
        let Some(std::path::Component::Normal(component)) = path_components.next() else {
            anyhow::bail!("Lean module `{module}` has unsafe path component");
        };
        anyhow::ensure!(
            path_components.next().is_none(),
            "Lean module `{module}` has unsafe path component"
        );
        path.push(component);
    }
    path.set_extension(extension);
    Ok(path)
}

fn dependency_source_digest(root: &Path) -> anyhow::Result<String> {
    fn collect(root: &Path, directory: &Path, paths: &mut Vec<PathBuf>) -> anyhow::Result<()> {
        let mut entries = std::fs::read_dir(directory)
            .with_context(|| format!("read_dir({})", directory.display()))?
            .collect::<Result<Vec<_>, _>>()
            .with_context(|| format!("reading {}", directory.display()))?;
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
            let metadata = std::fs::symlink_metadata(&path)
                .with_context(|| format!("metadata({})", path.display()))?;
            if metadata.is_dir() {
                collect(root, &path, paths)?;
            } else if metadata.is_file() || metadata.file_type().is_symlink() {
                paths.push(path);
            } else {
                anyhow::bail!("unsupported dependency entry: {}", path.display());
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
        let metadata = std::fs::symlink_metadata(&path)
            .with_context(|| format!("metadata({})", path.display()))?;
        let (kind, payload) = if metadata.file_type().is_symlink() {
            (
                b'L',
                std::fs::read_link(&path)
                    .with_context(|| format!("read_link({})", path.display()))?
                    .to_string_lossy()
                    .replace('\\', "/")
                    .into_bytes(),
            )
        } else {
            (
                b'F',
                std::fs::read(&path).with_context(|| format!("read {}", path.display()))?,
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

fn is_lake_require_line(line: &str) -> bool {
    line.split_whitespace().next() == Some("require")
}

fn lake_path_literal(path: &Path) -> String {
    path.to_string_lossy()
        .replace('\\', "/")
        .replace('"', "\\\"")
}

fn validated_automation_dependencies(
    output_dir: &Path,
) -> anyhow::Result<BTreeMap<String, PathBuf>> {
    let root_lakefile = std::fs::read_to_string(output_dir.join("lakefile.lean"))
        .context("reading root lakefile.lean")?;
    let has_require = root_lakefile.lines().any(is_lake_require_line);
    let manifest_path = output_dir.join("lake-manifest.json");
    let manifest_source = match std::fs::read_to_string(&manifest_path) {
        Ok(source) => source,
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => {
            anyhow::ensure!(
                !has_require,
                "Lake manifest is required when lakefile.lean declares dependencies"
            );
            return Ok(BTreeMap::new());
        }
        Err(error) => {
            return Err(error).with_context(|| format!("reading {}", manifest_path.display()));
        }
    };
    let manifest: serde_json::Value = serde_json::from_str(&manifest_source)
        .with_context(|| format!("parsing {}", manifest_path.display()))?;
    let manifest_version = manifest
        .get("version")
        .and_then(|value| value.as_str())
        .context("Lake manifest has no version")?;
    let packages = manifest
        .get("packages")
        .and_then(|value| value.as_array())
        .context("Lake manifest has no package array")?;
    if packages.is_empty() {
        anyhow::ensure!(
            !has_require,
            "Lake manifest is missing dependencies declared by lakefile.lean"
        );
        anyhow::ensure!(
            matches!(manifest_version, "1.1.0" | "1.2.0"),
            "dependency-free Lake manifest must use schema 1.1.0 or 1.2.0"
        );
        return Ok(BTreeMap::new());
    }
    anyhow::ensure!(
        manifest_version == "1.2.0",
        "Lake manifest with automation dependencies must use schema 1.2.0"
    );
    anyhow::ensure!(
        packages.len() == AUTOMATION_DEPENDENCIES.len(),
        "Lake manifest must contain exactly the pinned automation dependency set"
    );
    anyhow::ensure!(
        root_lakefile
            .lines()
            .filter(|line| is_lake_require_line(line))
            .count()
            == AUTOMATION_DEPENDENCIES.len(),
        "root lakefile must contain exactly the pinned automation requirement set"
    );
    let mut dependencies = BTreeMap::new();
    for (name, folder, config, expected_digest) in AUTOMATION_DEPENDENCIES {
        let matches = packages
            .iter()
            .filter(|package| package.get("name").and_then(|value| value.as_str()) == Some(name))
            .collect::<Vec<_>>();
        anyhow::ensure!(
            matches.len() == 1,
            "Lake manifest must contain exactly one `{name}` dependency"
        );
        let package = matches[0];
        anyhow::ensure!(
            package.get("type").and_then(|value| value.as_str()) == Some("path")
                && package.get("configFile").and_then(|value| value.as_str()) == Some(config)
                && package.get("manifestFile").and_then(|value| value.as_str())
                    == Some("lake-manifest.json")
                && package.get("url").is_none(),
            "Lake dependency `{name}` is not the pinned offline path dependency"
        );
        let raw_directory = package
            .get("dir")
            .and_then(|value| value.as_str())
            .with_context(|| format!("Lake dependency `{name}` has no directory"))?;
        let raw_path = Path::new(raw_directory);
        anyhow::ensure!(
            !std::fs::symlink_metadata(raw_path)
                .map(|metadata| metadata.file_type().is_symlink())
                .unwrap_or(true),
            "Lake dependency `{name}` is a symlink or missing"
        );
        let directory = raw_path
            .canonicalize()
            .with_context(|| format!("canonicalizing Lake dependency `{name}`"))?;
        anyhow::ensure!(
            directory.file_name().and_then(|value| value.to_str()) == Some(folder)
                && directory.join(config).is_file()
                && directory.join("lake-manifest.json").is_file(),
            "Lake dependency `{name}` does not use complete vendored `{folder}` sources"
        );
        anyhow::ensure!(
            dependency_source_digest(&directory)? == expected_digest,
            "Lake dependency `{name}` does not match its pinned source digest"
        );
        let require = format!("require {name} from \"{}\"", lake_path_literal(&directory));
        anyhow::ensure!(
            root_lakefile
                .lines()
                .filter(|line| line.trim() == require)
                .count()
                == 1,
            "root lakefile does not contain the exact local `{name}` requirement"
        );
        anyhow::ensure!(
            dependencies.insert(name.to_string(), directory).is_none(),
            "duplicate Lake dependency `{name}`"
        );
    }
    let vendor_roots = dependencies
        .values()
        .filter_map(|directory| directory.parent())
        .collect::<BTreeSet<_>>();
    anyhow::ensure!(
        vendor_roots.len() == 1
            && vendor_roots
                .first()
                .is_some_and(|root| root.join("VERSIONS.md").is_file()),
        "automation dependencies do not share a versioned vendor root"
    );
    let auto_lakefile = std::fs::read_to_string(dependencies["auto"].join("lakefile.lean"))
        .context("reading vendored lean-auto lakefile")?;
    anyhow::ensure!(
        auto_lakefile.contains("precompileModules := false")
            && auto_lakefile.contains("preferReleaseBuild := false")
            && !auto_lakefile.contains("zipperpositionAutoDownload"),
        "vendored lean-auto still enables an external download or release build"
    );
    Ok(dependencies)
}

fn pinned_smt_trust_is_source_backed(output_dir: &Path, overlay_root: &Path) -> bool {
    if module_file_in_overlay(SMT_TRUSTED_MODULE, overlay_root)
        || module_file_in_overlay(SMT_TRUSTED_MODULE, output_dir)
    {
        return false;
    }
    pinned_move_auto_sources(output_dir)
        && validated_automation_dependencies(output_dir)
            .is_ok_and(|dependencies| dependencies.contains_key("auto"))
}

/// Components of a dotted Lean declaration name, guillemets stripped:
/// the metaprogram rebuilds the `Name` via `Name.mkStr` from RAW atoms
/// (a `String.toName` on `Pkg.«matches»` would keep the guillemets in
/// the atom and miss the real declaration).
fn name_components(decl: &str) -> Vec<String> {
    decl.split('.')
        .map(|c| {
            c.trim_start_matches('\u{ab}')
                .trim_end_matches('\u{bb}')
                .to_string()
        })
        .collect()
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

fn lean_name_array(name: &str) -> String {
    name_components(name)
        .iter()
        .map(|component| lean_string(component))
        .collect::<Vec<_>>()
        .join(", ")
}

fn audit_artifact_directories(
    output_dir: &Path,
    root_artifact_dir: PathBuf,
) -> anyhow::Result<Vec<PathBuf>> {
    let mut directories = vec![root_artifact_dir];
    // Every vendored automation dependency is source-pinned and digest-verified
    // by `validated_automation_dependencies` on every audit, whether or not the
    // audited modules import it. Artifacts, however, exist only for the ones the
    // fresh build actually reached, and that build compiles the audited module
    // targets alone: an overlay that imports nothing from the automation layer
    // (integer-mate, stl, sui-system) leaves Aesop and lean-auto unbuilt.
    // Demanding artifacts unconditionally failed those projects closed for no
    // reason. Skipping an unbuilt dependency is safe because the audit query
    // runs a bare `lean` with a sanitized environment (no `LEAN_PATH`): the
    // search path is exactly this list, so a module that DOES import a
    // dependency whose artifacts are missing fails to load and the audit reports
    // the failure -- it can never silently resolve against unverified oleans.
    for (name, directory) in validated_automation_dependencies(output_dir)? {
        let Some(artifact) = [
            directory.join(".lake/build/lib/lean"),
            directory.join(".lake/build/lib"),
        ]
        .into_iter()
        .find(|path| path.is_dir()) else {
            continue;
        };
        let artifact = artifact.canonicalize().with_context(|| {
            format!("canonicalizing Lean artifacts for path dependency `{name}`")
        })?;
        if !directories.contains(&artifact) {
            directories.push(artifact);
        }
    }
    Ok(directories)
}

fn audit_lean_source(
    nonce: &str,
    artifact_dirs: &[PathBuf],
    import: &str,
    obligations: &[&Obligation],
    statement_heartbeats: u64,
) -> String {
    let mut src = format!(
        "-- Generated by sui-lean --audit-proofs; regenerated every audit run.\n\
         import Lean\n\n{}\n",
        include_str!("z3_attestation_query.lean")
    );
    // Statement checks (`isDefEq` against big generated props) can chew
    // through the default elaboration budget on mismatching telescopes. The
    // file-level budget bounds the surrounding command; the per-obligation
    // budget the statement check actually runs under is rebased below.
    src.push_str("\nset_option maxHeartbeats 0\nset_option maxRecDepth 100000\n");
    let module_comps = lean_name_array(import);
    let z3_oracle_marker = lean_name_array(SMT_ORACLE_MARKER);
    let z3_explicit_marker = lean_name_array(SMT_EXPLICIT_MARKER);
    let smt_oracle = lean_name_array(SMT_TRUSTED_AXIOM);
    let artifact_search_path = artifact_dirs
        .iter()
        .map(|path| {
            format!(
                "System.FilePath.mk {}",
                lean_string(&path.to_string_lossy())
            )
        })
        .collect::<Vec<_>>()
        .join(", ");
    src.push_str(&format!(
        "\nopen Lean Meta in\nrun_cmd Lean.Elab.Command.liftTermElabM do\n  \
         Lean.searchPathRef.modify fun paths => paths ++ [{artifact_search_path}]\n  \
         let nonce := {}\n  \
         let stHeartbeats := {statement_heartbeats}\n  \
         let moduleName := #[{module_comps}].foldl \
         (fun acc c => Lean.Name.mkStr acc c) Lean.Name.anonymous\n  \
         let z3OracleMarker := #[{z3_oracle_marker}].foldl \
         (fun acc c => Lean.Name.mkStr acc c) Lean.Name.anonymous\n  \
         let z3ExplicitMarker := #[{z3_explicit_marker}].foldl \
         (fun acc c => Lean.Name.mkStr acc c) Lean.Name.anonymous\n  \
         let smtOracle := #[{smt_oracle}].foldl \
         (fun acc c => Lean.Name.mkStr acc c) Lean.Name.anonymous\n  \
         let decls : Array (String \u{d7} Array String \u{d7} Array String \u{d7} Array String) := #[\n",
        lean_string(nonce),
    ));
    let entries: Vec<String> = obligations
        .iter()
        .map(|ob| {
            let namespace = if ob.kind == "theorem" {
                format!("{}_Proofs", ob.module)
            } else {
                ob.module.clone()
            };
            format!(
                "    ({}, #[{}], #[{}], #[{}])",
                lean_string(&ob.lean_decl),
                lean_name_array(&ob.lean_decl),
                lean_name_array(&namespace),
                lean_name_array(&ob.prop)
            )
        })
        .collect();
    src.push_str(&entries.join(",\n"));
    src.push_str(
        "\n  ]\n  let options \u{2190} getOptions\n  \
         Lean.withImportModules #[{ module := moduleName }] {} (act := fun env => do\n    \
         let _ \u{2190} Lean.Core.CoreM.toIO\n      \
         (ctx := { fileName := \"\", fileMap := default, options })\n      \
         (s := { env }) do\n      \
         Lean.Meta.MetaM.run' do\n",
    );
    // Body emits facts read from the REAL Environment (module of the
    // resolved obligation decl; the statement verdict of the decl's TYPE
    // against the prop's eta-expected statement; per-axiom declaring
    // module + whether its type is `@Eq Bool _ Bool.true`, the
    // native_decide synthetic shape). Every line is nonce-prefixed and a
    // final END sentinel bounds the stream; the Rust side ignores any
    // other output.
    //
    // Statement verdicts: `exact` -- the decl's type isDefEq the
    // eta-expected `forall xs, <prop> xs` (rebuilt with the prop def's
    // own binders, so binder-KIND differences don't matter: defeq
    // ignores binder info). `conditional` -- the decl's telescoped
    // conclusion is the prop applied to an in-order subset of its
    // binders (argument-wise fvar/defeq match, full prop arity); the
    // unconsumed binders are the extra hypotheses, reported as HYP
    // lines. Anything else -- including the impossible-by-construction
    // "all binders consumed yet not exact" state -- is `mismatch`.
    let body = r##"  -- `oracleReach` is a pure function of a FIXED environment: `withImportModules`
  -- hands this whole query one immutable `Environment`, so whether a name's
  -- `collectAxioms` closure reaches the Z3 oracle cannot change between
  -- obligations, and the memo is carried across the loop instead of being
  -- rebuilt 522 times.
  --
  -- `seen` is NOT carried. It records "already visited (name, context)" and
  -- makes the second visit return the NEUTRAL attestation, which is sound
  -- only within one traversal: sharing it across obligations would let one
  -- obligation's walk suppress the evidence another obligation's walk must
  -- see. It is re-initialised empty on every iteration below.
  let mut oracleReach : NameMap Bool := {}
  for (label, comps, namespaceComps, propComps) in decls do
    let bare := comps.foldl (fun acc c => Name.mkStr acc c) Name.anonymous
    -- Shard layout: the source module is the exact obligation shard, while
    -- declarations remain in the parent `<generated module>_Proofs`
    -- namespace. Prefer that declaration and retain the bare-name fallback
    -- for legacy declarations while manifests transition.
    let declarationNamespace :=
      namespaceComps.foldl (fun acc c => Name.mkStr acc c) Name.anonymous
    let qualified := comps.foldl (fun acc c => Name.mkStr acc c) declarationNamespace
    let declaredHere := fun (nm : Name) => match env.getModuleIdxFor? nm with
      | some idx => env.allImportedModuleNames[idx.toNat]! == moduleName
      | none => false
    let n := if (env.find? qualified).isSome && declaredHere qualified then qualified else bare
    match env.find? n with
    | none => IO.println s!"{nonce}|OB|{label}|missing|-|-"
    | some info =>
      let obMod := match env.getModuleIdxFor? n with
        | some idx => toString env.allImportedModuleNames[idx.toNat]!
        | none => "_current"
      let obKind := match info with
        | .defnInfo value => if value.hints.isAbbrev then "abbrev" else "def"
        | .opaqueInfo _ => "opaque"
        | .thmInfo _ => "theorem"
        | .axiomInfo _ => "axiom"
        | _ => "other"
      IO.println s!"{nonce}|OB|{label}|ok|{obKind}|{obMod}"
      -- Fresh `seen`, carried-over `oracleReach` (see the note above the loop).
      let (z3Evidence, z3State) ←
        (inspectZ3Decl z3OracleMarker z3ExplicitMarker smtOracle n 0).run
          { seen := {}, oracleReach := oracleReach }
      oracleReach := z3State.oracleReach
      let z3Oracle :=
        if z3Evidence.used && z3Evidence.valid then "1" else "0"
      IO.println s!"{nonce}|Z3|{label}|{z3Oracle}"
      let propName := propComps.foldl (fun acc c => Name.mkStr acc c) Name.anonymous
      let classifyStatement : MetaM (String × Array String) := do
        match env.find? propName with
        | none => pure ("prop_missing", (#[] : Array String))
        | some propInfo =>
          let propConst := mkConst propName (propInfo.levelParams.map Level.param)
          let (expected, propArity) ← forallTelescope propInfo.type fun xs _ => do
            pure (← mkForallFVars xs (mkAppN propConst xs), xs.size)
          let declType ← instantiateMVars info.type
          let expected ← instantiateMVars expected
          -- Cheapest sufficient check first. `BEq Expr` is alpha equivalence
          -- and `withReducible` restricts delta to `@[reducible]` definitions.
          -- Each fast path only ever ACCEPTS, and alpha-equal or
          -- reducibly-defeq types ARE definitionally equal, so a fast path can
          -- make an `exact` verdict cheap but can never manufacture one; a
          -- failure just falls through to the full check. Overlay theorems
          -- that restate the generated prop verbatim -- the common case --
          -- settle on the first line instead of delta-reducing the prop's
          -- whole abort tree.
          if declType == expected then
            pure ("exact", (#[] : Array String))
          else if ← withReducible (isDefEq declType expected) then
            pure ("exact", (#[] : Array String))
          else if ← isDefEq declType expected then
            pure ("exact", (#[] : Array String))
          else
            forallTelescope declType fun ys concl => do
              if concl.getAppFn.isConstOf propName then
                let args := concl.getAppArgs
                let mut ai := 0
                let mut extras : Array String := #[]
                for y in ys do
                  let matched ← do
                    if h : ai < args.size then
                      if args[ai] == y then pure true else isDefEq args[ai] y
                    else
                      pure false
                  if matched then
                    ai := ai + 1
                  else
                    let yName ← y.fvarId!.getUserName
                    let yTy ← inferType y
                    let yTyStr := toString (← ppExpr yTy)
                    extras := extras.push s!"{yName} : {yTyStr}"
                if ai == args.size && args.size == propArity && !extras.isEmpty then
                  pure ("conditional", extras)
                else
                  pure ("mismatch", (#[] : Array String))
              else
                pure ("mismatch", (#[] : Array String))
      -- `withCurrHeartbeats` rebases the deterministic-timeout budget on this
      -- obligation, so one expensive statement cannot spend the group's
      -- allowance and abort every obligation after it. The statement check is
      -- the only step here that consults the budget at all (`isDefEq`, `whnf`,
      -- `inferType`, `ppExpr`); an exhausted or otherwise failed check is
      -- recorded as `unverified` for THIS obligation and the group continues.
      -- `unverified` never passes: the Rust side counts it as its own fatal
      -- class, so a check that did not complete can never read as proven.
      -- `tryCatchRuntimeEx`, not `tryCatch`: the ordinary handler in every
      -- CoreM-based monad deliberately RE-THROWS resource-limit exceptions, so
      -- a plain `tryCatch` here would silently let the timeout kill the run.
      -- `tryCatchRuntimeEx` still refuses to catch interrupts.
      let stSaved ← saveState
      let stOutcome ← tryCatchRuntimeEx
        (do
          let (v, e) ← withTheReader Lean.Core.Context
            (fun ctx => { ctx with maxHeartbeats := stHeartbeats })
            (withCurrHeartbeats classifyStatement)
          pure (v, e, "-"))
        (fun ex => do
          stSaved.restore
          let reason := (← (← addMessageContext ex.toMessageData).toString).replace "\n" " "
          pure ("unverified", (#[] : Array String), reason))
      let verdict := stOutcome.1
      let extras := stOutcome.2.1
      IO.println s!"{nonce}|ST|{label}|{verdict}|{extras.size}|{stOutcome.2.2}"
      for hyp in extras do
        let clean := hyp.replace "\n" " "
        IO.println s!"{nonce}|HYP|{label}|{clean}"
      let axs ← Lean.collectAxioms n
      for a in axs do
        let m := match env.getModuleIdxFor? a with
          | some idx => toString env.allImportedModuleNames[idx.toNat]!
          | none => "_current"
        let ndShape := match env.find? a with
          | some (.axiomInfo v) =>
            if v.type.isAppOfArity ``Eq 3 then
              let args := v.type.getAppArgs
              if args[0]!.isConstOf ``Bool && args[2]!.isConstOf ``Bool.true then "1" else "0"
            else "0"
          | _ => "0"
        IO.println s!"{nonce}|AX|{label}|{ndShape}|{m}|{a}"
  IO.println s!"{nonce}|END|{decls.size}"
"##;
    for line in body.lines() {
        src.push_str("      ");
        src.push_str(line);
        src.push('\n');
    }
    src.push_str("  )\n");
    src
}

#[cfg(test)]
mod tests {
    use super::*;

    fn write_bundle_file(root: &Path, relative: &str, contents: &[u8]) {
        let path = root.join(relative);
        std::fs::create_dir_all(path.parent().unwrap()).unwrap();
        std::fs::write(path, contents).unwrap();
    }

    #[test]
    fn theorem_audit_import_targets_the_exact_proof_shard() {
        let obligation = Obligation {
            name: "escaped_name".to_string(),
            ir_name: "9-bad/name".to_string(),
            kind: "theorem".to_string(),
            reason: None,
            module: "Pkg.Math".to_string(),
            prop: "Pkg.Math.escaped_name".to_string(),
            lean_decl: "escaped_name".to_string(),
            target: "Pkg.Target.f".to_string(),
            target_source: "Pkg::target::f".to_string(),
            source: "Pkg::math::f_spec".to_string(),
        };

        assert_eq!(
            obligation_audit_import(&obligation).unwrap(),
            "Pkg.Math_Proofs._9_bad_name"
        );
    }

    #[test]
    fn lake_dependency_paths_use_the_renderer_literal_format() {
        assert_eq!(
            lake_path_literal(Path::new(r"\\?\E:\vendor\batteries")),
            "//?/E:/vendor/batteries"
        );
    }

    #[test]
    fn lemma_bundle_comparison_reports_every_verdict() {
        let embedded: [(&str, &[u8]); 3] = [
            ("Prelude/Same.lean", b"same\n"),
            ("Prelude/Drifted.lean", b"pinned\n"),
            ("natives/Sui/Absent.lean", b"pinned\n"),
        ];
        let bundle = tempfile::tempdir().unwrap();
        write_bundle_file(bundle.path(), "Prelude/Same.lean", b"same\n");
        write_bundle_file(bundle.path(), "Prelude/Drifted.lean", b"edited\n");
        write_bundle_file(bundle.path(), "natives/Sui/Unpinned.lean", b"new\n");

        let comparison = compare_lemma_bundle(&embedded, bundle.path()).unwrap();

        assert_eq!(comparison.matched, vec!["Prelude/Same.lean".to_string()]);
        assert_eq!(
            comparison.mismatched,
            vec!["Prelude/Drifted.lean".to_string()]
        );
        assert_eq!(
            comparison.missing,
            vec!["natives/Sui/Absent.lean".to_string()]
        );
        assert_eq!(
            comparison.extra,
            vec!["natives/Sui/Unpinned.lean".to_string()]
        );
    }

    #[test]
    fn lemma_bundle_verification_names_the_bundle_and_every_bad_file() {
        let embedded: [(&str, &[u8]); 2] = [
            ("Prelude/Drifted.lean", b"pinned\n"),
            ("natives/Sui/Absent.lean", b"pinned\n"),
        ];
        let bundle = tempfile::tempdir().unwrap();
        write_bundle_file(bundle.path(), "Prelude/Drifted.lean", b"edited\n");

        let comparison = compare_lemma_bundle(&embedded, bundle.path()).unwrap();
        let mismatched = render_bundle_file_list("mismatched", &comparison.mismatched);
        let missing = render_bundle_file_list("missing", &comparison.missing);

        assert!(mismatched.contains("Prelude/Drifted.lean"), "{mismatched}");
        assert!(missing.contains("natives/Sui/Absent.lean"), "{missing}");
        assert!(render_bundle_file_list("mismatched", &[]).is_empty());
    }

    #[cfg(unix)]
    #[test]
    fn lemma_bundle_treats_a_substituted_symlink_as_a_mismatch() {
        let embedded: [(&str, &[u8]); 1] = [("Prelude/Pinned.lean", b"pinned\n")];
        let bundle = tempfile::tempdir().unwrap();
        write_bundle_file(bundle.path(), "elsewhere.lean", b"pinned\n");
        std::fs::create_dir_all(bundle.path().join("Prelude")).unwrap();
        std::os::unix::fs::symlink(
            bundle.path().join("elsewhere.lean"),
            bundle.path().join("Prelude").join("Pinned.lean"),
        )
        .unwrap();

        let comparison = compare_lemma_bundle(&embedded, bundle.path()).unwrap();

        assert_eq!(
            comparison.mismatched,
            vec!["Prelude/Pinned.lean".to_string()]
        );
        assert!(comparison.matched.is_empty());
    }

    #[test]
    fn lemma_bundle_skips_build_output_and_the_vendor_trust_surface() {
        let embedded: [(&str, &[u8]); 0] = [];
        let bundle = tempfile::tempdir().unwrap();
        write_bundle_file(bundle.path(), ".lake/build/lib/Stale.olean", b"binary");
        write_bundle_file(bundle.path(), "vendor/batteries/lakefile.toml", b"vendored");
        write_bundle_file(bundle.path(), "Prelude/Real.lean", b"real\n");

        let comparison = compare_lemma_bundle(&embedded, bundle.path()).unwrap();

        assert_eq!(comparison.extra, vec!["Prelude/Real.lean".to_string()]);
    }

    #[test]
    fn the_embedded_manifest_is_the_whole_shipped_bundle() {
        let bundle = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .unwrap()
            .join("lean-pipeline/lemmas");
        assert!(
            LEMMA_BUNDLE_FILES.len() >= 60,
            "the embedded bundle shrank to {} files",
            LEMMA_BUNDLE_FILES.len()
        );
        for (bundle_relative, _) in PINNED_OUTPUT_SOURCES {
            assert!(
                embedded_lemma_source(bundle_relative).is_some(),
                "{bundle_relative} is not in the embedded manifest"
            );
        }
        let comparison = compare_lemma_bundle(LEMMA_BUNDLE_FILES, &bundle).unwrap();
        assert_eq!(comparison.matched.len(), LEMMA_BUNDLE_FILES.len());
        assert!(comparison.mismatched.is_empty() && comparison.missing.is_empty());
        assert!(comparison.extra.is_empty(), "{:?}", comparison.extra);
        verify_pinned_lemma_bundle(&bundle).unwrap();
    }

    #[test]
    fn lean_toolchain_comparison_reports_every_verdict() {
        let project = tempfile::tempdir().unwrap();
        assert_eq!(
            compare_lean_toolchain(project.path()).unwrap(),
            ToolchainVerdict::Missing
        );

        std::fs::write(
            project.path().join("lean-toolchain"),
            "leanprover/lean4:v4.31.0\n",
        )
        .unwrap();
        assert_eq!(
            compare_lean_toolchain(project.path()).unwrap(),
            ToolchainVerdict::Mismatched("leanprover/lean4:v4.31.0\n".to_string())
        );

        std::fs::write(
            project.path().join("lean-toolchain"),
            lean_pipeline::render::GENERATED_LEAN_TOOLCHAIN,
        )
        .unwrap();
        assert_eq!(
            compare_lean_toolchain(project.path()).unwrap(),
            ToolchainVerdict::Matched
        );
    }

    #[test]
    fn lean_toolchain_verification_names_expected_found_and_the_file() {
        let project = tempfile::tempdir().unwrap();
        let path = project.path().join("lean-toolchain");

        let missing = verify_pinned_lean_toolchain(project.path())
            .unwrap_err()
            .to_string();
        assert!(missing.contains("has no lean-toolchain"), "{missing}");
        assert!(missing.contains(&path.display().to_string()), "{missing}");
        assert!(missing.contains("leanprover/lean4:v4.32.2"), "{missing}");

        std::fs::write(&path, "leanprover/lean4:v4.31.0\n").unwrap();
        let mismatched = verify_pinned_lean_toolchain(project.path())
            .unwrap_err()
            .to_string();
        assert!(
            mismatched.contains(&path.display().to_string()),
            "{mismatched}"
        );
        assert!(
            mismatched.contains("expected: leanprover/lean4:v4.32.2"),
            "{mismatched}"
        );
        assert!(
            mismatched.contains("found: leanprover/lean4:v4.31.0"),
            "{mismatched}"
        );

        std::fs::write(&path, lean_pipeline::render::GENERATED_LEAN_TOOLCHAIN).unwrap();
        assert_eq!(
            verify_pinned_lean_toolchain(project.path()).unwrap(),
            "leanprover/lean4:v4.32.2"
        );
    }

    #[test]
    fn manifest_round_trip_and_classification_inputs() {
        let toml_src = r#"
[[obligation]]
name = "foo_correct"
ir_name = "foo_correct"
kind = "theorem"
module = "Pkg.Math"
prop = "Pkg.Math.foo_correct"
lean_decl = "foo_correct"
target = "Pkg.Math.foo"
target_source = "Pkg::math::foo"
source = "Pkg::math::foo_spec"

[[obligation]]
name = "bar_correct"
ir_name = "bar_correct"
kind = "trusted_axiom"
reason = "run_on_boogie"
module = "Pkg.Math"
prop = "Pkg.Math.bar_correct"
lean_decl = "Pkg.Math.bar_correct_holds"
target = "Pkg.Math.bar"
target_source = "Pkg::math::bar"
source = "Pkg::math::bar_spec"
"#;
        let m: Manifest = toml::from_str(toml_src).unwrap();
        assert_eq!(m.obligation.len(), 2);
        assert_eq!(m.obligation[1].reason.as_deref(), Some("run_on_boogie"));

        // Trusted `_holds` is a (name, module) PAIR from the manifest.
        let trusted: BTreeSet<(&str, &str)> = [("Pkg.Math.bar_correct_holds", "Pkg.Math")]
            .into_iter()
            .collect();
        let no_overlay = std::path::Path::new("/nonexistent/lean");
        let nd = true; // type is @Eq Bool _ true
        let notnd = false;
        assert!(axiom_allowed(
            "propext",
            "Init.Core",
            notnd,
            &trusted,
            no_overlay
        ));
        // Trusted `_holds` in its declared module -> allowed.
        assert!(axiom_allowed(
            "Pkg.Math.bar_correct_holds",
            "Pkg.Math",
            notnd,
            &trusted,
            no_overlay
        ));
        // Same `_holds` NAME declared in a DIFFERENT (proofs-overlay)
        // module -> NOT trusted (the medium bypass this closes).
        assert!(!axiom_allowed(
            "Pkg.Math.bar_correct_holds",
            "Pkg.Other_Proofs",
            notnd,
            &trusted,
            no_overlay
        ));
        assert!(axiom_allowed(
            "Sui.Table_vec.index_present_iff_lt",
            "Sui.Table_vecLemmas",
            notnd,
            &trusted,
            no_overlay
        ));
        assert!(!axiom_allowed(
            "Proofs.helper_axiom",
            "Proofs.WorldFrame",
            notnd,
            &trusted,
            no_overlay
        ));
        // native_decide synthetics: trusted ONLY with the Bool-eq type
        // shape AND the name marker.
        assert!(axiom_allowed(
            "_private.SuiSystemSpecs.Sui_system_specs_Proofs.0.one_val_u64._native.native_decide.ax_1_1",
            "SuiSystemSpecs.Sui_system_specs_Proofs",
            nd,
            &trusted,
            no_overlay
        ));
        // A forged axiom with the native_decide NAME but a non-Bool-eq
        // type (nd_shape=false, e.g. it proves the obligation Prop) is
        // NOT trusted -- the high-severity bypass this closes.
        assert!(!axiom_allowed(
            "o._native.native_decide.stub",
            "SuiSystemSpecs.Sui_system_specs_Proofs",
            notnd,
            &trusted,
            no_overlay
        ));
        assert!(!axiom_allowed(
            "o._native.native_decide.stub",
            "SuiSystemSpecs.Sui_system_specs_Proofs",
            nd,
            &trusted,
            no_overlay
        ));
        assert!(!axiom_allowed(
            "o._native.native_decide.ax_1_many",
            "SuiSystemSpecs.Sui_system_specs_Proofs",
            nd,
            &trusted,
            no_overlay
        ));
        // A Bool-eq-shaped axiom WITHOUT the native_decide name marker is
        // not auto-trusted either.
        assert!(!axiom_allowed(
            "validator_is_duplicate_aborts_noabort_nx",
            "SuiSystemSpecs.Sui_system_state_inner_specs_Proofs",
            nd,
            &trusted,
            no_overlay
        ));
    }

    #[test]
    fn lib_root_trust_denied_for_overlay_shadow_modules() {
        // A proofs-overlay file at lean/Sui/X.lean gets module name
        // `Sui.X`; its axioms must NOT inherit lemma-base trust.
        let temp = tempfile::tempdir().unwrap();
        let overlay = temp.path().join("lean");
        std::fs::create_dir_all(overlay.join("Sui")).unwrap();
        std::fs::write(
            overlay.join("Sui").join("Evil_Proofs.lean"),
            "axiom bad : False\n",
        )
        .unwrap();
        let trusted: BTreeSet<(&str, &str)> = BTreeSet::new();
        assert!(!axiom_allowed(
            "Sui.bad",
            "Sui.Evil_Proofs",
            false,
            &trusted,
            &overlay
        ));
        // A genuine lemma-lib module (no overlay file) keeps its trust.
        assert!(axiom_allowed(
            "Sui.Table_vec.index_present_iff_lt",
            "Sui.Table_vecLemmas",
            false,
            &trusted,
            &overlay
        ));
    }

    #[test]
    fn overlay_scan_rejects_initialize_block() {
        let temp = tempfile::tempdir().unwrap();
        let overlay = temp.path().join("lean");
        std::fs::create_dir_all(overlay.join("Pkg")).unwrap();
        let evil = overlay.join("Pkg").join("Evil_Proofs.lean");
        for source in [
            "#eval IO.println \"spoof\"\n",
            "initialize do IO.println \"spoof\"\n",
            "private initialize state : IO.Ref Nat ← IO.mkRef 0\n",
            "builtin_initialize state : IO.Ref Nat ← IO.mkRef 0\n",
            "@[init] def runAtImport : IO Unit := pure ()\n",
            "@[builtin_init] unsafe def runAtImport : IO Unit := pure ()\n",
            "@[«init»] def runAtImport : IO Unit := pure ()\n",
            "@[«builtin_init»] unsafe def runAtImport : IO Unit := pure ()\n",
            "@[other,\n  init ] def runAtImport : IO Unit := pure ()\n",
            "@[deprecated \"]\", init] def runAtImport : IO Unit := pure ()\n",
            "-- initialize hidden in a comment is conservatively reserved\n",
            "def note := r#\"@[init] hidden in a raw string\"#\n",
        ] {
            std::fs::write(&evil, source).unwrap();
            let err = scan_overlay_for_import_time_execution(&overlay).unwrap_err();
            assert!(err.to_string().contains("reserved import-time"), "{err}");
        }
        std::fs::remove_file(evil).unwrap();
        std::fs::write(
            overlay.join("Pkg").join("Ok_Proofs.lean"),
            "def reinitialize_counter := 0\n\
             def builtin_initializer := 0\n\
             @[initialization] def ordinaryAttribute := 0\n\
             @[my_builtin_init] def ordinaryBuiltinAttribute := 0\n\
             @[simp] def init := 0\n",
        )
        .unwrap();
        scan_overlay_for_import_time_execution(&overlay).expect("clean overlay passes");
    }

    #[test]
    fn overlay_scan_rejects_direct_z3_oracle_and_attestation_access() {
        let temp = tempfile::tempdir().unwrap();
        let overlay = temp.path().join("lean");
        std::fs::create_dir_all(overlay.join("Pkg")).unwrap();
        let proof = overlay.join("Pkg").join("Evil_Proofs.lean");
        for source in [
            "theorem bad : False := autoSMTSorry False\n",
            "theorem bad (P : Prop) : P := _root_.«autoSMTSorry» P\n",
            "theorem bad : True := Prover.MoveAuto.z3OracleResult True.intro\n",
            "set_option auto.smt.trust true in theorem bad : True := by trivial\n",
            "set_option «auto».«smt».«trust» true in theorem bad : True := by trivial\n",
            "set_option auto.«smt».trust true in theorem bad : True := by trivial\n",
            "set_option «auto.smt.trust» true in theorem bad : True := by trivial\n",
            "theorem bad : True := by move_z3\n",
            "theorem bad : True := by «move_z3»\n",
            "theorem bad (P : Prop) : P :=\n\
             \x20 Prover.MoveAuto.«explicitZ3OracleResult»\n\
             \x20   (Prover.MoveAuto.«z3OracleResult» («autoSMTSorry» P))\n",
        ] {
            std::fs::write(&proof, source).unwrap();
            let error = scan_overlay_for_import_time_execution(&overlay).unwrap_err();
            assert!(error.to_string().contains("reserved Z3 trust"), "{error}");
        }

        std::fs::write(
            &proof,
            "theorem «autoSMTSorry_helper» : True := True.intro\n\
             theorem «z3OracleResult_note» : True := True.intro\n\
             theorem «explicitZ3OracleResult_note» : True := True.intro\n\
             theorem «move_z3_note» : True := True.intro\n\
             theorem «auto.smt.trusted» : True := True.intro\n",
        )
        .unwrap();
        scan_overlay_for_import_time_execution(&overlay)
            .expect("unrelated quoted identifiers must remain valid");
    }

    #[test]
    fn source_scans_reject_handwritten_native_decide_axiom_provenance() {
        let temp = tempfile::tempdir().unwrap();
        let overlay = temp.path().join("lean");
        std::fs::create_dir_all(overlay.join("Pkg")).unwrap();
        let proof = overlay.join("Pkg").join("Math_Proofs.lean");
        for source in [
            "axiom forged._native.native_decide.ax_1_1 : false = true\n",
            "namespace forged._native.native_decide\n\
             private axiom ax_1_1 : false = true\n\
             end forged._native.native_decide\n",
            "namespace forged._native\n\
             namespace native_decide\n\
             axiom ax_1_1 : false = true\n\
             end native_decide\n\
             end forged._native\n",
            "namespace forged.«_native».«native_decide»\n\
             private axiom ax_1_1 : false = true\n\
             end forged.«_native».«native_decide»\n",
        ] {
            std::fs::write(&proof, source).unwrap();
            let error = scan_overlay_for_import_time_execution(&overlay).unwrap_err();
            assert!(
                error
                    .to_string()
                    .contains("forged native_decide provenance"),
                "{error}"
            );
        }

        std::fs::write(
            &proof,
            "namespace «_native_helper».«native_decide_note»\n\
             axiom documented_assumption : True\n\
             end «_native_helper».«native_decide_note»\n\
             theorem genuine : True := by native_decide\n",
        )
        .unwrap();
        scan_overlay_for_import_time_execution(&overlay).unwrap();
    }

    #[test]
    fn overlay_scan_rejects_custom_metaprograms_but_ignores_comments() {
        let temp = tempfile::tempdir().unwrap();
        let overlay = temp.path().join("lean");
        std::fs::create_dir_all(overlay.join("Pkg")).unwrap();
        let proof = overlay.join("Pkg").join("Evil_Proofs.lean");
        std::fs::write(
            &proof,
            "-- the source Move macro syntax is irrelevant here\n\
             theorem ok : True := by trivial\n",
        )
        .unwrap();
        scan_overlay_for_import_time_execution(&overlay).unwrap();

        std::fs::write(&proof, "elab \"forge\" : tactic => pure ()\n").unwrap();
        let error = scan_overlay_for_import_time_execution(&overlay).unwrap_err();
        assert!(
            error.to_string().contains("reserved proof metaprogram"),
            "{error}"
        );

        std::fs::write(
            &proof,
            "theorem forge : True := by fromMetaTactic [makeProof]\n",
        )
        .unwrap();
        let error = scan_overlay_for_import_time_execution(&overlay).unwrap_err();
        assert!(
            error.to_string().contains("reserved proof metaprogram"),
            "{error}"
        );

        for source in [
            "theorem forge : True := by «fromMetaTactic» [makeProof]\n",
            "#getExprAndApply[True | makeProof]\n",
            "#«getExprAndApply»[True | makeProof]\n",
            "def forge : Lean.Elab.Tactic.TacticM Unit := pure ()\n\
             theorem bad : True := by aesop (add safe tactic forge)\n",
            "def forge : Lean.Elab.Tactic.«TacticM» Unit := pure ()\n",
            "declare_rebindable forge : Lean.MetaM Unit\n",
            "declare_rebindable forge : Lean.«MetaM» Unit\n",
        ] {
            std::fs::write(&proof, source).unwrap();
            let error = scan_overlay_for_import_time_execution(&overlay).unwrap_err();
            assert!(
                error.to_string().contains("reserved proof metaprogram"),
                "{error}"
            );
        }

        std::fs::write(
            &proof,
            "theorem «fromMetaTactic_helper» : True := True.intro\n\
             theorem «getExprAndApply_note» : True := True.intro\n\
             theorem «TacticM_note» : True := True.intro\n",
        )
        .unwrap();
        scan_overlay_for_import_time_execution(&overlay)
            .expect("unrelated quoted metaprogram-like identifiers must remain valid");
    }

    #[test]
    fn reserved_lean_module_roots_cannot_be_shadowed_by_generated_or_overlay_sources() {
        let temp = tempfile::tempdir().unwrap();
        for (source_kind, relative, module_root) in [
            ("generated-auto", "Auto/Tactic.lean", "Auto"),
            ("generated-core", "Lean.lean", "Lean"),
            ("proof-overlay", "Init/Prelude.lean", "Init"),
        ] {
            let root = temp.path().join(source_kind);
            let shadow = root.join(relative);
            std::fs::create_dir_all(shadow.parent().unwrap()).unwrap();
            std::fs::write(&shadow, "def harmless := True\n").unwrap();
            let error = reject_reserved_module_collisions(&root, source_kind).unwrap_err();
            assert!(
                error.to_string().contains(&format!(
                    "shadows reserved Lean module root `{module_root}`"
                )),
                "{error}"
            );
        }
    }

    #[test]
    fn proof_overlay_snapshot_tracks_the_complete_source_tree() {
        let temp = tempfile::tempdir().unwrap();
        let overlay = temp.path().join("lean");
        std::fs::create_dir_all(overlay.join("Pkg")).unwrap();
        let proof = overlay.join("Pkg").join("Math_Proofs.lean");
        std::fs::write(&proof, "theorem ok : True := by trivial\n").unwrap();
        let before = proof_overlay_snapshot(&overlay).unwrap();

        std::fs::write(&proof, "theorem changed : True := by trivial\n").unwrap();
        let after_edit = proof_overlay_snapshot(&overlay).unwrap();
        std::fs::write(overlay.join("trusted_axioms.toml"), "axiom = []\n").unwrap();
        let after_add = proof_overlay_snapshot(&overlay).unwrap();

        assert_ne!(before, after_edit);
        assert_ne!(after_edit, after_add);
    }

    fn protocol_obligation() -> Manifest {
        toml::from_str(
            r#"
[[obligation]]
name = "foo_correct"
ir_name = "foo_correct"
kind = "theorem"
module = "Pkg.Math"
prop = "Pkg.Math.foo_correct"
lean_decl = "foo_correct"
target = "Pkg.Math.foo"
target_source = "Pkg::math::foo"
source = "Pkg::math::foo_spec"
"#,
        )
        .unwrap()
    }

    #[test]
    fn audit_protocol_accepts_one_complete_strict_transcript() {
        let manifest = protocol_obligation();
        let obligations: Vec<_> = manifest.obligation.iter().collect();
        let transcript = "noise from Lake\n\
            N|OB|foo_correct|ok|theorem|Pkg.Math_Proofs\n\
            N|Z3|foo_correct|0\n\
            N|ST|foo_correct|conditional|1|-\n\
            N|HYP|foo_correct|h : True | display text may contain pipes\n\
            N|AX|foo_correct|0|Init.Prelude|propext\n\
            N|END|1\n";

        let parsed =
            parse_audit_group_output("N", "Pkg.Math_Proofs", &obligations, transcript).unwrap();

        assert_eq!(
            parsed.found["foo_correct"],
            (true, "theorem".to_string(), "Pkg.Math_Proofs".to_string())
        );
        assert_eq!(
            parsed.statements["foo_correct"],
            ("conditional".to_string(), 1)
        );
        assert_eq!(
            parsed.hypotheses["foo_correct"],
            ["h : True | display text may contain pipes"]
        );
        assert_eq!(
            parsed.axioms["foo_correct"],
            [("propext".to_string(), "Init.Prelude".to_string(), false)]
        );
    }

    #[test]
    fn audit_protocol_rejects_spoofed_or_truncated_transcripts() {
        let manifest = protocol_obligation();
        let obligations: Vec<_> = manifest.obligation.iter().collect();
        let cases = [
            (
                "duplicate OB",
                "N|OB|foo_correct|ok|theorem|Pkg.Math_Proofs\nN|OB|foo_correct|ok|theorem|Pkg.Math_Proofs\nN|ST|foo_correct|exact|0|-\nN|END|1\n",
            ),
            (
                "duplicate ST",
                "N|OB|foo_correct|ok|theorem|Pkg.Math_Proofs\nN|ST|foo_correct|exact|0|-\nN|ST|foo_correct|exact|0|-\nN|END|1\n",
            ),
            (
                "row after END",
                "N|OB|foo_correct|missing|-|-\nN|END|1\nN|END|1\n",
            ),
            (
                "unknown nonce-prefixed",
                "N|OB|foo_correct|missing|-|-\nN|EVIL|foo_correct\nN|END|1\n",
            ),
            (
                "unknown label",
                "N|OB|other|missing|-|-\nN|END|1\n",
            ),
            (
                "invalid OB status",
                "N|OB|foo_correct|maybe|theorem|Pkg.Math_Proofs\nN|END|1\n",
            ),
            (
                "invalid OB kind",
                "N|OB|foo_correct|ok|proof|Pkg.Math_Proofs\nN|END|1\n",
            ),
            (
                "invalid ST verdict",
                "N|OB|foo_correct|ok|theorem|Pkg.Math_Proofs\nN|ST|foo_correct|invented|0|-\nN|END|1\n",
            ),
            (
                "ST row without a reason field",
                "N|OB|foo_correct|ok|theorem|Pkg.Math_Proofs\nN|ST|foo_correct|exact|0\nN|END|1\n",
            ),
            (
                "unverified ST without a reason",
                "N|OB|foo_correct|ok|theorem|Pkg.Math_Proofs\nN|ST|foo_correct|unverified|0|-\nN|END|1\n",
            ),
            (
                "completed ST carrying a reason",
                "N|OB|foo_correct|ok|theorem|Pkg.Math_Proofs\nN|ST|foo_correct|exact|0|boom\nN|END|1\n",
            ),
            (
                "invalid AX native_decide",
                "N|OB|foo_correct|ok|theorem|Pkg.Math_Proofs\nN|ST|foo_correct|exact|0|-\nN|AX|foo_correct|yes|Init.Prelude|propext\nN|END|1\n",
            ),
            (
                "duplicate AX",
                "N|OB|foo_correct|ok|theorem|Pkg.Math_Proofs\nN|ST|foo_correct|exact|0|-\nN|AX|foo_correct|0|Init.Prelude|propext\nN|AX|foo_correct|0|Init.Prelude|propext\nN|END|1\n",
            ),
            (
                "wrong END count",
                "N|OB|foo_correct|missing|-|-\nN|END|2\n",
            ),
            (
                "truncated hypotheses",
                "N|OB|foo_correct|ok|theorem|Pkg.Math_Proofs\nN|ST|foo_correct|conditional|1|-\nN|END|1\n",
            ),
            (
                "missing END",
                "N|OB|foo_correct|missing|-|-\n",
            ),
            (
                "missing OB",
                "N|END|1\n",
            ),
            (
                "rows for missing declaration",
                "N|OB|foo_correct|missing|-|-\nN|ST|foo_correct|exact|0|-\nN|END|1\n",
            ),
        ];

        for (case, transcript) in cases {
            let error = parse_audit_group_output("N", "Pkg.Math_Proofs", &obligations, transcript)
                .expect_err(case);
            assert!(!error.to_string().is_empty(), "{case}");
        }
    }

    #[test]
    fn name_components_strip_guillemets() {
        assert_eq!(
            name_components("Pkg.\u{ab}matches\u{bb}.foo_holds"),
            vec!["Pkg", "matches", "foo_holds"]
        );
    }

    #[test]
    fn audit_source_loads_target_without_importing_it() {
        let m: Manifest = toml::from_str(
            r#"
[[obligation]]
name = "foo_correct"
ir_name = "foo_correct"
kind = "theorem"
module = "Pkg.Math"
prop = "Pkg.Math.foo_correct"
lean_decl = "foo_correct"
target = "Pkg.Math.foo"
target_source = "Pkg::math::foo"
source = "Pkg::math::foo_spec"
"#,
        )
        .unwrap();
        let obs: Vec<&Obligation> = m.obligation.iter().collect();
        let src = audit_lean_source(
            "AUDIT_NONCE",
            &[
                PathBuf::from("/fresh/root artifacts"),
                PathBuf::from("/fresh/auto artifacts"),
            ],
            "Pkg.Math_Proofs",
            &obs,
            1234,
        );
        assert!(src.contains("import Lean"));
        assert!(!src.contains("import Pkg.Math_Proofs"));
        assert_eq!(
            src.lines()
                .filter(|line| line.starts_with("import "))
                .collect::<Vec<_>>(),
            vec!["import Lean"]
        );
        assert!(src.contains("Lean.withImportModules"));
        assert!(src.contains("(act := fun env => do"));
        assert!(src.contains("System.FilePath.mk \"/fresh/root artifacts\""));
        assert!(src.contains("System.FilePath.mk \"/fresh/auto artifacts\""));
        assert!(src.contains("#[\"Pkg\", \"Math_Proofs\"]"));
        // Quadruple: label, proof-decl components, declaration namespace,
        // prop components.
        assert!(src.contains(
            "(\"foo_correct\", #[\"foo_correct\"], #[\"Pkg\", \"Math_Proofs\"], #[\"Pkg\", \"Math\", \"foo_correct\"])"
        ));
        assert!(src.contains("Lean.collectAxioms"));
        assert!(src.contains("let nonce := \"AUDIT_NONCE\""));
        assert!(src.contains("{nonce}|END|{decls.size}"));
        assert!(src.contains("isConstOf ``Bool.true"));
        assert!(src.contains("{nonce}|OB|{label}|ok|{obKind}|{obMod}"));
        assert!(src.contains("{nonce}|Z3|{label}|{z3Oracle}"));
        // Statement-check machinery: eta-expected statement built from
        // the prop's own telescope, defeq gate, conditional scan, and
        // the ST / HYP protocol lines.
        assert!(src.contains("mkForallFVars xs (mkAppN propConst xs)"));
        assert!(src.contains("if declType == expected then"));
        assert!(src.contains("withReducible (isDefEq declType expected)"));
        assert!(src.contains("isDefEq declType expected"));
        assert!(src.contains("withCurrHeartbeats classifyStatement"));
        assert!(src.contains("tryCatchRuntimeEx"));
        assert!(src.contains("{nonce}|ST|{label}|{verdict}|{extras.size}|{stOutcome.2.2}"));
        assert!(src.contains("{nonce}|HYP|{label}|{clean}"));
        assert!(src.contains("prop_missing"));
        // The statement check runs under its OWN rebased budget, so one slow
        // obligation cannot spend the group's allowance, and a check that does
        // not complete is recorded as `unverified` instead of aborting the run.
        assert!(src.contains("let stHeartbeats := 1234"));
        assert!(src.contains("maxHeartbeats := stHeartbeats"));
        assert!(src.contains("pure (\"unverified\", (#[] : Array String), reason)"));
        assert!(src.contains("stSaved.restore"));
    }

    #[test]
    fn audit_protocol_records_declaration_kinds() {
        let manifest = protocol_obligation();
        let obligations: Vec<_> = manifest.obligation.iter().collect();
        let transcript = "N|OB|foo_correct|ok|def|Pkg.Math_Proofs\n\
                          N|Z3|foo_correct|0\n\
                          N|ST|foo_correct|exact|0|-\n\
                          N|END|1\n";

        let parsed =
            parse_audit_group_output("N", "Pkg.Math_Proofs", &obligations, transcript).unwrap();

        assert_eq!(
            parsed.found["foo_correct"],
            (true, "def".to_string(), "Pkg.Math_Proofs".to_string())
        );
        assert_eq!(expected_declaration_kind("theorem"), Some("theorem"));
        assert_ne!(
            expected_declaration_kind("theorem"),
            Some(parsed.found["foo_correct"].1.as_str())
        );
        assert_eq!(expected_declaration_kind("trusted_axiom"), Some("axiom"));
    }

    struct RealAuditFixture {
        _temp: tempfile::TempDir,
        output: PathBuf,
        package: PathBuf,
        proof: PathBuf,
    }

    impl RealAuditFixture {
        fn new(proof_source: &str) -> Self {
            let temp = tempfile::tempdir().unwrap();
            let output = temp.path().join("output");
            let package = temp.path().join("package");
            let proof_root = package.join("lean");
            let proof = proof_root
                .join("Pkg")
                .join("Math_Proofs")
                .join("foo_correct.lean");
            std::fs::create_dir_all(output.join("Pkg")).unwrap();
            std::fs::create_dir_all(proof.parent().unwrap()).unwrap();
            std::fs::write(
                output.join("lakefile.lean"),
                format!(
                    "import Lake\nopen Lake DSL\n\npackage audit_boundary\n\n\
                     lean_lib Pkg where\n  roots := #[`Pkg]\n  globs := #[.submodules `Pkg]\n\n\
                     @[default_target]\nlean_lib SourceProofs where\n  srcDir := \"../package/lean\"\n  roots := #[`Pkg.Math_Proofs.foo_correct]\n"
                ),
            )
            .unwrap();
            // Every real generated project carries this file. Without it lake
            // resolves the toolchain by walking ANCESTORS of the scratch
            // project, which lives under the system temp dir -- so a stray
            // `/tmp/lean-toolchain` silently builds the fixture on a Lean the
            // model does not support.
            std::fs::write(
                output.join("lean-toolchain"),
                lean_pipeline::render::GENERATED_LEAN_TOOLCHAIN,
            )
            .unwrap();
            std::fs::write(output.join("Pkg.lean"), "import Pkg.Math\n").unwrap();
            std::fs::write(
                output.join("Pkg").join("Math.lean"),
                "namespace Pkg.Math\n\ndef foo_correct : Prop := True\n\nend Pkg.Math\n",
            )
            .unwrap();
            std::fs::write(&proof, proof_source).unwrap();
            std::fs::write(
                output.join("obligations.toml"),
                r#"[[obligation]]
name = "foo_correct"
ir_name = "foo_correct"
kind = "theorem"
module = "Pkg.Math"
prop = "Pkg.Math.foo_correct"
lean_decl = "foo_correct"
target = "Pkg.Math.foo"
target_source = "Pkg::math::foo"
source = "Pkg::math::foo_spec"
"#,
            )
            .unwrap();
            std::fs::write(
                output.join("expected_obligations.toml"),
                r#"version = 1

[[expected]]
source = "Pkg::math::foo_spec"
target = "Pkg::math::foo"
kind = "theorem"
obligations = ["foo_correct"]
"#,
            )
            .unwrap();
            Self {
                _temp: temp,
                output,
                package,
                proof,
            }
        }
    }

    #[tokio::test]
    async fn audit_accepts_genuine_native_decide_synthetics() {
        if std::process::Command::new("lake")
            .arg("--version")
            .output()
            .is_err()
        {
            return;
        }
        let fixture = RealAuditFixture::new(
            "import Pkg.Math\nimport Std.Tactic\n\n\
             theorem foo_correct : Pkg.Math.foo_correct := by\n\
             \x20 unfold Pkg.Math.foo_correct\n\
             \x20 native_decide\n",
        );

        let summary = run_proof_audit(&fixture.output, &fixture.package, AuditMode::CleanRoom)
            .await
            .unwrap();

        assert_eq!(summary.proven, 1);
        assert_eq!(summary.suspicious, 0);
        let status = std::fs::read_to_string(fixture.output.join("proof_status.toml")).unwrap();
        assert!(status.contains("status = \"proven\""));
    }

    #[tokio::test]
    async fn audit_rejects_same_source_and_imported_native_decide_axiom_forgeries() {
        let same_source = RealAuditFixture::new(
            "import Pkg.Math\n\n\
             namespace forged._native.native_decide\n\
             axiom ax_1_1 : false = true\n\
             end forged._native.native_decide\n\n\
             theorem foo_correct : Pkg.Math.foo_correct := by trivial\n",
        );
        let error = run_proof_audit(
            &same_source.output,
            &same_source.package,
            AuditMode::CleanRoom,
        )
        .await
        .unwrap_err();
        assert!(
            error
                .to_string()
                .contains("forged native_decide provenance"),
            "{error:#}"
        );

        let imported = RealAuditFixture::new(
            "import Pkg.Math\nimport Pkg.ForgedHelper\n\n\
             theorem foo_correct : Pkg.Math.foo_correct := by trivial\n",
        );
        std::fs::write(
            imported
                .package
                .join("lean")
                .join("Pkg")
                .join("ForgedHelper.lean"),
            "namespace forged._native\n\
             namespace native_decide\n\
             private axiom ax_1_1 : false = true\n\
             end native_decide\n\
             end forged._native\n",
        )
        .unwrap();
        let error = run_proof_audit(&imported.output, &imported.package, AuditMode::CleanRoom)
            .await
            .unwrap_err();
        assert!(
            error
                .to_string()
                .contains("forged native_decide provenance"),
            "{error:#}"
        );
    }

    fn copy_move_auto_source_closure(backend: &Path, output: &Path) {
        let lemma_sources = [
            ("Prelude/BoundedNat.lean", "lemmas/Prelude/BoundedNat.lean"),
            ("Prelude/Helpers.lean", "lemmas/Prelude/Helpers.lean"),
            ("Prelude/Mutation.lean", "lemmas/Prelude/Mutation.lean"),
            (
                "Prover/MoveAutoAttr.lean",
                "lemmas/natives/Prover/MoveAutoAttr.lean",
            ),
            (
                "Prover/MoveAuto.lean",
                "lemmas/natives/Prover/MoveAuto.lean",
            ),
        ];
        for (destination, source) in lemma_sources {
            let destination = output.join(destination);
            std::fs::create_dir_all(destination.parent().unwrap()).unwrap();
            std::fs::copy(
                backend.join("crates/lean-pipeline").join(source),
                destination,
            )
            .unwrap();
        }
    }

    /// Rewire a `RealAuditFixture` output tree into the shape a generated
    /// `--new-pipeline` project has: the pinned MoveAuto source closure plus the
    /// three vendored automation `require`s and their Lake manifest entries.
    fn wire_automation_dependencies(backend: &Path, output: &Path) {
        copy_move_auto_source_closure(backend, output);
        let dependency_specs = [
            (
                "batteries",
                backend.join("vendor/batteries"),
                "lakefile.toml",
            ),
            ("aesop", backend.join("vendor/aesop"), "lakefile.toml"),
            ("auto", backend.join("vendor/lean-auto"), "lakefile.lean"),
        ];
        let original_lakefile = std::fs::read_to_string(output.join("lakefile.lean")).unwrap();
        let requires = dependency_specs
            .iter()
            .map(|(name, directory, _)| {
                format!(
                    "require {name} from \"{}\"\n",
                    lake_path_literal(&directory.canonicalize().unwrap())
                )
            })
            .collect::<String>();
        std::fs::write(
            output.join("lakefile.lean"),
            original_lakefile.replace(
                "package audit_boundary\n\n",
                &format!(
                    "package audit_boundary\n\n{requires}\n\
                     lean_lib Prelude where\n  roots := #[`Prelude]\n  \
                     globs := #[.submodules `Prelude]\n\n\
                     lean_lib Prover where\n  roots := #[`Prover]\n  \
                     globs := #[.submodules `Prover]\n\n"
                ),
            ),
        )
        .unwrap();
        let manifest = serde_json::json!({
            "version": "1.2.0",
            "packagesDir": ".lake/packages",
            "packages": dependency_specs.iter().map(|(name, directory, config)| {
                serde_json::json!({
                    "type": "path",
                    "scope": "",
                    "name": name,
                    "manifestFile": "lake-manifest.json",
                    "inherited": false,
                    "dir": directory.canonicalize().unwrap(),
                    "configFile": config
                })
            }).collect::<Vec<_>>(),
            "name": "audit_boundary",
            "lakeDir": ".lake",
            "fixedToolchain": false
        });
        std::fs::write(
            output.join("lake-manifest.json"),
            serde_json::to_vec(&manifest).unwrap(),
        )
        .unwrap();
    }

    /// The integer-mate shape: the vendored automation dependencies are
    /// required and digest-verified, but nothing in the audited import closure
    /// reaches Aesop or lean-auto, so the fresh audit build never produces
    /// artifacts for them. That must audit clean, not fail closed.
    #[tokio::test]
    async fn audit_accepts_an_overlay_that_imports_no_automation_dependency() {
        if std::process::Command::new("lake")
            .arg("--version")
            .output()
            .is_err()
        {
            return;
        }
        let backend = Path::new(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .and_then(Path::parent)
            .unwrap();
        let fixture = RealAuditFixture::new(
            "import Pkg.Math\n\n\
             theorem foo_correct : Pkg.Math.foo_correct := by\n\
             \x20 unfold Pkg.Math.foo_correct\n\
             \x20 trivial\n",
        );
        wire_automation_dependencies(backend, &fixture.output);

        let summary = run_proof_audit(&fixture.output, &fixture.package, AuditMode::CleanRoom)
            .await
            .unwrap();

        assert_eq!(summary.proven, 1);
        assert_eq!(summary.sorry, 0);
        assert_eq!(summary.suspicious, 0);
        assert_eq!(summary.missing, 0);
        assert_eq!(summary.statement_mismatch, 0);
    }

    // lean-auto's trusted external-Z3 oracle does not currently consume the
    // Windows process output correctly (even for `x < x + 1`). The audit's
    // source-provenance logic is covered platform-independently below; keep
    // this end-to-end external solver test on supported hosts.
    #[cfg(not(windows))]
    #[tokio::test]
    async fn audit_reports_vendored_z3_oracle_proofs_as_smt_trusted() {
        if std::process::Command::new("lake")
            .arg("--version")
            .output()
            .is_err()
            || std::process::Command::new("z3")
                .arg("--version")
                .output()
                .is_err()
        {
            return;
        }
        let backend = Path::new(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .and_then(Path::parent)
            .unwrap();
        let fixture = RealAuditFixture::new(
            "import Pkg.Math\nimport Prover.MoveAuto\n\n\
             theorem foo_correct : Pkg.Math.foo_correct := by\n\
             \x20 unfold Pkg.Math.foo_correct\n\
             \x20 intro x\n\
             \x20 move_auto (solver := z3)\n",
        );
        std::fs::write(
            fixture.output.join("Pkg/Math.lean"),
            "namespace Pkg.Math\n\ndef foo_correct : Prop := ∀ x : Int, x < x + 1\n\nend Pkg.Math\n",
        )
        .unwrap();
        wire_automation_dependencies(backend, &fixture.output);

        let summary = run_proof_audit(&fixture.output, &fixture.package, AuditMode::CleanRoom)
            .await
            .unwrap();

        assert_eq!(summary.proven, 0);
        assert_eq!(summary.smt_trusted, 1);
        assert_eq!(summary.suspicious, 0);
        let status = std::fs::read_to_string(fixture.output.join("proof_status.toml")).unwrap();
        assert!(status.contains("status = \"smt_trusted\""));
        assert!(status.contains("smt_trusted_axioms = [\"autoSMTSorry\"]"));
    }

    /// A generated proposition whose body only reduces after real work, so a
    /// statement check that unfolds it is measurably expensive while one that
    /// never looks inside it is free.
    fn write_slow_prop(fixture: &RealAuditFixture) {
        std::fs::write(
            fixture.output.join("Pkg/Math.lean"),
            "namespace Pkg.Math\n\n\
             def spin (n : Nat) : Nat := Nat.rec 0 (fun _ ih => ih) n\n\n\
             def foo_correct : Prop := spin 300 = 0\n\n\
             end Pkg.Math\n",
        )
        .unwrap();
    }

    /// An overlay theorem that restates the generated proposition verbatim -- a
    /// direct application of the generated `def`, the overwhelmingly common
    /// shape -- is alpha-equivalent to the eta-expected statement. The
    /// structural fast path settles it without unfolding the proposition and
    /// without calling anything that consults the deterministic-timeout budget,
    /// so it is accepted even at the smallest budget the audit can be given.
    /// The sibling test below runs the SAME proposition and budget through a
    /// statement that has to unfold it, and gets `statement_unverified`.
    #[tokio::test]
    async fn audit_accepts_a_direct_application_statement_without_spending_its_budget() {
        if std::process::Command::new("lake")
            .arg("--version")
            .output()
            .is_err()
        {
            return;
        }
        let fixture = RealAuditFixture::new(
            "import Pkg.Math\n\ntheorem foo_correct : Pkg.Math.foo_correct := by rfl\n",
        );
        write_slow_prop(&fixture);

        let summary = run_proof_audit_with_statement_budget(
            &fixture.output,
            &fixture.package,
            HEARTBEATS_PER_OPTION_UNIT,
            AuditMode::CleanRoom,
        )
        .await
        .unwrap();

        assert_eq!(summary.proven, 1);
        assert_eq!(summary.statement_unverified, 0);
        assert!(summary.is_clean());
    }

    /// A statement check that cannot finish inside its budget must be REPORTED,
    /// not allowed to abort the run: `proof_status.toml` is still written, the
    /// offender carries its own non-passing class plus the Lean reason, and the
    /// summary stays dirty so the caller exits non-zero. The same obligation at
    /// the real budget is `proven`, so the class tracks the budget rather than a
    /// statement defect -- and an incomplete check never reads as proven.
    #[tokio::test]
    async fn audit_reports_a_budget_exhausted_statement_check_instead_of_aborting() {
        if std::process::Command::new("lake")
            .arg("--version")
            .output()
            .is_err()
        {
            return;
        }
        let fixture = RealAuditFixture::new(
            "import Pkg.Math\n\ntheorem foo_correct : (0 : Nat) = 0 := rfl\n",
        );
        write_slow_prop(&fixture);

        let exhausted = run_proof_audit_with_statement_budget(
            &fixture.output,
            &fixture.package,
            HEARTBEATS_PER_OPTION_UNIT,
            AuditMode::CleanRoom,
        )
        .await
        .unwrap();

        assert_eq!(exhausted.statement_unverified, 1);
        assert_eq!(exhausted.proven, 0);
        assert_eq!(exhausted.statement_mismatch, 0);
        assert!(!exhausted.is_clean());
        let status = std::fs::read_to_string(fixture.output.join("proof_status.toml")).unwrap();
        assert!(status.contains("statement_unverified = 1"));
        assert!(status.contains("status = \"statement_unverified\""));
        assert!(status.contains("maximum number of heartbeats"));

        let generous = run_proof_audit_with_statement_budget(
            &fixture.output,
            &fixture.package,
            DEFAULT_STATEMENT_HEARTBEATS,
            AuditMode::CleanRoom,
        )
        .await
        .unwrap();

        assert_eq!(generous.proven, 1);
        assert_eq!(generous.statement_unverified, 0);
        assert!(generous.is_clean());
    }

    #[test]
    fn statement_heartbeat_budget_is_parsed_or_rejected() {
        assert_eq!(
            parse_statement_heartbeats(None).unwrap(),
            DEFAULT_STATEMENT_HEARTBEATS
        );
        assert_eq!(
            parse_statement_heartbeats(Some(" 4096 ")).unwrap(),
            4096 * HEARTBEATS_PER_OPTION_UNIT
        );
        assert_eq!(parse_statement_heartbeats(Some("0")).unwrap(), 0);
        assert!(parse_statement_heartbeats(Some("many")).is_err());
        assert!(parse_statement_heartbeats(Some("-1")).is_err());
    }

    #[test]
    fn audit_job_counts_are_parsed_or_rejected() {
        assert_eq!(
            parse_audit_jobs(QUERY_JOBS_ENV, None).unwrap(),
            DEFAULT_AUDIT_JOBS
        );
        assert_eq!(parse_audit_jobs(QUERY_JOBS_ENV, Some(" 6 ")).unwrap(), 6);
        // Zero would silently disable the phase rather than run it serially.
        assert!(parse_audit_jobs(QUERY_JOBS_ENV, Some("0")).is_err());
        assert!(parse_audit_jobs(QUERY_JOBS_ENV, Some("-1")).is_err());
        assert!(parse_audit_jobs(QUERY_JOBS_ENV, Some("all")).is_err());
    }

    #[tokio::test]
    async fn a_failing_audit_cannot_leave_the_previous_green_report_behind() {
        let temp = tempfile::tempdir().unwrap();
        let output = temp.path().join("output");
        let package = temp.path().join("package");
        std::fs::create_dir_all(&output).unwrap();
        std::fs::create_dir_all(package.join("lean")).unwrap();
        let status = output.join("proof_status.toml");
        // A previous run's all-green report.
        write_proof_status(
            &status,
            AuditMode::CleanRoom,
            &AuditSummary {
                proven: 520,
                trusted: 2,
                ..AuditSummary::default()
            },
            Vec::new(),
            Vec::new(),
            Vec::new(),
        )
        .unwrap();
        assert!(status.is_file());

        // No `obligations.toml`: the audit fails long before it can classify
        // anything -- the same shape as dying in the dependency build.
        let error = run_proof_audit(&output, &package, AuditMode::CleanRoom)
            .await
            .unwrap_err();
        assert!(error.to_string().contains("obligations.toml"), "{error}");
        assert!(
            !status.exists(),
            "a failed audit left a stale report at {}",
            status.display()
        );
    }

    /// The whole point of the counter: an audit with nothing to classify
    /// must still report the prove-specs that produced nothing. Seven
    /// sui-system declarations hid for months under a `0 missing` header
    /// precisely because every counter in this file was structurally
    /// unable to be non-zero for them.
    #[tokio::test]
    async fn spec_no_obligation_is_reported_even_when_no_obligation_exists() {
        let temp = tempfile::tempdir().unwrap();
        let output = temp.path().join("output");
        let package = temp.path().join("package");
        std::fs::create_dir_all(&output).unwrap();
        std::fs::create_dir_all(package.join("lean")).unwrap();
        std::fs::write(
            output.join("obligations.toml"),
            "[[spec_no_obligation]]\n\
             source = \"SuiSystemSpecs::staking_pool_specs::frozen_rate_spec\"\n\
             reason = \"no_target_and_no_ensures\"\n\
             \n\
             [[spec_no_obligation]]\n\
             source = \"SuiSystemSpecs::validator_specs::validate_metadata_bcs_spec\"\n\
             reason = \"no_ensures\"\n",
        )
        .unwrap();
        std::fs::write(output.join("expected_obligations.toml"), "version = 1\n").unwrap();

        let summary = run_proof_audit(&output, &package, AuditMode::CleanRoom)
            .await
            .unwrap();

        assert_eq!(summary.spec_no_obligation, 2);
        // NOT an integrity failure: one legitimate member (a prove spec
        // with a target but no `ensures`) remains, and folding a
        // visibility counter into the gate would change what the gate
        // means rather than what it can see.
        assert!(summary.is_clean());

        let status = std::fs::read_to_string(output.join("proof_status.toml")).unwrap();
        assert!(status.contains("spec_no_obligation = 2"), "{status}");
        assert!(
            status.contains("source = \"SuiSystemSpecs::staking_pool_specs::frozen_rate_spec\""),
            "{status}"
        );
        assert!(status.contains("[[unproduced_obligation]]"), "{status}");
    }

    /// A manifest written before the field existed reads back as zero
    /// unproduced -- an older renderer could not have measured the class,
    /// and the alternative is inventing a count.
    #[test]
    fn a_manifest_without_the_field_parses_as_no_unproduced_specs() {
        let manifest: Manifest = toml::from_str(
            "[[obligation]]\n\
             name = \"foo_correct\"\n\
             ir_name = \"foo_correct\"\n\
             kind = \"theorem\"\n\
             module = \"P.M\"\n\
             prop = \"P.M.foo_correct\"\n\
             lean_decl = \"foo_correct\"\n\
             target = \"P.M.foo\"\n\
             target_source = \"P::m::foo\"\n\
             source = \"P::m::foo_spec\"\n",
        )
        .unwrap();
        assert_eq!(manifest.obligation.len(), 1);
        assert!(manifest.spec_no_obligation.is_empty());
    }

    #[test]
    fn audit_modes_label_themselves_distinctly() {
        assert_eq!(AuditMode::CleanRoom.label(), "clean-room");
        assert_eq!(AuditMode::Cached.label(), "cached");
        assert!(!AuditMode::CleanRoom.reuses_existing_build());
        assert!(AuditMode::Cached.reuses_existing_build());
    }

    #[test]
    fn proof_status_records_the_audit_mode_it_ran_under() {
        let temp = tempfile::tempdir().unwrap();
        for mode in [AuditMode::CleanRoom, AuditMode::Cached] {
            let path = temp.path().join(format!("{}.toml", mode.label()));
            write_proof_status(
                &path,
                mode,
                &AuditSummary::default(),
                Vec::new(),
                Vec::new(),
                Vec::new(),
            )
            .unwrap();
            let raw = std::fs::read_to_string(&path).unwrap();
            assert!(
                raw.contains(&format!("audit_mode = \"{}\"", mode.label())),
                "{raw}"
            );
            let decoded: ProofStatusDocument = toml::from_str(&raw).unwrap();
            assert_eq!(decoded.audit_mode, mode.label());
        }
    }

    #[tokio::test]
    async fn audit_rejects_an_exact_typed_definition_as_a_theorem() {
        if std::process::Command::new("lake")
            .arg("--version")
            .output()
            .is_err()
        {
            return;
        }
        let fixture = RealAuditFixture::new(
            "import Pkg.Math\n\ndef foo_correct : Pkg.Math.foo_correct := by trivial\n",
        );

        let summary = run_proof_audit(&fixture.output, &fixture.package, AuditMode::CleanRoom)
            .await
            .unwrap();

        assert_eq!(summary.suspicious, 1);
        let status = std::fs::read_to_string(fixture.output.join("proof_status.toml")).unwrap();
        assert!(status.contains("obligation decl has kind `def`, expected `theorem`"));
    }

    #[tokio::test]
    async fn audit_rejects_an_imported_obligation_from_the_wrong_module() {
        if std::process::Command::new("lake")
            .arg("--version")
            .output()
            .is_err()
        {
            return;
        }
        let fixture = RealAuditFixture::new("import Pkg.Foreign\n");
        std::fs::write(
            fixture.output.join("Pkg").join("Foreign.lean"),
            "import Pkg.Math\n\ntheorem foo_correct : Pkg.Math.foo_correct := by trivial\n",
        )
        .unwrap();

        let summary = run_proof_audit(&fixture.output, &fixture.package, AuditMode::CleanRoom)
            .await
            .unwrap();

        assert_eq!(summary.suspicious, 1);
        let status = std::fs::read_to_string(fixture.output.join("proof_status.toml")).unwrap();
        assert!(status.contains(
            "obligation decl resolved in `Pkg.Foreign`, expected `Pkg.Math_Proofs.foo_correct`"
        ));
    }

    #[tokio::test]
    async fn audit_prefers_a_local_qualified_obligation_over_an_imported_bare_homonym() {
        if std::process::Command::new("lake")
            .arg("--version")
            .output()
            .is_err()
        {
            return;
        }
        let fixture = RealAuditFixture::new(
            "import Pkg.Math\nimport Pkg.Foreign\n\n\
             theorem _root_.Pkg.Math_Proofs.foo_correct : Pkg.Math.foo_correct := by trivial\n",
        );
        std::fs::write(
            fixture.output.join("Pkg").join("Foreign.lean"),
            "import Pkg.Math\n\ntheorem foo_correct : Pkg.Math.foo_correct := by trivial\n",
        )
        .unwrap();

        let summary = run_proof_audit(&fixture.output, &fixture.package, AuditMode::CleanRoom)
            .await
            .unwrap();

        assert_eq!(summary.proven, 1);
        assert_eq!(summary.suspicious, 0);
    }

    #[tokio::test]
    async fn proof_command_elaborators_are_rejected_before_the_audit_query() {
        let fixture = RealAuditFixture::new(
            "import Lean\nimport Pkg.Math\n\n\
             open Lean Elab Command\n\n\
             syntax (name := proofRunCmdSpoof) (priority := high) \"run_cmd \" doSeq : command\n\
             @[command_elab proofRunCmdSpoof]\n\
             def spoofRunCmd : CommandElab := fun _ =>\n  \
             throwError \"untrusted proof run_cmd elaborator executed\"\n\n\
             theorem foo_correct : Pkg.Math.foo_correct := by trivial\n",
        );

        let error = run_proof_audit(&fixture.output, &fixture.package, AuditMode::CleanRoom)
            .await
            .unwrap_err();
        assert!(
            error.to_string().contains("reserved proof metaprogram"),
            "{error:#}"
        );
    }

    #[tokio::test]
    async fn audit_query_supports_lean_4_17_with_import_modules_signature() {
        const TOOLCHAIN: &str = "leanprover/lean4:v4.17.0-rc1";
        let available = std::process::Command::new("elan")
            .args(["run", TOOLCHAIN, "lean", "--version"])
            .output()
            .is_ok_and(|output| output.status.success());
        if !available {
            return;
        }
        let fixture = RealAuditFixture::new(
            "import Pkg.Math\n\ntheorem foo_correct : Pkg.Math.foo_correct := by trivial\n",
        );
        std::fs::write(
            fixture.output.join("lean-toolchain"),
            format!("{TOOLCHAIN}\n"),
        )
        .unwrap();
        let lake = move_prover_lean_backend::resolve_audit_lake_executable(&fixture.output)
            .await
            .unwrap();
        let module = "Pkg.Math_Proofs.foo_correct";
        let (artifact_dir, _) = rebuild_audit_modules(
            &lake,
            &fixture.output,
            &[(
                module.to_string(),
                fixture.proof.clone(),
                fixture.package.join("lean"),
            )],
            1,
        )
        .await
        .unwrap();
        assert!(lean_module_file(&artifact_dir, module, "olean")
            .unwrap()
            .is_file());
        assert!(
            !lean_module_file(&fixture.output.join(".lake/build/ir"), module, "c")
                .unwrap()
                .exists()
        );

        let summary = run_proof_audit(&fixture.output, &fixture.package, AuditMode::CleanRoom)
            .await
            .unwrap();

        assert_eq!(summary.proven, 1);
        assert_eq!(summary.suspicious, 0);
    }

    /// The one property that justifies `--audit-in-place` doing a build at
    /// all. Editing a proof and forgetting to rebuild must NOT read as green
    /// off a stale OLean -- that is the stale-artifact trap that has already
    /// cost this project days. The mode brings the build up to date first, so
    /// the second audit sees the `sorry` even though nothing rebuilt in
    /// between.
    #[tokio::test]
    async fn the_fast_audit_refuses_to_read_a_stale_olean_as_green() {
        if std::process::Command::new("lake")
            .arg("--version")
            .output()
            .is_err()
        {
            return;
        }
        let fixture = RealAuditFixture::new(
            "import Pkg.Math\n\ntheorem foo_correct : Pkg.Math.foo_correct := by trivial\n",
        );

        let clean = run_proof_audit(&fixture.output, &fixture.package, AuditMode::Cached)
            .await
            .unwrap();
        assert_eq!(clean.proven, 1, "in-place should prove the honest proof");
        assert_eq!(clean.sorry, 0);
        let status = std::fs::read_to_string(fixture.output.join("proof_status.toml")).unwrap();
        assert!(status.contains("audit_mode = \"cached\""), "{status}");

        // Break the proof on disk and DO NOT rebuild. A mode that trusted the
        // artifacts lying around would still report `proven`.
        std::fs::write(
            &fixture.proof,
            "import Pkg.Math\n\ntheorem foo_correct : Pkg.Math.foo_correct := by sorry\n",
        )
        .unwrap();

        let stale = run_proof_audit(&fixture.output, &fixture.package, AuditMode::Cached)
            .await
            .unwrap();
        assert_eq!(
            stale.sorry, 1,
            "in-place audit read a stale OLean instead of rebuilding the edited proof"
        );
        assert_eq!(stale.proven, 0);
    }

    #[tokio::test]
    async fn the_fast_audit_and_clean_room_agree_on_the_same_tree() {
        if std::process::Command::new("lake")
            .arg("--version")
            .output()
            .is_err()
        {
            return;
        }
        let fixture = RealAuditFixture::new(
            "import Pkg.Math\n\ntheorem foo_correct : Pkg.Math.foo_correct := by trivial\n",
        );
        let in_place = run_proof_audit(&fixture.output, &fixture.package, AuditMode::Cached)
            .await
            .unwrap();
        let clean_room = run_proof_audit(&fixture.output, &fixture.package, AuditMode::CleanRoom)
            .await
            .unwrap();
        // The fast path may reuse a BUILD; it may never reach a different
        // VERDICT.
        assert_eq!(
            (in_place.proven, in_place.sorry, in_place.suspicious),
            (clean_room.proven, clean_room.sorry, clean_room.suspicious),
        );
    }

    #[tokio::test]
    async fn audit_rebuild_emits_the_target_olean_without_target_c() {
        if std::process::Command::new("lake")
            .arg("--version")
            .output()
            .is_err()
        {
            return;
        }
        let fixture = RealAuditFixture::new(
            "import Pkg.Math\n\ntheorem foo_correct : Pkg.Math.foo_correct := by trivial\n",
        );
        let lake = move_prover_lean_backend::resolve_audit_lake_executable(&fixture.output)
            .await
            .unwrap();
        let module = "Pkg.Math_Proofs.foo_correct";
        let (artifact_dir, _) = rebuild_audit_modules(
            &lake,
            &fixture.output,
            &[(
                module.to_string(),
                fixture.proof.clone(),
                fixture.package.join("lean"),
            )],
            1,
        )
        .await
        .unwrap();

        assert!(lean_module_file(&artifact_dir, module, "olean")
            .unwrap()
            .is_file());
        assert!(
            !lean_module_file(&fixture.output.join(".lake/build/ir"), module, "c")
                .unwrap()
                .exists()
        );
    }

    #[tokio::test]
    async fn audit_rebuilds_instead_of_trusting_a_transplanted_olean() {
        if std::process::Command::new("lake")
            .arg("--version")
            .output()
            .is_err()
        {
            return;
        }
        let fixture = RealAuditFixture::new(
            "import Pkg.Math\n\ntheorem foo_correct : Pkg.Math.foo_correct := by trivial\n",
        );
        let target = "+Pkg.Math_Proofs.foo_correct";
        let first = move_prover_lean_backend::run_lake_command(
            &fixture.output,
            ["--reconfigure", "build", target],
        )
        .await
        .unwrap();
        assert!(
            first.status.success(),
            "initial fixture build failed:\nstdout:\n{}\nstderr:\n{}",
            String::from_utf8_lossy(&first.stdout),
            String::from_utf8_lossy(&first.stderr)
        );
        let olean = fixture
            .output
            .join(".lake/build/lib/lean/Pkg/Math_Proofs/foo_correct.olean");
        let proven_olean = fixture.package.join("proven.olean");
        std::fs::copy(&olean, &proven_olean).unwrap();

        std::fs::write(
            &fixture.proof,
            "import Pkg.Math\n\ntheorem foo_correct : Pkg.Math.foo_correct := by sorry\n",
        )
        .unwrap();
        let second = move_prover_lean_backend::run_lake_command(
            &fixture.output,
            ["--rehash", "build", target],
        )
        .await
        .unwrap();
        assert!(second.status.success());
        std::fs::copy(&proven_olean, &olean).unwrap();

        let summary = run_proof_audit(&fixture.output, &fixture.package, AuditMode::CleanRoom)
            .await
            .unwrap();

        assert_eq!(summary.proven, 0);
        assert_eq!(summary.sorry, 1);
    }

    #[test]
    fn theorem_status_precedence() {
        // Unexpected axioms dominate everything.
        assert_eq!(
            theorem_status(true, "mismatch", true, true, true),
            "suspicious"
        );
        // Statement mismatch is integrity: beats sorry.
        assert_eq!(
            theorem_status(false, "mismatch", true, true, true),
            "statement_mismatch"
        );
        // An incomplete statement check is its own class and, like a
        // mismatch, is never masked by the axiom classification -- but a
        // smuggled axiom still dominates it.
        assert_eq!(
            theorem_status(true, "unverified", false, false, false),
            "suspicious"
        );
        assert_eq!(
            theorem_status(false, "unverified", true, true, true),
            "statement_unverified"
        );
        assert_eq!(
            theorem_status(false, "unverified", false, false, false),
            "statement_unverified"
        );
        // Sorry/axiom classification stays orthogonal and precedes
        // conditional: a conditional proof containing sorryAx is sorry.
        assert_eq!(
            theorem_status(false, "conditional", true, false, true),
            "sorry"
        );
        // Conditional precedes declared (so --audit-strict-statements
        // cannot be masked by a declared axiom).
        assert_eq!(
            theorem_status(false, "conditional", false, true, true),
            "conditional"
        );
        assert_eq!(
            theorem_status(false, "conditional", false, false, true),
            "conditional"
        );
        assert_eq!(
            theorem_status(false, "exact", false, true, true),
            "declared"
        );
        assert_eq!(
            theorem_status(false, "exact", false, false, true),
            "smt_trusted"
        );
        assert_eq!(
            theorem_status(false, "exact", false, false, false),
            "proven"
        );
        assert_eq!(theorem_status(false, "exact", true, false, false), "sorry");
    }

    #[test]
    fn smt_trust_requires_the_pinned_source_and_rejects_overlay_shadowing() {
        let temp = tempfile::tempdir().unwrap();
        let output = temp.path().join("output");
        let overlay = temp.path().join("lean");
        let backend = Path::new(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .and_then(Path::parent)
            .unwrap();
        let dependencies = [
            (
                "batteries",
                backend.join("vendor/batteries").canonicalize().unwrap(),
                "lakefile.toml",
            ),
            (
                "aesop",
                backend.join("vendor/aesop").canonicalize().unwrap(),
                "lakefile.toml",
            ),
            (
                "auto",
                backend.join("vendor/lean-auto").canonicalize().unwrap(),
                "lakefile.lean",
            ),
        ];
        std::fs::create_dir_all(&output).unwrap();
        std::fs::create_dir_all(&overlay).unwrap();
        copy_move_auto_source_closure(backend, &output);
        let lakefile = dependencies
            .iter()
            .map(|(name, directory, _)| {
                format!("require {name} from \"{}\"\n", lake_path_literal(directory))
            })
            .collect::<String>();
        std::fs::write(output.join("lakefile.lean"), &lakefile).unwrap();
        let manifest = serde_json::json!({
            "version": "1.2.0",
            "packages": dependencies.iter().map(|(name, directory, config)| {
                serde_json::json!({
                    "type": "path",
                    "name": name,
                    "dir": directory,
                    "configFile": config,
                    "manifestFile": "lake-manifest.json"
                })
            }).collect::<Vec<_>>()
        });
        std::fs::write(
            output.join("lake-manifest.json"),
            serde_json::to_vec(&manifest).unwrap(),
        )
        .unwrap();

        assert!(pinned_smt_trust_is_source_backed(&output, &overlay));
        std::fs::write(
            output.join("lakefile.lean"),
            format!("{lakefile}require\textra from \"../extra\"\n"),
        )
        .unwrap();
        assert!(!pinned_smt_trust_is_source_backed(&output, &overlay));
        std::fs::write(output.join("lakefile.lean"), lakefile).unwrap();
        std::fs::write(output.join("Prover/MoveAuto.lean"), "import Auto.Tactic\n").unwrap();
        assert!(!pinned_smt_trust_is_source_backed(&output, &overlay));
        std::fs::write(
            output.join("Prover/MoveAuto.lean"),
            embedded_lemma_source("natives/Prover/MoveAuto.lean").unwrap(),
        )
        .unwrap();
        let shadow = overlay.join("Auto/Solver/SMT.lean");
        std::fs::create_dir_all(shadow.parent().unwrap()).unwrap();
        std::fs::write(shadow, "axiom autoSMTSorry : False\n").unwrap();
        assert!(!pinned_smt_trust_is_source_backed(&output, &overlay));
    }

    #[test]
    fn proof_status_toml_round_trips_multiline_and_control_text() {
        let document = ProofStatusDocument {
            audit_mode: AuditMode::CleanRoom.label().to_string(),
            proven: 1,
            conditional: 1,
            declared: 0,
            trusted: 0,
            smt_trusted: 0,
            sorry: 0,
            suspicious: 0,
            missing: 0,
            statement_mismatch: 0,
            statement_unverified: 0,
            spec_no_obligation: 1,
            warnings: vec!["warning with newline\nand tab\tand bell \u{7}".to_string()],
            unproduced_obligations: vec![ProofStatusUnproducedObligation {
                source: "Pkg::m::lemma\nspec".to_string(),
                reason: Some("no_target_and_no_ensures".to_string()),
            }],
            obligations: vec![ProofStatusObligation {
                name: "quoted_\"name".to_string(),
                module: "Pkg\\Math".to_string(),
                kind: "theorem".to_string(),
                reason: Some("line one\nline two".to_string()),
                status: "conditional".to_string(),
                statement_note: Some("timeout\nat isDefEq".to_string()),
                extra_hypotheses: vec![r#"h : a = "x" \ y"#.to_string()],
                declared_axioms: vec!["Declared.axiom".to_string()],
                smt_trusted_axioms: vec!["autoSMTSorry".to_string()],
                unexpected_axioms: vec!["unexpected\naxiom\t\u{1}".to_string()],
            }],
        };

        let encoded = toml::to_string_pretty(&document).unwrap();
        let decoded: ProofStatusDocument = toml::from_str(&encoded).unwrap();

        assert_eq!(decoded, document);
    }

    #[test]
    fn expected_roster_rejects_empty_and_misclassified_manifests() {
        let temp = tempfile::tempdir().unwrap();
        std::fs::write(
            temp.path().join("expected_obligations.toml"),
            r#"version = 1

[[expected]]
source = "Pkg::math::foo_spec"
target = "Pkg::math::foo"
kind = "theorem"
obligations = ["foo_correct"]
"#,
        )
        .unwrap();

        let empty = Manifest {
            obligation: vec![],
            spec_no_obligation: vec![],
        };
        let err = validate_expected_obligations(temp.path(), &empty).unwrap_err();
        assert!(err.to_string().contains("foo_spec"), "{err:#}");

        let wrong: Manifest = toml::from_str(
            r#"[[obligation]]
name = "foo_correct"
ir_name = "foo_correct"
kind = "trusted_axiom"
reason = "skip"
module = "Pkg.Math"
prop = "Pkg.Math.foo_correct"
lean_decl = "Pkg.Math.foo_correct_holds"
target = "Pkg.Math.foo"
target_source = "Pkg::math::wrong_target"
source = "Pkg::math::foo_spec"
"#,
        )
        .unwrap();
        let err = validate_expected_obligations(temp.path(), &wrong).unwrap_err();
        assert!(
            err.to_string().contains("expected kind `theorem`"),
            "{err:#}"
        );
        assert!(
            err.to_string().contains("expected target `Pkg::math::foo`"),
            "{err:#}"
        );
    }

    #[test]
    fn empty_manifest_is_clean_for_explicit_zero_obligation_source() {
        let temp = tempfile::tempdir().unwrap();
        std::fs::write(
            temp.path().join("expected_obligations.toml"),
            r#"version = 1

[[expected]]
source = "Pkg::math::reachability_spec"
target = "Pkg::math::reachability"
kind = "theorem"
obligations = []
"#,
        )
        .unwrap();
        validate_expected_obligations(
            temp.path(),
            &Manifest {
                obligation: vec![],
                spec_no_obligation: vec![],
            },
        )
        .unwrap();
    }

    #[test]
    fn expected_roster_requires_the_exact_obligation_identity_set() {
        let temp = tempfile::tempdir().unwrap();
        std::fs::write(
            temp.path().join("expected_obligations.toml"),
            r#"version = 1

[[expected]]
source = "Pkg::math::foo_spec"
target = "Pkg::math::foo"
kind = "theorem"
obligations = ["foo_asserts_correct", "foo_correct"]
"#,
        )
        .unwrap();
        let actual: Manifest = toml::from_str(
            r#"[[obligation]]
name = "foo_correct"
ir_name = "foo_correct"
kind = "theorem"
module = "Pkg.Math"
prop = "Pkg.Math.foo_correct"
lean_decl = "foo_correct"
target = "Pkg.Math.foo"
target_source = "Pkg::math::foo"
source = "Pkg::math::foo_spec"
"#,
        )
        .unwrap();
        let err = validate_expected_obligations(temp.path(), &actual).unwrap_err();
        assert!(err.to_string().contains("foo_asserts_correct"), "{err:#}");
        assert!(err.to_string().contains("foo_correct"), "{err:#}");
    }

    #[test]
    fn expected_roster_rejects_actual_source_not_in_authoritative_roster() {
        let temp = tempfile::tempdir().unwrap();
        std::fs::write(
            temp.path().join("expected_obligations.toml"),
            "version = 1\n",
        )
        .unwrap();
        let actual: Manifest = toml::from_str(
            r#"[[obligation]]
name = "unexpected_correct"
ir_name = "unexpected_correct"
kind = "theorem"
module = "Pkg.Math"
prop = "Pkg.Math.unexpected_correct"
lean_decl = "unexpected_correct"
target = "Pkg.Math.unexpected"
target_source = "Pkg::math::unexpected"
source = "Pkg::math::unexpected_spec"
"#,
        )
        .unwrap();
        let err = validate_expected_obligations(temp.path(), &actual).unwrap_err();
        assert!(
            err.to_string()
                .contains("absent from the authoritative roster"),
            "{err:#}"
        );
        assert!(err.to_string().contains("unexpected_correct"), "{err:#}");
    }
}
