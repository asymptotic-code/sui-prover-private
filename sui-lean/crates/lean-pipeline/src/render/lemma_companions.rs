//! Generator-conditional lemma imports.
//!
//! A `*Lemmas.lean` file under `lemmas/` proves theorems about GENERATED
//! defs. Historically the renderer copied every such file into every output
//! tree and imported none of them: the only way a client reached one was a
//! hand-written `import` in its proof overlay. Two separately-proven,
//! separately-useful modules (`Sui/WorldFrameLemmas.lean`, then
//! `MoveStdlib/U64PowLemmas.lean`) sat kernel-checked and invisible for
//! months because of it. This module is the reachability mechanism.
//!
//! NAMING CONVENTION. `<Lib>/<Module>Lemmas.lean` is the lemma COMPANION of
//! the Lean module `<Lib>.<Module>` -- its SUBJECT. `MoveStdlib/U64Lemmas.lean`
//! is the companion of `MoveStdlib.U64`, `Sui/BalanceLemmas.lean` of
//! `Sui.Balance`. The subject is derivable from the filename alone, which is
//! what makes the wiring mechanical rather than a hand-maintained table. Files
//! whose subject is NOT derivable that way (no such module, or several
//! subjects at once) carry an explicit [`REGISTRY`] entry; the conformance
//! test refuses a file that is neither.
//!
//! The namespace INSIDE a companion is deliberately not constrained --
//! `U64Lemmas.lean` keeps `namespace U64Pow` because every client citation
//! (`U64Pow.pow_val`) names it. The convention is about the file, i.e. the
//! module path an import must spell.
//!
//! REQUIREMENT CHECK (the tree-shaking guard). A companion cannot simply be
//! imported everywhere its subject is: per-package pruning drops whatever the
//! package does not reach, so `MoveStdlib.U64` is `pow` + loop helpers on
//! ember and just `min`/`max` on bluefin. A blanket
//! `import MoveStdlib.U64Lemmas` fails elaboration on the second. So each
//! companion's REQUIRED CONSTANTS are derived mechanically -- scan the file
//! for references to its subject's namespace -- and checked against the IR the
//! renderer is about to emit, which IS the shaken set. Requirements
//! unsatisfied means the file is neither copied nor imported, exactly as
//! today.
//!
//! NATIVES ATTRIBUTION. A subject's namespace is shared between the
//! generated module and its hand-written natives model
//! (`natives/<Lib>/<Module>Natives.lean` -- `Transfer.transfer_impl__ghost`
//! lives in `TransferNatives.lean`, not in the generated `Sui/Transfer.lean`).
//! Natives files ship with EVERY output tree and are never tree-shaken, so a
//! constant the natives model declares is corpus-independent: it can never be
//! the reason a companion fails to elaborate, and it is therefore NOT a
//! requirement on the generated subject. The scan resolves each reference
//! against the natives model first and only what remains becomes a
//! requirement. This cannot weaken the guard -- tree-shaking only ever
//! removes GENERATED declarations, which the natives model by definition
//! does not contain (and no `U64Natives.lean`/`BalanceNatives.lean` exists,
//! so the motivating `U64.pow` / `Balance.split` guards are untouched).
//!
//! ACYCLICITY. A companion imports its subject; a consumer imports both. No
//! generated module below a subject ever imports the subject's companion,
//! because the import is emitted only at the point where a dependency edge
//! `consumer -> subject` is already being emitted, and never for the subject
//! itself (self-deps are skipped upstream).

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};

use crate::ir::{ModId, Program};

use super::{RenderError, RenderResult};

/// Filename suffix that marks a proof-lemma companion.
pub const COMPANION_SUFFIX: &str = "Lemmas.lean";

/// What the renderer does with a companion once its subject is known.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Disposition {
    /// Copy the file and emit `import <companion>` into every generated
    /// module that imports one of its subjects -- when the requirement
    /// check passes.
    Wire,
    /// Registered (the subjects are known and the conformance test is
    /// satisfied) but deliberately NOT emitted. Carries the reason.
    Hold(&'static str),
}

/// An explicit registry entry. Only files whose subject is not derivable
/// from the naming convention, or whose disposition is not the default
/// `Wire`, need one.
pub struct RegistryEntry {
    /// Path relative to `lemmas/`, forward slashes.
    pub file: &'static str,
    /// Subject Lean module paths. Importing ANY of these pulls the
    /// companion in (subject to the requirement check).
    pub subjects: &'static [&'static str],
    pub disposition: Disposition,
}

/// Companions the naming convention cannot classify on its own.
pub const REGISTRY: &[RegistryEntry] = &[
    // `BalanceSupply` is not a module: this file is a second companion of
    // `Sui.Balance`, split out so a corpus that reaches `split`/`join` but
    // not the supply half still gets the half it can build.
    RegistryEntry {
        file: "natives/Sui/BalanceSupplyLemmas.lean",
        subjects: &["Sui.Balance"],
        disposition: Disposition::Wire,
    },
    // `Sui/WorldFrameLemmas.lean` -- the five-subject frame island that
    // motivated the `Hold` disposition -- was RETIRED by the Phase-3 lemma
    // wave landing: its 68 theorems were audited against the wave's world
    // and container frame batteries; the duplicated majority was deleted
    // and the unique remainder migrated beside the definitions
    // (`Prelude/World.lean`, `Sui/{Object,Table,Bag,Dynamic_field}Natives.lean`),
    // where the ordinary import graph reaches it. No companion currently
    // holds; `Disposition::Hold` remains for the next multi-subject or
    // blast-radius-gated companion.
];

/// Files under `lemmas/` that are neither a companion nor reachable from a
/// generated import, with the reason they may ship anyway. The conformance
/// test enumerates every other file and requires it to be reachable.
pub const REACHABILITY_ALLOWLIST: &[(&str, &str)] = &[
    // The five files under `natives/` that are neither a `<X>Natives.lean`
    // sibling nor a `<X>Lemmas.lean` companion. Four of them ARE module
    // files -- a hand-written `<Lib>/<Module>.lean` that the copy walk
    // installs where the renderer would otherwise emit a forwarding stub,
    // so an ordinary `import <Lib>.<Module>` dep edge reaches it (measured:
    // cetus imports `Prover.Prover`, bluefin imports `Prover.Vector_iter`).
    (
        "natives/Prover/Prover.lean",
        "module file for the native Move module `prover::prover`; reached by \
         the ordinary module dep edge, not a Natives sibling",
    ),
    (
        "natives/Prover/Ghost.lean",
        "module file for the native Move module `prover::ghost`; reached by \
         the ordinary module dep edge on any corpus with ghost vars",
    ),
    (
        "natives/Prover/Vector_iter.lean",
        "module file for the native Move module `prover::vector_iter`; reached \
         by the ordinary module dep edge",
    ),
    (
        "natives/Prover/MoveAuto.lean",
        "tactic library; reached by proof overlays via `import Prover.MoveAuto`, \
         never by generated code",
    ),
    (
        "natives/Prover/MoveAutoAttr.lean",
        "attribute declarations; imported by MoveAuto and by the companions that \
         tag `@[move_effect]`",
    ),
    (
        "README.md",
        "not a Lean module -- the lemma library's own documentation",
    ),
    (
        "native_model_policy.toml",
        "not a Lean module -- the trusted-native classification gate",
    ),
];

/// One companion file and the verdict the renderer reached about it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CompanionVerdict {
    /// Path relative to `lemmas/`, forward slashes.
    pub file: String,
    /// Lean module path of the companion itself.
    pub module: String,
    pub subjects: Vec<String>,
    /// Required constants, as `<namespace>.<decl>` pairs flattened to the
    /// dotted form they appear in inside the companion.
    pub requirements: Vec<String>,
    pub disposition: Disposition,
    /// `None` when the disposition is `Hold`. Otherwise the first
    /// requirement that the program does not satisfy, or `Some(Ok)`.
    pub unsatisfied: Vec<String>,
}

impl CompanionVerdict {
    /// Emit `import <module>` beside every import of a subject.
    pub fn wired(&self) -> bool {
        self.disposition == Disposition::Wire && self.unsatisfied.is_empty()
    }

    /// Copy the file into the output tree.
    ///
    /// Wider than [`wired`](Self::wired), deliberately. The only case that
    /// drops the copy is the one where the renderer POSITIVELY KNOWS the
    /// file cannot elaborate here: wire-eligible with a requirement the
    /// program does not satisfy. A `Hold` companion keeps shipping exactly
    /// as it did before this mechanism existed, because proof overlays
    /// hand-import it today (ember's `Vault_specs_Proofs.lean` imports
    /// `Sui.WorldFrameLemmas`) and withholding the file would turn a
    /// disposition decision into a client build break.
    pub fn copied(&self) -> bool {
        match self.disposition {
            Disposition::Wire => self.unsatisfied.is_empty(),
            Disposition::Hold(_) => true,
        }
    }
}

/// The renderer's decision about every companion in a lemmas tree.
#[derive(Debug, Default, Clone)]
pub(super) struct CompanionPlan {
    /// Subject module path -> companion module paths to import beside it.
    by_subject: BTreeMap<String, Vec<String>>,
    /// Source paths (relative to `lemmas/`) of the companions to copy.
    retained: BTreeSet<String>,
    verdicts: Vec<CompanionVerdict>,
}

impl CompanionPlan {
    /// Companion modules to import alongside `subject`.
    pub(super) fn companions_for(&self, subject: &str) -> &[String] {
        self.by_subject
            .get(subject)
            .map(Vec::as_slice)
            .unwrap_or(&[])
    }

    /// True when the companion at `relative` (path under `lemmas/`, forward
    /// slashes) must be copied into the output tree.
    pub(super) fn retains(&self, relative: &str) -> bool {
        self.retained.contains(relative)
    }

    pub(super) fn verdicts(&self) -> &[CompanionVerdict] {
        &self.verdicts
    }

    /// Build the plan for `program` against the companions found under
    /// `lemmas_dir`. An empty plan (no copies, no imports) is the correct
    /// answer when there is no lemmas tree.
    pub(super) fn build(program: &Program, lemmas_dir: Option<&Path>) -> RenderResult<Self> {
        let Some(root) = lemmas_dir else {
            return Ok(Self::default());
        };
        if !root.is_dir() {
            return Ok(Self::default());
        }

        let mut files = Vec::new();
        collect_companion_files(root, root, &mut files)?;
        files.sort();

        let subject_index = subject_index(program);
        let mut plan = Self::default();
        for relative in files {
            let source = root.join(&relative);
            let text = std::fs::read_to_string(&source).map_err(|error| RenderError::Io {
                what: format!("read({}): {}", source.display(), error),
            })?;
            let verdict = classify(&relative, &text, program, &subject_index, root)?;
            if verdict.copied() {
                plan.retained.insert(verdict.file.clone());
            }
            if verdict.wired() {
                for subject in &verdict.subjects {
                    plan.by_subject
                        .entry(subject.clone())
                        .or_default()
                        .push(verdict.module.clone());
                }
            }
            plan.verdicts.push(verdict);
        }
        for companions in plan.by_subject.values_mut() {
            companions.sort();
            companions.dedup();
        }
        Ok(plan)
    }
}

/// Why each companion was or was not wired for `program`. Same computation
/// the renderer acts on -- a diagnosis that could disagree with the decision
/// would be worse than none.
pub fn explain(
    program: &Program,
    lemmas_dir: Option<&Path>,
) -> RenderResult<Vec<CompanionVerdict>> {
    Ok(CompanionPlan::build(program, lemmas_dir)?.verdicts)
}

/// Classify one companion file. Public to the crate's tests through
/// [`explain`]; the conformance test reads the same verdicts the renderer
/// acted on rather than recomputing them.
fn classify(
    relative: &str,
    text: &str,
    program: &Program,
    subject_index: &BTreeMap<String, ModId>,
    lemmas_root: &Path,
) -> RenderResult<CompanionVerdict> {
    let module = companion_module_path(relative).ok_or_else(|| RenderError::Io {
        what: format!(
            "lemma companion `{}` is not under a `<Lib>/` directory; the \
             `<Lib>/<Module>Lemmas.lean` convention gives it no module path",
            relative
        ),
    })?;

    let entry = REGISTRY.iter().find(|entry| entry.file == relative);
    let (subjects, disposition) = match entry {
        Some(entry) => (
            entry.subjects.iter().map(|s| s.to_string()).collect(),
            entry.disposition,
        ),
        None => {
            let subject = derived_subject(relative).ok_or_else(|| RenderError::Io {
                what: format!(
                    "lemma companion `{}` has no subject: its name does not \
                     match `<Lib>/<Module>Lemmas.lean` and it carries no entry \
                     in the companion registry (render/lemma_companions.rs)",
                    relative
                ),
            })?;
            (vec![subject], Disposition::Wire)
        }
    };

    let body = strip_comments(text);
    let mut requirements = Vec::new();
    let mut unsatisfied = Vec::new();
    for subject in &subjects {
        let namespace = subject_namespace(subject);
        // One body walk per subject, not per constant.
        let aliases = subject_index
            .get(subject)
            .map(|mid| super::module_opaque_const_aliases(program, *mid));
        let natives = natives_declarations(lemmas_root, subject);
        for constant in scan_subject_references(&body, &namespace) {
            // A constant the subject's natives model declares is
            // corpus-independent framework content (the natives file ships
            // with every output tree, untouched by tree-shaking) -- it is a
            // reference, not a requirement.
            if natives_declares(&natives, &namespace, &constant) {
                continue;
            }
            let dotted = format!("{}.{}", namespace, constant);
            if !requirements.contains(&dotted) {
                requirements.push(dotted.clone());
            }
            let satisfied = match (subject_index.get(subject), aliases.as_ref()) {
                (Some(mid), Some(aliases)) => module_declares(program, *mid, &constant, aliases),
                _ => false,
            };
            if !satisfied && !unsatisfied.contains(&dotted) {
                unsatisfied.push(dotted);
            }
        }
    }
    // A subject the program does not contain at all cannot be imported, so
    // the companion cannot ride along with it either. Record it as an
    // unsatisfied requirement so the verdict says why.
    for subject in &subjects {
        if !subject_index.contains_key(subject) {
            let missing = format!("{} (subject module absent)", subject);
            if !unsatisfied.contains(&missing) {
                unsatisfied.push(missing);
            }
        }
    }

    Ok(CompanionVerdict {
        file: relative.to_string(),
        module,
        subjects,
        requirements,
        disposition,
        unsatisfied,
    })
}

/// `natives/MoveStdlib/U64Lemmas.lean` -> `MoveStdlib.U64Lemmas`.
pub fn companion_module_path(relative: &str) -> Option<String> {
    let stem = relative.strip_suffix(".lean")?;
    let mut parts: Vec<&str> = stem.split('/').collect();
    let file = parts.pop()?;
    let lib = parts.pop()?;
    if lib == "natives" || lib.is_empty() {
        return None;
    }
    Some(format!("{}.{}", lib, file))
}

/// `natives/MoveStdlib/U64Lemmas.lean` -> `MoveStdlib.U64`, when that is a
/// well-formed module path. Returns `None` for a bare `Lemmas.lean`.
pub fn derived_subject(relative: &str) -> Option<String> {
    let module = companion_module_path(relative)?;
    let (lib, file) = module.split_once('.')?;
    let stem = file.strip_suffix("Lemmas")?;
    if stem.is_empty() {
        return None;
    }
    Some(format!("{}.{}", lib, stem))
}

/// The Lean namespace a subject module's declarations live in. For the
/// lemma packages (`Sui`, `MoveStdlib`, `Prover`) that is the bare module
/// stem; user packages are package-qualified.
fn subject_namespace(subject: &str) -> String {
    match subject.split_once('.') {
        Some((pkg, stem)) if super::escape::is_lemma_package(pkg) => stem.to_string(),
        Some((pkg, stem)) => format!("{}.{}", pkg, stem),
        None => subject.to_string(),
    }
}

/// Map every module the program will emit to its import path.
fn subject_index(program: &Program) -> BTreeMap<String, ModId> {
    let mut index = BTreeMap::new();
    for (mid, module) in &program.modules {
        let location = super::module_render_location(&module.package_name, &module.name);
        index.insert(location.import_path, *mid);
    }
    index
}

/// Does the module `mid` declare `constant` (a dotted name relative to the
/// module's namespace)?
///
/// Three ways to be declared, matching the three kinds of thing a rendered
/// module file contains: a function (including every `.aborts` / `.while_N` /
/// `.after` companion, which carry their suffix in the IR name), an opaque
/// wide-literal alias (and its `_val` theorem), or a struct (whose
/// constructors, variants and fields are reached through it).
///
/// THE COMPARISON IS AGAINST THE RENDERED SPELLING, NOT THE IR NAME. A
/// companion cites the constant as the output tree spells it, and the
/// renderer escapes on the way out: `escape_struct_name` prefixes every
/// Lean-builtin collision (`option::Option` renders as `MoveOption.MoveOption`
/// -- module AND struct), `escape_identifier` rewrites keyword and
/// `$`/`#`/`::` identifiers. Comparing the raw IR name made
/// `MoveOptionLemmas.lean` fail its own requirement check on every corpus:
/// the struct is `Option` in the IR and `MoveOption` in the file the
/// companion imports, so the guard withheld a file that elaborates fine (and
/// that three clients hand-import).
fn module_declares(
    program: &Program,
    mid: ModId,
    constant: &str,
    aliases: &BTreeMap<String, (u32, String)>,
) -> bool {
    // `.eq_def` is Lean's own equation lemma for a `partial_fixpoint` def,
    // not a rendered declaration -- strip it and require the def itself.
    let constant = constant.strip_suffix(".eq_def").unwrap_or(constant);

    if program
        .functions
        .values()
        .any(|f| f.module == mid && super::escape::escape_identifier(&f.name) == constant)
    {
        return true;
    }

    if aliases.contains_key(constant)
        || constant
            .strip_suffix("_val")
            .is_some_and(|base| aliases.contains_key(base))
    {
        return true;
    }

    let head = constant.split('.').next().unwrap_or(constant);
    program
        .structs
        .values()
        .any(|s| s.module_id == mid && super::escape::escape_struct_name(&s.name) == head)
}

/// The subject's hand-written natives model, relative to `lemmas/`.
/// `Sui.Transfer` -> `natives/Sui/TransferNatives.lean`.
fn natives_sibling(subject: &str) -> Option<String> {
    let (lib, stem) = subject.split_once('.')?;
    Some(format!("natives/{}/{}Natives.lean", lib, stem))
}

/// Fully-qualified names the subject's natives model declares. Empty when
/// the subject has no natives sibling.
fn natives_declarations(lemmas_root: &Path, subject: &str) -> BTreeSet<String> {
    let Some(relative) = natives_sibling(subject) else {
        return BTreeSet::new();
    };
    let path = lemmas_root.join(relative);
    let Ok(text) = std::fs::read_to_string(&path) else {
        return BTreeSet::new();
    };
    declared_names(&strip_comments(&text))
}

/// Is `constant` (dotted, relative to `namespace`) declared by the natives
/// model? Exact name, or -- mirroring [`module_declares`]'s struct rule --
/// a declaration that heads the dotted path (fields, constructors and
/// projections are reached through their parent).
fn natives_declares(natives: &BTreeSet<String>, namespace: &str, constant: &str) -> bool {
    if natives.is_empty() {
        return false;
    }
    let constant = constant.strip_suffix(".eq_def").unwrap_or(constant);
    if natives.contains(&format!("{}.{}", namespace, constant)) {
        return true;
    }
    let head = constant.split('.').next().unwrap_or(constant);
    natives.contains(&format!("{}.{}", namespace, head))
}

/// Namespace-aware declaration census of a Lean source file (comments
/// already stripped). Tracks `namespace`/`section`/`end` nesting and records
/// each declaration under its fully-qualified name.
fn declared_names(body: &str) -> BTreeSet<String> {
    const KEYWORDS: &[&str] = &[
        "def",
        "theorem",
        "lemma",
        "abbrev",
        "structure",
        "inductive",
        "opaque",
        "axiom",
        "instance",
        "class",
    ];
    const MODIFIERS: &[&str] = &[
        "private",
        "protected",
        "noncomputable",
        "partial",
        "unsafe",
        "scoped",
        "local",
    ];
    let mut out = BTreeSet::new();
    // (contributes_to_prefix, name); anonymous sections carry an empty name.
    let mut stack: Vec<(bool, String)> = Vec::new();
    for raw in body.lines() {
        let line = raw.trim();
        if let Some(rest) = line.strip_prefix("namespace ") {
            let name = leading_dotted_ident(rest);
            if !name.is_empty() {
                stack.push((true, name));
            }
            continue;
        }
        if line == "section" {
            stack.push((false, String::new()));
            continue;
        }
        if let Some(rest) = line.strip_prefix("section ") {
            stack.push((false, leading_dotted_ident(rest)));
            continue;
        }
        if line == "end" {
            if let Some(position) = stack.iter().rposition(|(_, name)| name.is_empty()) {
                stack.remove(position);
            }
            continue;
        }
        if let Some(rest) = line.strip_prefix("end ") {
            let name = leading_dotted_ident(rest);
            if let Some(position) = stack.iter().rposition(|(_, frame)| *frame == name) {
                stack.truncate(position);
            }
            continue;
        }

        // Strip leading attribute groups, then modifiers, then match a
        // declaration keyword and take its name.
        let mut rest = line;
        while rest.starts_with("@[") {
            let Some(close) = matching_bracket(rest) else {
                break;
            };
            rest = rest[close + 1..].trim_start();
        }
        loop {
            let mut stripped = false;
            for modifier in MODIFIERS {
                if let Some(after) = rest.strip_prefix(modifier) {
                    if after.starts_with(' ') {
                        rest = after.trim_start();
                        stripped = true;
                    }
                }
            }
            if !stripped {
                break;
            }
        }
        for keyword in KEYWORDS {
            if let Some(after) = rest.strip_prefix(keyword) {
                if !after.starts_with(' ') {
                    continue;
                }
                let name = leading_dotted_ident(after.trim_start());
                if name.is_empty() {
                    continue;
                }
                let prefix: Vec<&str> = stack
                    .iter()
                    .filter(|(contributes, _)| *contributes)
                    .map(|(_, frame)| frame.as_str())
                    .collect();
                let full = if prefix.is_empty() {
                    name
                } else {
                    format!("{}.{}", prefix.join("."), name)
                };
                out.insert(full);
                break;
            }
        }
    }
    out
}

/// The dotted identifier a line starts with, if any.
fn leading_dotted_ident(text: &str) -> String {
    let bytes = text.as_bytes();
    if bytes.is_empty() || !is_ident_start(bytes[0]) {
        return String::new();
    }
    let mut end = 0usize;
    while end < bytes.len() {
        let byte = bytes[end];
        if is_ident_byte(byte)
            || (byte == b'.' && end + 1 < bytes.len() && is_ident_start(bytes[end + 1]))
        {
            end += 1;
        } else {
            break;
        }
    }
    text[..end].trim_end_matches('.').to_string()
}

/// Index of the `]` closing the `@[` a string starts with.
fn matching_bracket(text: &str) -> Option<usize> {
    let bytes = text.as_bytes();
    let mut depth = 0usize;
    for (index, byte) in bytes.iter().enumerate() {
        match byte {
            b'[' => depth += 1,
            b']' => {
                depth -= 1;
                if depth == 0 {
                    return Some(index);
                }
            }
            _ => {}
        }
    }
    None
}

/// Collect every `<namespace>.<dotted>` reference in `body`, with or without
/// a `_root_.` prefix. This is the mechanical requirement derivation: what a
/// companion names from its subject is what its subject must still declare.
fn scan_subject_references(body: &str, namespace: &str) -> Vec<String> {
    let mut out = Vec::new();
    let bytes = body.as_bytes();
    let mut search = 0usize;
    while let Some(found) = body[search..].find(namespace) {
        let start = search + found;
        search = start + namespace.len();

        // Must be preceded by a boundary, or by exactly `_root_.`.
        let preceded_ok = if start == 0 {
            true
        } else {
            let head = &body[..start];
            if head.ends_with("_root_.") {
                let before = head.len() - "_root_.".len();
                before == 0 || !is_ident_byte(bytes[before - 1])
            } else {
                !is_ident_byte(bytes[start - 1]) && bytes[start - 1] != b'.'
            }
        };
        if !preceded_ok {
            continue;
        }

        let rest = &body[search..];
        let Some(tail) = rest.strip_prefix('.') else {
            continue;
        };
        let mut end = 0usize;
        let tail_bytes = tail.as_bytes();
        while end < tail_bytes.len() {
            let byte = tail_bytes[end];
            if is_ident_byte(byte) {
                end += 1;
            } else if byte == b'.'
                && end + 1 < tail_bytes.len()
                && is_ident_start(tail_bytes[end + 1])
            {
                end += 1;
            } else {
                break;
            }
        }
        if end == 0 || !is_ident_start(tail_bytes[0]) {
            continue;
        }
        let constant = tail[..end].trim_end_matches('.').to_string();
        if !constant.is_empty() && !out.contains(&constant) {
            out.push(constant);
        }
    }
    out.sort();
    out
}

fn is_ident_byte(byte: u8) -> bool {
    byte.is_ascii_alphanumeric() || byte == b'_' || byte == b'\''
}

fn is_ident_start(byte: u8) -> bool {
    byte.is_ascii_alphabetic() || byte == b'_'
}

/// Drop Lean comments so a docstring naming a constant the corpus does not
/// have cannot manufacture a requirement. Handles nested `/- -/` blocks
/// (including `/-- -/` docstrings) and `--` line comments.
fn strip_comments(text: &str) -> String {
    let bytes = text.as_bytes();
    let mut out = String::with_capacity(text.len());
    let mut index = 0usize;
    let mut depth = 0usize;
    while index < bytes.len() {
        if bytes[index..].starts_with(b"/-") {
            depth += 1;
            index += 2;
            continue;
        }
        if depth > 0 {
            if bytes[index..].starts_with(b"-/") {
                depth -= 1;
                index += 2;
                continue;
            }
            index += 1;
            continue;
        }
        if bytes[index..].starts_with(b"--") {
            while index < bytes.len() && bytes[index] != b'\n' {
                index += 1;
            }
            continue;
        }
        let ch_len = utf8_len(bytes[index]);
        out.push_str(&text[index..index + ch_len]);
        index += ch_len;
    }
    out
}

fn utf8_len(first: u8) -> usize {
    match first {
        0x00..=0x7f => 1,
        0xc0..=0xdf => 2,
        0xe0..=0xef => 3,
        _ => 4,
    }
}

/// Every `*Lemmas.lean` under `root`, as `/`-joined paths relative to it.
pub(super) fn collect_companion_files(
    root: &Path,
    dir: &Path,
    out: &mut Vec<String>,
) -> RenderResult<()> {
    let entries = std::fs::read_dir(dir).map_err(|error| RenderError::Io {
        what: format!("read_dir({}): {}", dir.display(), error),
    })?;
    for entry in entries {
        let entry = entry.map_err(|error| RenderError::Io {
            what: format!("read_dir entry under {}: {}", dir.display(), error),
        })?;
        let path = entry.path();
        if path.is_dir() {
            collect_companion_files(root, &path, out)?;
            continue;
        }
        let Some(name) = path.file_name().and_then(|n| n.to_str()) else {
            continue;
        };
        if !name.ends_with(COMPANION_SUFFIX) {
            continue;
        }
        let relative = path
            .strip_prefix(root)
            .map_err(|_| RenderError::Io {
                what: format!("{} is not under {}", path.display(), root.display()),
            })?
            .components()
            .map(|c| c.as_os_str().to_string_lossy().into_owned())
            .collect::<Vec<_>>()
            .join("/");
        out.push(relative);
    }
    Ok(())
}

/// Relative path (under `lemmas/`) of a file the copy walk is about to
/// write, given the lemmas root. `None` when the path is not under it.
pub(super) fn relative_to_root(root: &Path, path: &Path) -> Option<String> {
    let relative: PathBuf = path.strip_prefix(root).ok()?.to_path_buf();
    Some(
        relative
            .components()
            .map(|c| c.as_os_str().to_string_lossy().into_owned())
            .collect::<Vec<_>>()
            .join("/"),
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn convention_derives_module_and_subject() {
        assert_eq!(
            companion_module_path("natives/MoveStdlib/U64Lemmas.lean").as_deref(),
            Some("MoveStdlib.U64Lemmas")
        );
        assert_eq!(
            derived_subject("natives/MoveStdlib/U64Lemmas.lean").as_deref(),
            Some("MoveStdlib.U64")
        );
        assert_eq!(
            derived_subject("natives/Sui/BalanceLemmas.lean").as_deref(),
            Some("Sui.Balance")
        );
        assert_eq!(
            derived_subject("natives/Prover/AbortLemmas.lean").as_deref(),
            Some("Prover.Abort")
        );
        // A bare `Lemmas.lean` names no module.
        assert_eq!(derived_subject("natives/Sui/Lemmas.lean"), None);
    }

    #[test]
    fn comments_never_manufacture_a_requirement() {
        let text = "-- mentions U64.pow_from_a_comment\n\
                    /-- doc mentions U64.pow_from_a_docstring -/\n\
                    theorem t : U64.pow.aborts = 0 := rfl\n";
        let body = strip_comments(text);
        assert_eq!(
            scan_subject_references(&body, "U64"),
            vec!["pow.aborts".to_string()]
        );
    }

    #[test]
    fn scan_reads_both_root_prefixed_and_bare_references() {
        let body = "theorem t (x : _root_.Balance.Balance t) :\n\
                    Balance.split.aborts t x = _root_.Balance.join.aborts t x := rfl\n";
        assert_eq!(
            scan_subject_references(body, "Balance"),
            vec![
                "Balance".to_string(),
                "join.aborts".to_string(),
                "split.aborts".to_string()
            ]
        );
    }

    #[test]
    fn scan_does_not_match_a_longer_namespace() {
        // `U64Pow` is this file's own namespace; it must not be read as a
        // reference into `U64`.
        let body = "theorem U64Pow.pow_val : True := trivial\n";
        assert!(scan_subject_references(body, "U64").is_empty());
    }

    #[test]
    fn a_held_companion_is_copied_but_never_wired() {
        // No in-tree companion currently holds (WorldFrameLemmas, the
        // motivating island, was retired by the lemma-wave landing), but the
        // disposition stays for the next blast-radius-gated companion: a
        // held file keeps shipping (overlays may hand-import it) while its
        // import is withheld.
        let verdict = CompanionVerdict {
            file: "natives/Sui/ExampleLemmas.lean".to_string(),
            module: "Sui.ExampleLemmas".to_string(),
            subjects: vec!["Sui.Example".to_string()],
            requirements: vec![],
            disposition: Disposition::Hold("blast radius pending measurement"),
            unsatisfied: vec![],
        };
        assert!(verdict.copied());
        assert!(!verdict.wired());
    }

    #[test]
    fn natives_census_tracks_namespaces_attributes_and_dotted_defs() {
        let text = "namespace Transfer\n\
                    structure Receiving (T : Type) where\n\
                    \x20 value : T\n\
                    instance (T : Type) : Inhabited (Receiving T) where default := d\n\
                    @[simp] def Object.toEntry (t : Type) : Nat := 0\n\
                    private def transfer_impl__ghost (t : Type) : Nat := 0\n\
                    namespace WorldWriterLemmas\n\
                    theorem inner_face : True := trivial\n\
                    end WorldWriterLemmas\n\
                    section\n\
                    def in_anon_section : Nat := 0\n\
                    end\n\
                    end Transfer\n\
                    def at_root : Nat := 0\n";
        let names = declared_names(text);
        assert!(names.contains("Transfer.Receiving"));
        assert!(names.contains("Transfer.Object.toEntry"));
        assert!(names.contains("Transfer.transfer_impl__ghost"));
        assert!(names.contains("Transfer.WorldWriterLemmas.inner_face"));
        assert!(names.contains("Transfer.in_anon_section"));
        assert!(names.contains("at_root"));
        // The unnamed instance contributes no name.
        assert!(!names.iter().any(|n| n.contains('(')));
    }

    #[test]
    fn natives_declared_constants_are_references_not_requirements() {
        let natives: BTreeSet<String> = [
            "Transfer.transfer_impl__ghost".to_string(),
            "Transfer.Object.toEntry".to_string(),
            "Transfer.Receiving".to_string(),
        ]
        .into_iter()
        .collect();
        // Exact name.
        assert!(natives_declares(
            &natives,
            "Transfer",
            "transfer_impl__ghost"
        ));
        assert!(natives_declares(&natives, "Transfer", "Object.toEntry"));
        // Struct-head rule: fields/ctors reached through their parent.
        assert!(natives_declares(&natives, "Transfer", "Receiving.value"));
        // `.eq_def` rides on the declaration itself.
        assert!(natives_declares(
            &natives,
            "Transfer",
            "transfer_impl__ghost.eq_def"
        ));
        // A generated-owned name stays a requirement.
        assert!(!natives_declares(&natives, "Transfer", "public_transfer"));
        assert!(!natives_declares(
            &natives,
            "Transfer",
            "public_transfer.aborts"
        ));
        // No natives sibling at all: nothing resolves.
        assert!(!natives_declares(&BTreeSet::new(), "U64", "pow"));
    }

    #[test]
    fn subjects_without_a_natives_sibling_keep_their_full_requirement_set() {
        // The motivating guards must be untouched: no `U64Natives.lean` or
        // `BalanceNatives.lean` exists, so `U64.pow` / `Balance.split` remain
        // requirements on the generated modules.
        let root = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("lemmas");
        assert!(natives_declarations(&root, "MoveStdlib.U64").is_empty());
        assert!(natives_declarations(&root, "Sui.Balance").is_empty());
        // And the fixed case really is resolved by its natives model.
        let transfer = natives_declarations(&root, "Sui.Transfer");
        assert!(transfer.contains("Transfer.transfer_impl__ghost"));
        assert!(transfer.contains("Transfer.Object.toEntry"));
        assert!(!transfer.contains("Transfer.public_transfer"));
    }

    #[test]
    fn every_registry_entry_names_a_real_convention_gap_or_a_hold() {
        for entry in REGISTRY {
            assert!(
                entry.file.ends_with(COMPANION_SUFFIX),
                "registry entry {} is not a companion file",
                entry.file
            );
            let derived = derived_subject(entry.file);
            let overrides_subject = derived
                .as_deref()
                .is_none_or(|subject| entry.subjects != [subject]);
            let holds = matches!(entry.disposition, Disposition::Hold(_));
            assert!(
                overrides_subject || holds,
                "registry entry {} restates what the convention already derives",
                entry.file
            );
        }
    }
}
