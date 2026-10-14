//! Optional total-`def` emission for self-recursive loop helpers.
//!
//! By default the renderer emits a self-recursive loop helper
//! (`<fn>.while_N`, and its `.aborts` companion) as
//! `def … partial_fixpoint` -- a denotational fixpoint that needs no
//! termination argument, is computable (`#eval` works, so the `--test`
//! pipeline runs), and exposes `.eq_def` so spec proofs can unfold it.
//! That stays the default in the proof and test generation modes.
//!
//! This module adds an OPT-IN upgrade for PROOF-mode generation: a loop
//! helper can instead be emitted as a genuinely total
//! `def … termination_by <measure> decreasing_by <tactic>` when a human
//! has supplied a real (non-`sorry`) measure + decreasing proof for it.
//! A loop's `.aborts` companion (`<fn>.aborts.while_N`) is the SAME carry
//! recursion as the value loop (`<fn>.while_N`) -- same params, same
//! recursive args, same guard -- so it inherits the value loop's single
//! registry entry automatically (one entry upgrades both `def`s; an
//! explicit abort-key entry still wins if a loop ever needs a distinct
//! proof). See [`aborts_companion_value_key`].
//! A total def carries a real termination certificate (the loop provably
//! terminates -- no junk value on divergence) while still exposing
//! `.eq_def`. It is NEVER used in `--test` mode: a `sorry` anywhere in the
//! termination argument poisons `#eval` (the kernel refuses to evaluate an
//! expression depending on the `sorry` axiom), which would break the test
//! drivers -- so test generation is hard-locked to `partial_fixpoint`.
//!
//! A third, deliberately narrow `Execution` mode exists for semantic runtime
//! checks whose call graph has already been sliced away from the proof
//! surface. It renders every recursive function/SCC as opaque `partial def`.
//! This avoids elaborating fixpoint or human termination proofs, but also
//! gives up their proof-facing equations; it must therefore never replace an
//! authoritative `Proof` render.
//!
//! ## Why a registry, and why inline
//!
//! The measure expression and the decreasing tactic are loop-specific and
//! cannot be derived by the renderer. They live in a per-package registry
//! data file (one block per loop helper) so they survive regeneration: the
//! renderer rewrites the generated `def` every run but never touches the
//! registry. This mirrors the seed-and-reconcile `<Mod>_Proofs.lean`
//! discipline -- the hand-written proof content lives outside the generated
//! output and is referenced/spliced by stable name.
//!
//! The measure + tactic are INLINED into the `termination_by` /
//! `decreasing_by` clauses (rather than referenced as named lemmas in a
//! sibling Lean file) for two reasons:
//!   1. No import cycle. A named measure lemma would need the loop's
//!      parameter struct types (module-defined), forcing a sidecar that
//!      imports the module while the module's `termination_by` references
//!      the sidecar -- a cycle. Inlining sidesteps it entirely.
//!   2. No guard-signature guessing. The `decreasing_by` tactic runs in a
//!      context that already has the loop's path conditions (the `if guard`
//!      leading to the recursive call) as hypotheses, so the inlined tactic
//!      can just `omega` / `assumption` over them -- the renderer never has
//!      to know how many guard hypotheses a named lemma would take.
//!
//! ## Stability across regeneration
//!
//! The registry is keyed by the STABLE loop-helper name
//! `<pkg>.<module>.<fn>.while_N` (derived from the Move source, not from an
//! allocation-order id). As long as the Move source's loops don't change,
//! the key is stable and the human's measure/proof is reused verbatim every
//! run. If the Move source adds/removes/reorders a loop the suffix can
//! shift and orphan an entry -- [`report_orphans`] warns loudly so the
//! human notices (the measure needs review anyway) rather than silently
//! regressing to `partial_fixpoint`.

use std::collections::BTreeMap;
use std::path::Path;

use crate::ir::{Function, Program};

/// Which generation mode the renderer is running in.
///
/// `Test` hard-locks recursive functions to `partial_fixpoint` (so `#eval`
/// stays sound), while `Proof` allows the opt-in total-`def` upgrade.
/// `Execution` is an explicit runtime-only boundary: every recursive
/// function/SCC is emitted as opaque `partial def`, never
/// `partial_fixpoint` or a human termination proof. Non-recursive
/// definitions are unaffected.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LoopMode {
    Proof,
    Test,
    Execution,
}

/// A human-supplied termination measure + decreasing proof for one loop
/// helper. Both are verbatim Lean text spliced into the emitted
/// `termination_by` / `decreasing_by` clauses.
#[derive(Debug, Clone)]
pub struct TerminationEntry {
    pub measure: String,
    pub decreasing: String,
}

impl TerminationEntry {
    /// A loop is upgraded to a total `def` only when BOTH the measure and
    /// the decreasing proof are present and non-`sorry`. An entry that is
    /// still a `sorry` placeholder (the seeded template state) is treated
    /// as absent, so a freshly-seeded registry produces output identical
    /// to the `partial_fixpoint` default -- no `sorry` regression.
    pub fn is_ready(&self) -> bool {
        let m = self.measure.trim();
        let d = self.decreasing.trim();
        !m.is_empty() && !d.is_empty() && m != "sorry" && d != "sorry"
    }
}

/// Parsed registry: loop-helper key -> entry.
#[derive(Debug, Clone, Default)]
pub struct LoopTerminationRegistry {
    entries: BTreeMap<String, TerminationEntry>,
}

impl LoopTerminationRegistry {
    pub fn get(&self, key: &str) -> Option<&TerminationEntry> {
        self.entries.get(key)
    }

    pub fn keys(&self) -> impl Iterator<Item = &String> {
        self.entries.keys()
    }

    /// Parse the block-delimited registry text. Format (lines outside a
    /// block starting with `#` are comments):
    ///
    /// ```text
    /// @loop <pkg>.<module>.<fn>.while_N
    /// @measure
    /// <lean expression, possibly multi-line>
    /// @decreasing
    /// <lean tactic block, possibly multi-line>
    /// @end
    /// ```
    ///
    /// `@signature` lines (informational) are accepted and ignored.
    pub fn parse(content: &str) -> Self {
        #[derive(PartialEq)]
        enum St {
            Outside,
            Measure,
            Decreasing,
        }
        let mut entries = BTreeMap::new();
        let mut st = St::Outside;
        let mut key = String::new();
        let mut measure: Vec<&str> = Vec::new();
        let mut decreasing: Vec<&str> = Vec::new();

        let flush = |entries: &mut BTreeMap<String, TerminationEntry>,
                     key: &str,
                     measure: &[&str],
                     decreasing: &[&str]| {
            if !key.is_empty() {
                entries.insert(
                    key.to_string(),
                    TerminationEntry {
                        measure: measure.join("\n").trim().to_string(),
                        decreasing: decreasing.join("\n").trim().to_string(),
                    },
                );
            }
        };

        for raw in content.lines() {
            let line = raw.trim_end();
            let trimmed = line.trim_start();
            if let Some(rest) = trimmed.strip_prefix("@loop") {
                // Starting a new block flushes the previous one.
                flush(&mut entries, &key, &measure, &decreasing);
                key = rest.trim().to_string();
                measure.clear();
                decreasing.clear();
                st = St::Outside;
                continue;
            }
            if trimmed.starts_with("@signature") {
                continue;
            }
            if trimmed == "@measure" {
                st = St::Measure;
                continue;
            }
            if trimmed == "@decreasing" {
                st = St::Decreasing;
                continue;
            }
            if trimmed == "@end" {
                flush(&mut entries, &key, &measure, &decreasing);
                key.clear();
                measure.clear();
                decreasing.clear();
                st = St::Outside;
                continue;
            }
            match st {
                St::Measure => measure.push(line),
                St::Decreasing => decreasing.push(line),
                // Outside any value section: ignore comments / blank lines.
                St::Outside => {}
            }
        }
        // Trailing block without an explicit `@end`.
        flush(&mut entries, &key, &measure, &decreasing);
        Self { entries }
    }

    /// Load a registry from `path`. A missing file is not an error -- it
    /// yields an empty registry, so every loop falls back to
    /// `partial_fixpoint` (the zero-config default).
    pub fn load(path: &Path) -> Self {
        match std::fs::read_to_string(path) {
            Ok(s) => Self::parse(&s),
            Err(_) => Self::default(),
        }
    }
}

/// The stable registry key for a loop helper: `<pkg>.<module>.<name>`.
/// Returns `None` when the function's module is unknown.
pub fn loop_key(program: &Program, func: &Function) -> Option<String> {
    let m = program.modules.get(&func.module)?;
    Some(format!("{}.{}.{}", m.package_name, m.name, func.name))
}

/// The value-loop key an abort-companion loop helper inherits from, or
/// `None` if `key` is not an abort loop. The `.aborts` companion
/// (`<fn>.aborts.while_N`) is the SAME carry recursion as the value loop
/// (`<fn>.while_N`) -- same params, same recursive args, same guard -- so
/// it shares the value loop's measure + decreasing proof. The human
/// registers ONE entry (the value loop) and both `def`s are upgraded; an
/// explicit abort entry still wins if a loop ever needs a distinct proof.
fn aborts_companion_value_key(key: &str) -> Option<String> {
    key.contains(".aborts.while_")
        .then(|| key.replacen(".aborts.while_", ".while_", 1))
}

#[derive(Debug, Clone)]
pub struct LoopRenderContext {
    mode: LoopMode,
    registry: LoopTerminationRegistry,
}

impl LoopRenderContext {
    pub fn new(mode: LoopMode, registry: LoopTerminationRegistry) -> Self {
        Self { mode, registry }
    }

    pub fn mode(&self) -> LoopMode {
        self.mode
    }

    pub fn registry(&self) -> &LoopTerminationRegistry {
        &self.registry
    }
}

impl Default for LoopRenderContext {
    fn default() -> Self {
        Self::new(LoopMode::Proof, LoopTerminationRegistry::default())
    }
}

/// The ready total-termination entry for `func`, or `None` to keep
/// `partial_fixpoint`. Returns `Some` only in `Proof` mode and only when
/// the registry has a non-`sorry` entry keyed by this loop's stable name.
pub fn ready_entry(
    context: &LoopRenderContext,
    program: &Program,
    func: &Function,
) -> Option<TerminationEntry> {
    if context.mode() != LoopMode::Proof {
        return None;
    }
    let key = loop_key(program, func)?;
    let registry = context.registry();
    if let Some(entry) = registry.get(&key).filter(|entry| entry.is_ready()) {
        return Some(entry.clone());
    }
    let value_key = aborts_companion_value_key(&key)?;
    registry
        .get(&value_key)
        .filter(|entry| entry.is_ready())
        .cloned()
}

/// Warn (to stderr) about registry keys that no longer match any loop
/// helper in `program` -- a Move-source change likely renumbered or
/// removed a loop, orphaning the human's measure. Fail-loud rather than
/// silently dropping the entry. Called once per render.
pub fn report_orphans(program: &Program, registry: &LoopTerminationRegistry) {
    use std::collections::BTreeSet;
    let live: BTreeSet<String> = program
        .functions
        .values()
        .filter_map(|f| loop_key(program, f))
        .collect();
    for k in registry.keys() {
        if !live.contains(k) {
            eprintln!(
                "⚠ loop-termination registry: entry `{k}` matches no loop helper \
                 in this package (a Move-source change may have renumbered or removed \
                 the loop). The measure/proof is being ignored -- update or delete it."
            );
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn loop_fixture() -> (Program, Function) {
        let mut program = Program::default();
        program.modules.insert(
            0,
            crate::ir::Module {
                name: "m".to_string(),
                package_name: "Pkg".to_string(),
                address: String::new(),
                required_imports: Vec::new(),
                is_native: false,
            },
        );
        let function = Function {
            module: 0,
            name: "f.while_0".to_string(),
            signature: crate::ir::Signature {
                type_params: Vec::new(),
                params: Vec::new(),
                return_type: crate::ir::Type::Unit,
            },
            body: crate::ir::Block::just(crate::ir::Expr::Unit),
            kind: crate::ir::FunctionKind::Source,
            effects: crate::ir::Effects::PURE,
            explicit_pure: true,
        };
        (program, function)
    }

    #[test]
    fn parses_blocks_and_trims() {
        let src = "\
# a comment, ignored
@loop Pkg.modx.foo.while_0
@measure
2 ^ 32 - carry.val
@decreasing
simp only [foo]
omega
@end
";
        let reg = LoopTerminationRegistry::parse(src);
        let e = reg.get("Pkg.modx.foo.while_0").expect("entry present");
        assert_eq!(e.measure, "2 ^ 32 - carry.val");
        assert_eq!(e.decreasing, "simp only [foo]\nomega");
        assert!(e.is_ready());
    }

    #[test]
    fn sorry_placeholders_are_not_ready() {
        let src = "\
@loop Pkg.m.f.while_0
@measure
sorry
@decreasing
sorry
@end
@loop Pkg.m.g.while_0
@measure
n.val
@decreasing
sorry
@end
";
        let reg = LoopTerminationRegistry::parse(src);
        assert!(!reg.get("Pkg.m.f.while_0").unwrap().is_ready());
        // measure present but decreasing still `sorry` -> not ready.
        assert!(!reg.get("Pkg.m.g.while_0").unwrap().is_ready());
    }

    #[test]
    fn signature_lines_ignored_and_trailing_block_flushed() {
        let src = "\
@loop Pkg.m.f.while_0
@signature def f (carry : BoundedNat) : Nat
@measure
carry.val
@decreasing
decreasing_with omega
";
        let reg = LoopTerminationRegistry::parse(src);
        let e = reg
            .get("Pkg.m.f.while_0")
            .expect("trailing block flushed without @end");
        assert_eq!(e.measure, "carry.val");
        assert_eq!(e.decreasing, "decreasing_with omega");
        assert!(e.is_ready());
    }

    #[test]
    fn missing_file_yields_empty_registry() {
        let reg = LoopTerminationRegistry::load(Path::new("/nonexistent/loop_termination.txt"));
        assert_eq!(reg.keys().count(), 0);
    }

    #[test]
    fn abort_companion_inherits_value_loop_key() {
        assert_eq!(
            aborts_companion_value_key("Pkg.m.wrapping_add.aborts.while_0").as_deref(),
            Some("Pkg.m.wrapping_add.while_0"),
        );
        // A plain value loop is not an abort companion.
        assert_eq!(
            aborts_companion_value_key("Pkg.m.wrapping_add.while_0"),
            None
        );
        // Only the companion segment is stripped, not an unrelated `.aborts`.
        assert_eq!(aborts_companion_value_key("Pkg.m.foo.aborts"), None);
    }

    #[test]
    fn loop_contexts_can_be_interleaved_without_state_leaking() {
        let (program, function) = loop_fixture();
        let registry = LoopTerminationRegistry::parse(
            "@loop Pkg.m.f.while_0\n@measure\nn\n@decreasing\nomega\n@end\n",
        );
        let proof = LoopRenderContext::new(LoopMode::Proof, registry.clone());
        let test = LoopRenderContext::new(LoopMode::Test, registry.clone());
        let execution = LoopRenderContext::new(LoopMode::Execution, registry);
        let empty = LoopRenderContext::default();

        assert_eq!(
            ready_entry(&proof, &program, &function).unwrap().measure,
            "n"
        );
        assert!(ready_entry(&test, &program, &function).is_none());
        assert!(ready_entry(&execution, &program, &function).is_none());
        assert!(ready_entry(&empty, &program, &function).is_none());
        assert_eq!(
            ready_entry(&proof, &program, &function).unwrap().measure,
            "n"
        );
    }
}
