//! Human-readable formatting for invariant violations.
//!
//! `verify_at` returns `Vec<InvariantViolation>`. Printing that vec
//! via `Debug` works but groups badly when many invariants fire at
//! once. This module provides a structured pretty-print:
//!
//!   [invariant-id]
//!     function name (fid): detail
//!     function name (fid): detail
//!   [other-invariant-id]
//!     ...
//!
//! Massively cuts triage time when 40+ violations land on the same
//! report. See `plans/lean-pipeline/new-invariant-checks.md` Tier 5.

use std::collections::BTreeMap;
use std::fmt::Write;

use crate::ir::{CalleeRef, Program};

use super::traits::InvariantViolation;

/// Render a slice of violations as a grouped, multi-line string.
///
/// Groups by `invariant` id, then within each group lists each
/// violation as `<function_name> (fid): <detail>`. Looks up function
/// names from `program.functions` and `program.natives.decls`;
/// violations without a function id are listed under
/// `<program-level>`.
pub fn display_table(violations: &[InvariantViolation], program: &Program) -> String {
    if violations.is_empty() {
        return "<no violations>".to_string();
    }

    // Group by invariant id, preserving insertion order via BTreeMap
    // keyed by invariant id (stable since ids are static strings).
    let mut groups: BTreeMap<&'static str, Vec<&InvariantViolation>> = BTreeMap::new();
    for v in violations {
        groups.entry(v.invariant).or_default().push(v);
    }

    let mut out = String::new();
    for (id, vs) in &groups {
        let _ = writeln!(
            out,
            "[{}] ({} violation{})",
            id,
            vs.len(),
            if vs.len() == 1 { "" } else { "s" }
        );
        for v in vs {
            let name = match v.function {
                Some(fid) => function_name(program, fid),
                None => "<program-level>".to_string(),
            };
            let _ = match v.function {
                Some(fid) => writeln!(out, "  {} (fid {}): {}", name, fid, v.detail),
                None => writeln!(out, "  {}: {}", name, v.detail),
            };
        }
    }
    out
}

/// Look up a function's name (translated or native) by FunId, with a
/// fallback to a synthetic placeholder if the id doesn't resolve.
fn function_name(program: &Program, fid: crate::ir::FunId) -> String {
    match program.lookup_callee(fid) {
        Some(CalleeRef::Translated(function)) => function.name.clone(),
        Some(CalleeRef::Native(decl)) => format!("<native> {}", decl.name),
        None => format!("<unknown fid {}>", fid),
    }
}

/// Convenience: pretty-print a verify_at result. Useful in error
/// paths and tests.
pub fn format_result(result: &Result<(), Vec<InvariantViolation>>, program: &Program) -> String {
    match result {
        Ok(()) => "<ok>".to_string(),
        Err(vs) => display_table(vs, program),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::invariants::Stage;
    use crate::ir::{
        builder::var, Block, BlockTail, Function, FunctionKind, Module, Param, Signature, Type,
    };

    fn program_with_two_broken_functions() -> Program {
        // Two functions, both with unbound variable references --
        // catches baseline-well-formedness twice.
        let mut p = Program::default();
        p.modules.insert(
            0,
            Module {
                name: "m".to_string(),
                package_name: "test".to_string(),
                address: String::new(),
                required_imports: Vec::new(),
                is_native: false,
            },
        );
        for i in 0..2 {
            p.functions.insert(
                i,
                Function {
                    module: 0,
                    name: format!("broken_{i}"),
                    signature: Signature {
                        type_params: Vec::new(),
                        params: Vec::<Param>::new(),
                        return_type: Type::Unit,
                    },
                    body: Block {
                        stmts: Vec::new(),
                        tail: BlockTail::Value(var(&format!("missing_{i}"))),
                    },
                    kind: FunctionKind::Source,
                    effects: crate::ir::Effects::PURE,
                    explicit_pure: false,
                },
            );
        }
        p
    }

    #[test]
    fn display_table_empty_says_no_violations() {
        let p = Program::default();
        assert_eq!(display_table(&[], &p), "<no violations>");
    }

    #[test]
    fn display_table_groups_by_invariant_id() {
        let p = program_with_two_broken_functions();
        let result = crate::ir::invariants::verify_at(Stage::Render, &p);
        let output = format_result(&result, &p);
        // BaselineWellFormedness is an umbrella that wraps the legacy
        // `validate_program`, which returns the first violation only.
        // The grouping still applies, but the count is per-invariant
        // not per-function.
        assert!(output.contains("[baseline-well-formedness]"));
        assert!(output.contains("broken_0") || output.contains("broken_1"));
        assert!(output.contains("violation"));
    }

    #[test]
    fn display_table_resolves_function_names() {
        let p = program_with_two_broken_functions();
        let v = InvariantViolation::new("test-inv", Some(0), "test detail");
        let out = display_table(&[v], &p);
        assert!(
            out.contains("broken_0 (fid 0)"),
            "expected resolved function name, got: {}",
            out,
        );
    }

    #[test]
    fn display_table_program_level_uses_placeholder() {
        let p = Program::default();
        let v = InvariantViolation::new("test-inv", None, "program-level issue");
        let out = display_table(&[v], &p);
        assert!(out.contains("<program-level>"));
    }

    #[test]
    fn display_table_handles_unknown_fid() {
        let p = Program::default();
        let v = InvariantViolation::new("test-inv", Some(99), "ghost function");
        let out = display_table(&[v], &p);
        assert!(out.contains("<unknown fid 99>"));
    }
}
