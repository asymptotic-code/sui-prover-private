//! Per-project `Generated/StructIdx.lean` -- the NAME-keyed table of
//! Move datatype tags.
//!
//! `StructId` is a positional integer: `Program::next_struct_id` hands
//! it out while walking modules in module-name order, so a datatype's
//! numeric identity is its position in that walk. Renaming ANY module
//! permutes the table, and every generated `borrowField <sid> <off>` /
//! `Edge.structField <sid> <off>` moves with it -- silently, in modules
//! that were not touched.
//!
//! This module breaks that coupling at the emission boundary. Every
//! rendered reference to a datatype's identity is spelled as the
//! datatype's NAME (`StructIdx.SuiSystem__validator__Validator`), and
//! the one place that still knows the ordinal is the generated table
//! below. Renaming a module then rewrites at most the table entries of
//! the datatypes that module itself declares; every other generated
//! byte, every hand-written proof site, and every obligation
//! fingerprint is unchanged.
//!
//! The entries are `abbrev ... : Nat`, i.e. `@[reducible]`, so a tag
//! reduces to its `Nat` literal in one delta step: `decide`,
//! `native_decide`, `rfl` and `simp` matching all behave exactly as
//! they did against the bare numeral. The prelude's `Edge` /
//! `Mutation` types are untouched, which is what keeps this change
//! from being a fleet-wide breaking change to every corpus's
//! `Mutation Key T` signatures.
//!
//! Coverage is `Program::structs`, which holds Move `struct` AND
//! `enum` datatypes (an enum is a `Struct` with `variants: Some(..)`).
//! Both take a global index, so both must be tagged.

use std::collections::HashMap;
use std::fs;
use std::io;
use std::path::Path;

use crate::ir::{Program, StructId};

use super::dyn_type_universe::struct_mangle_prefix;

/// The stable, name-derived Lean identifier for a Move datatype.
///
/// `<module>__<Name>` for lemma-package datatypes,
/// `<Package>__<module>__<Name>` for user-package ones -- the same
/// mangling `TyCode` / `ObjType` constructors already use, so the two
/// tables name the same datatype the same way. No ordinal appears in
/// the result: an unknown `StructId` is a renderer bug, not a case to
/// fall back on.
pub fn struct_tag_ident(struct_id: StructId, program: &Program) -> String {
    assert!(
        program.structs.contains_key(&struct_id),
        "struct tag requested for unknown StructId {struct_id}"
    );
    let ident = struct_mangle_prefix(struct_id, program);
    assert!(
        !ident.is_empty() && !ident.starts_with(|c: char| c.is_ascii_digit()),
        "struct tag for StructId {struct_id} is not a Lean identifier: {ident}"
    );
    ident
}

/// The qualified reference emitted into generated Lean in place of a
/// bare struct index.
pub fn struct_tag_ref(struct_id: StructId, program: &Program) -> String {
    format!("StructIdx.{}", struct_tag_ident(struct_id, program))
}

/// The identifier-safe datatype name used to build ghost binder names
/// (`__ghost_<tag>`) and the opaque ghost-output declarations
/// (`<fn>__ghost_out_<tag>`). Same derivation as [`struct_tag_ident`];
/// separate entry point so the ghost stage does not have to know it is
/// spelling a Lean namespace member.
pub fn struct_tag_name(struct_id: StructId, program: &Program) -> String {
    struct_tag_ident(struct_id, program)
}

pub fn write_struct_idx_file(program: &Program, output_dir: &Path) -> io::Result<()> {
    let gen_dir = output_dir.join("Generated");
    fs::create_dir_all(&gen_dir)?;
    let path = gen_dir.join("StructIdx.lean");

    let mut seen: HashMap<String, StructId> = HashMap::new();
    let mut out = String::new();
    out.push_str("-- Generated per project by the lean-pipeline renderer.\n");
    out.push_str("-- Name-keyed table of Move datatype (struct AND enum) tags.\n");
    out.push_str("--\n");
    out.push_str("-- The renderer emits `StructIdx.<Package>__<module>__<Name>`\n");
    out.push_str("-- wherever a datatype's identity is needed (borrow paths,\n");
    out.push_str("-- ghost binders). This file is the ONLY place the positional\n");
    out.push_str("-- index survives, so renaming a module rewrites entries here\n");
    out.push_str("-- and nothing else. Entries are `abbrev`, i.e. reducible, so a\n");
    out.push_str("-- tag reduces to its Nat literal for decide/rfl/simp.\n\n");
    out.push_str("namespace StructIdx\n\n");
    let mut collisions: Vec<String> = Vec::new();
    for (sid, s) in program.structs.iter() {
        let ident = struct_tag_ident(*sid, program);
        if let Some(prev) = seen.insert(ident.clone(), *sid) {
            collisions.push(format!(
                "  `{ident}`: StructId {prev} ({}) vs StructId {sid} ({})",
                program
                    .structs
                    .get(&prev)
                    .map(|p| p.qualified_name.as_str())
                    .expect("collision partner exists"),
                s.qualified_name
            ));
        }
        let kind = if s.variants.is_some() { "enum" } else { "struct" };
        out.push_str(&format!("-- {} {}\n", kind, s.qualified_name));
        out.push_str(&format!("abbrev {} : Nat := {}\n", ident, sid));
    }
    out.push_str("\nend StructIdx\n");
    assert!(
        collisions.is_empty(),
        "{} datatype tag collision(s):\n{}",
        collisions.len(),
        collisions.join("\n")
    );
    fs::write(&path, &out)?;
    Ok(())
}
