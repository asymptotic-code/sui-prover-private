//! Stage 4 world.rs tests: World struct registration is idempotent
//! and allocates a fresh StructId.

use crate::stage_04_effects::world::{ensure_world_struct, WORLD_QUALIFIED_NAME};

use super::fixtures::*;

#[test]
fn ensure_world_struct_allocates_fresh_id() {
    let mut program = program_with(Vec::new());
    let id1 = ensure_world_struct(&mut program);
    assert!(program.structs.contains_key(&id1));
    assert_eq!(program.structs[&id1].qualified_name, WORLD_QUALIFIED_NAME);
    assert_eq!(program.structs[&id1].name, "World");
}

#[test]
fn ensure_world_struct_is_idempotent() {
    let mut program = program_with(Vec::new());
    let id1 = ensure_world_struct(&mut program);
    let id2 = ensure_world_struct(&mut program);
    assert_eq!(id1, id2);
    assert_eq!(program.structs.len(), 1);
}

#[test]
fn world_struct_has_prelude_fields() {
    let mut program = program_with(Vec::new());
    let id = ensure_world_struct(&mut program);
    let s = &program.structs[&id];
    let field_names: Vec<&str> = s.fields.iter().map(|f| f.name.as_str()).collect();
    assert_eq!(
        field_names,
        vec![
            "events",
            "owned",
            "shared",
            "frozen",
            "deleted",
            "received",
            "gas_used",
            "bag_entries",
            "df_entries",
            "df_bag_entries",
            "tx_user_events",
            "tx_created",
            "allocated_ids",
            "accumulator"
        ]
    );
}

#[test]
fn ensure_world_module_registered() {
    let mut program = program_with(Vec::new());
    ensure_world_struct(&mut program);
    let prover_modules: Vec<_> = program
        .modules
        .values()
        .filter(|m| m.package_name == "Prover" && m.name == "world")
        .collect();
    assert_eq!(prover_modules.len(), 1);
    assert!(prover_modules[0].is_native);
}
