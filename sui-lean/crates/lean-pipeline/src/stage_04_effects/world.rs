//! World struct registration and World-threading helpers.
//!
//! Stage 4 emits one synthetic `World` struct per `Program`, lazily
//! allocated at the start of the pass. The renderer maps any
//! `Type::Struct { struct_id: world_id, .. }` reference to the
//! hand-written `Prover.World.World` Lean type.
//!
//! See `plans/lean-pipeline/stage-04-effects.md` for the design.

use crate::ir::{Field, ModId, Module, Program, Struct, StructId, Type};

/// Canonical qualified name of the synthetic World struct. The
/// renderer maps this exact string to `Prover.World.World`.
pub const WORLD_QUALIFIED_NAME: &str = "Prover::World::World";

/// Canonical package name of the synthetic prelude module World
/// lives under.
pub const WORLD_PACKAGE_NAME: &str = "Prover";

/// Canonical module name.
pub const WORLD_MODULE_NAME: &str = "world";

/// Get-or-register the synthetic World struct. Idempotent: a second
/// call on a `Program` that already has the struct returns the same
/// `StructId`.
///
/// Allocates a fresh `StructId` (one greater than the maximum key in
/// `program.structs`) and inserts a `Struct` with the World field
/// names. If no Module for the prelude exists, allocates one too.
pub fn ensure_world_struct(program: &mut Program) -> StructId {
    if let Some(id) = find_existing_world(program) {
        return id;
    }

    let module_id = ensure_world_module(program);
    let world_id = program.next_struct_id();

    // Field types reference helper inductives that the renderer
    // emits per-package (`AnyEvent`, `AnyObject`) plus a few prelude
    // types. At the IR level we use opaque `Type::Unit` placeholders
    // for the heterogeneous collections -- the renderer doesn't read
    // these field types when emitting the World; it uses the
    // hand-written prelude. We still register the field names so
    // downstream tooling (debug-print, sanity checks) can introspect.
    program.structs.insert(
        world_id,
        Struct {
            module_id,
            name: "World".to_string(),
            qualified_name: WORLD_QUALIFIED_NAME.to_string(),
            type_params: Vec::new(),
            fields: vec![
                Field {
                    name: "events".into(),
                    field_type: Type::Unit,
                },
                Field {
                    name: "owned".into(),
                    field_type: Type::Unit,
                },
                Field {
                    name: "shared".into(),
                    field_type: Type::Unit,
                },
                Field {
                    name: "frozen".into(),
                    field_type: Type::Unit,
                },
                Field {
                    name: "deleted".into(),
                    field_type: Type::Unit,
                },
                Field {
                    name: "received".into(),
                    field_type: Type::Unit,
                },
                Field {
                    name: "gas_used".into(),
                    field_type: Type::UInt(64),
                },
                Field {
                    name: "bag_entries".into(),
                    field_type: Type::Unit,
                },
                Field {
                    name: "df_entries".into(),
                    field_type: Type::Unit,
                },
                Field {
                    name: "df_bag_entries".into(),
                    field_type: Type::Unit,
                },
                Field {
                    name: "tx_user_events".into(),
                    field_type: Type::UInt(64),
                },
                Field {
                    name: "tx_created".into(),
                    field_type: Type::Unit,
                },
                Field {
                    name: "allocated_ids".into(),
                    field_type: Type::Unit,
                },
                Field {
                    name: "accumulator".into(),
                    field_type: Type::Unit,
                },
            ],
            variants: None,
            // Synthetic World struct: the body lives in
            // `Prelude/World.lean` (`Prover.World.World` indexed by
            // `__WorldEvent __WorldObject`). The IR Struct entry
            // exists only so cross-module signatures can reference
            // `Type::Struct { struct_id: world_id, .. }`; the
            // renderer skips the structure declaration (sees
            // `is_native = true`) and lets the prelude provide it.
            is_native: true,
        },
    );
    world_id
}

/// The `Type` for `world` parameters and the last return-tuple slot.
/// Always `Type::Struct { struct_id, type_args: [] }`.
pub fn world_type(world_id: StructId) -> Type {
    Type::Struct {
        struct_id: world_id,
        type_args: Vec::new(),
    }
}

fn find_existing_world(program: &Program) -> Option<StructId> {
    program.struct_id_by_qualified_name(WORLD_QUALIFIED_NAME)
}

fn ensure_world_module(program: &mut Program) -> ModId {
    if let Some(id) = program.module_id_by_name(WORLD_PACKAGE_NAME, WORLD_MODULE_NAME) {
        return id;
    }
    let id = program.next_module_id();
    program.modules.insert(
        id,
        Module {
            name: WORLD_MODULE_NAME.to_string(),
            package_name: WORLD_PACKAGE_NAME.to_string(),
            address: String::new(),
            required_imports: Vec::new(),
            is_native: true,
        },
    );
    id
}
