use crate::ir::{Block, Const, Expr, Module, Struct, Type};
use crate::render::{
    module_render_location, read_test_declarations, write_test_declarations_manifest,
};

use super::fixtures::{add_function, empty_program, func, param, sig};

#[test]
fn package_qualification_resolves_cross_package_module_collisions() {
    let client = module_render_location("CetusDlmm", "versioned");
    let framework = module_render_location("Sui", "versioned");

    assert_eq!(client.file_stem, "Versioned");
    assert_eq!(client.import_path, "CetusDlmm.Versioned");
    assert_eq!(client.namespace, "CetusDlmm.Versioned");
    assert_eq!(framework.file_stem, "Versioned");
    assert_eq!(framework.import_path, "Sui.Versioned");
    assert_eq!(framework.namespace, "Versioned");
}

#[test]
fn declaration_manifest_uses_final_ir_signature() {
    let mut program = empty_program();
    program.modules.get_mut(&0).unwrap().address = "2".into();
    program.modules.insert(
        1,
        Module {
            name: "world".into(),
            package_name: "Prover".into(),
            address: String::new(),
            required_imports: Vec::new(),
            is_native: true,
        },
    );
    program.structs.insert(
        7,
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
    add_function(
        &mut program,
        9,
        func(
            "versioned",
            sig(Vec::new(), Type::Unit),
            Block::just(Expr::Const(Const::Unit)),
            0,
        ),
    );
    add_function(
        &mut program,
        0,
        func(
            "versioned.aborts",
            sig(
                vec![
                    param(
                        "world",
                        Type::Struct {
                            struct_id: 7,
                            type_args: Vec::new(),
                        },
                    ),
                    param("__ghost_9", Type::Bool),
                ],
                Type::Bool,
            ),
            Block::just(Expr::Const(Const::Bool(false))),
            0,
        ),
    );
    program.functions.get_mut(&0).unwrap().kind = crate::ir::FunctionKind::Spec {
        kind: crate::ir::SpecKind::Aborts,
        target: 9,
    };
    program.ghost_vars.insert(9, vec![(Type::Unit, Type::Bool)]);

    let output = tempfile::tempdir().unwrap();
    write_test_declarations_manifest(&program, output.path()).unwrap();
    let manifest = read_test_declarations(output.path()).unwrap();

    assert_eq!(manifest.schema_version, 1);
    assert_eq!(manifest.declarations.len(), 1);
    let declaration = &manifest.declarations[0];
    assert_eq!(declaration.addressed_module, "0x2::m");
    assert_eq!(declaration.function, "versioned");
    assert_eq!(declaration.import_path, "p.M");
    assert_eq!(declaration.lean_declaration, "p.M.versioned.aborts");
    assert!(declaration.needs_world);
    assert_eq!(declaration.ghost_param_count, 1);
}

#[test]
fn declaration_manifest_does_not_guess_ghosts_from_source_names() {
    let mut program = empty_program();
    program.modules.get_mut(&0).unwrap().address = "2".into();
    add_function(
        &mut program,
        9,
        func(
            "test",
            sig(Vec::new(), Type::Unit),
            Block::just(Expr::Const(Const::Unit)),
            0,
        ),
    );
    add_function(
        &mut program,
        0,
        func(
            "test.aborts",
            sig(
                vec![param("__ghost_user_parameter", Type::Bool)],
                Type::Bool,
            ),
            Block::just(Expr::Const(Const::Bool(false))),
            0,
        ),
    );
    program.functions.get_mut(&0).unwrap().kind = crate::ir::FunctionKind::Spec {
        kind: crate::ir::SpecKind::Aborts,
        target: 9,
    };

    let output = tempfile::tempdir().unwrap();
    write_test_declarations_manifest(&program, output.path()).unwrap();
    let manifest = read_test_declarations(output.path()).unwrap();

    assert_eq!(manifest.declarations[0].ghost_param_count, 0);
}

#[test]
fn declaration_manifest_rejects_duplicate_addressed_identity() {
    let output = tempfile::tempdir().unwrap();
    std::fs::write(
        output
            .path()
            .join(crate::render::TEST_DECLARATIONS_MANIFEST),
        r#"schema_version = 1

[[declaration]]
addressed_module = "0x2::m"
function = "test"
import_path = "one.M"
lean_declaration = "one.M.test.aborts"
needs_world = false
ghost_param_count = 0

[[declaration]]
addressed_module = "0x2::m"
function = "test"
import_path = "two.M"
lean_declaration = "two.M.test.aborts"
needs_world = false
ghost_param_count = 0
"#,
    )
    .unwrap();
    assert!(read_test_declarations(output.path()).is_err());
}

#[test]
fn declaration_manifest_rejects_address_aliasing_one_rendered_module() {
    let output = tempfile::tempdir().unwrap();
    std::fs::write(
        output
            .path()
            .join(crate::render::TEST_DECLARATIONS_MANIFEST),
        r#"schema_version = 1

[[declaration]]
addressed_module = "0x2::m"
function = "first"
import_path = "p.M"
lean_declaration = "p.M.first.aborts"
needs_world = false
ghost_param_count = 0

[[declaration]]
addressed_module = "0x3::m"
function = "second"
import_path = "p.M"
lean_declaration = "p.M.second.aborts"
needs_world = false
ghost_param_count = 0
"#,
    )
    .unwrap();
    let error = read_test_declarations(output.path()).unwrap_err();
    assert!(matches!(
        error,
        crate::render::RenderError::Io { what }
            if what.contains("aliases addressed modules `0x2::m` and `0x3::m`")
    ));
}

#[test]
fn declaration_manifest_writer_rejects_address_aliasing() {
    let mut program = empty_program();
    program.modules.get_mut(&0).unwrap().address = "2".into();
    program.modules.insert(
        1,
        Module {
            name: "m".into(),
            package_name: "p".into(),
            address: "3".into(),
            required_imports: Vec::new(),
            is_native: false,
        },
    );
    add_function(
        &mut program,
        10,
        func(
            "first",
            sig(Vec::new(), Type::Unit),
            Block::just(Expr::Const(Const::Unit)),
            0,
        ),
    );
    add_function(
        &mut program,
        11,
        func(
            "second",
            sig(Vec::new(), Type::Unit),
            Block::just(Expr::Const(Const::Unit)),
            1,
        ),
    );
    add_function(
        &mut program,
        0,
        func(
            "first.aborts",
            sig(Vec::new(), Type::Bool),
            Block::just(Expr::Const(Const::Bool(false))),
            0,
        ),
    );
    program.functions.get_mut(&0).unwrap().kind = crate::ir::FunctionKind::Spec {
        kind: crate::ir::SpecKind::Aborts,
        target: 10,
    };
    add_function(
        &mut program,
        1,
        func(
            "second.aborts",
            sig(Vec::new(), Type::Bool),
            Block::just(Expr::Const(Const::Bool(false))),
            1,
        ),
    );
    program.functions.get_mut(&1).unwrap().kind = crate::ir::FunctionKind::Spec {
        kind: crate::ir::SpecKind::Aborts,
        target: 11,
    };

    let output = tempfile::tempdir().unwrap();
    assert!(write_test_declarations_manifest(&program, output.path()).is_err());
}

#[test]
fn declaration_manifest_uses_spec_identity_not_name_suffix() {
    let mut program = empty_program();
    program.modules.get_mut(&0).unwrap().address = "2".into();
    add_function(
        &mut program,
        0,
        func(
            "not_a_companion.aborts",
            sig(Vec::new(), Type::Bool),
            Block::just(Expr::Const(Const::Bool(false))),
            0,
        ),
    );

    let output = tempfile::tempdir().unwrap();
    write_test_declarations_manifest(&program, output.path()).unwrap();
    assert!(read_test_declarations(output.path())
        .unwrap()
        .declarations
        .is_empty());
}

#[test]
fn declaration_manifest_rejects_mismatched_spec_target() {
    let mut program = empty_program();
    program.modules.get_mut(&0).unwrap().address = "2".into();
    add_function(
        &mut program,
        9,
        func(
            "target",
            sig(Vec::new(), Type::Unit),
            Block::just(Expr::Const(Const::Unit)),
            0,
        ),
    );
    add_function(
        &mut program,
        0,
        func(
            "other.aborts",
            sig(Vec::new(), Type::Bool),
            Block::just(Expr::Const(Const::Bool(false))),
            0,
        ),
    );
    program.functions.get_mut(&0).unwrap().kind = crate::ir::FunctionKind::Spec {
        kind: crate::ir::SpecKind::Aborts,
        target: 9,
    };

    let output = tempfile::tempdir().unwrap();
    assert!(write_test_declarations_manifest(&program, output.path()).is_err());
}

#[test]
fn declaration_manifest_rejects_unknown_fields() {
    let output = tempfile::tempdir().unwrap();
    std::fs::write(
        output
            .path()
            .join(crate::render::TEST_DECLARATIONS_MANIFEST),
        "schema_version = 1\nunknown = true\ndeclaration = []\n",
    )
    .unwrap();
    assert!(read_test_declarations(output.path()).is_err());
}
