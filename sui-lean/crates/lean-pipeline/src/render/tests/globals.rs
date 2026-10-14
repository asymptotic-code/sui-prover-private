use crate::global_threading::thread_globals;
use crate::ir::{
    validate::{validate_program, ValidationErrorKind},
    BorrowEdge, BorrowNode, Expr, Field, Global, GlobalDefinition, StaticValue, Struct, Type,
};
use crate::render::{render_program, RenderError};
use ethnum::U256;
use num::BigUint;

use super::fixtures::*;

fn mutable_u64() -> Type {
    Type::MutableRef {
        inner: Box::new(Type::UInt(64)),
        root: Box::new(Type::UInt(64)),
    }
}

fn insert_global(program: &mut crate::ir::Program, id: usize, mutable: bool, name: &str) {
    program.globals.insert(
        id,
        Global {
            module_id: 0,
            name: name.to_string(),
            ty: Type::UInt(64),
            mutable,
            definition: GlobalDefinition::BoundarySupplied,
        },
    );
}

#[test]
fn empty_global_table_preserves_the_legacy_render() {
    let mut program = empty_program();
    let baseline = render_program(&program).expect("render empty globals");

    insert_global(&mut program, 7, true, "temporary");
    program.globals.clear();
    let after = render_program(&program).expect("render cleared globals");

    assert_eq!(after, baseline);
    assert!(!after.contains("namespace C2LeanGlobals"));
    assert!(!after.contains("ofGlobal"));
}

#[test]
fn global_boundary_helpers_are_deterministic_and_respect_mutability() {
    let mut program = empty_program();
    // Insert in reverse ID order and use source names that would be unsafe as
    // Lean identifiers. Rendering is keyed only by the stable GlobalId.
    insert_global(&mut program, 7, true, "mutable.@/counter");
    insert_global(&mut program, 2, false, "readonly.@/limit");

    let output = render_program(&program).expect("render globals");
    let readonly = output.find("def g2Id").expect("readonly declaration");
    let mutable = output.find("def g7Id").expect("mutable declaration");

    assert!(readonly < mutable, "globals must render in GlobalId order");
    assert!(output.contains("def g2Mutable : Bool := false"));
    assert!(output.contains("def g2Ref (value : BoundedNat (2^64)) : BoundedNat (2^64) := value"));
    assert!(!output.contains("def g2Root"));
    assert!(output.contains("def g7Mutable : Bool := true"));
    assert!(output.contains(
        "def g7Root {Key : Type} (value : BoundedNat (2^64)) : Prover.Mutation.Mutation Key (BoundedNat (2^64)) :="
    ));
    assert!(
        output.contains("@Prover.Mutation.Mutation.ofGlobal Key (BoundedNat (2^64)) g7Id value")
    );
    assert!(!output.contains("mutable.@/counter"));
    assert!(!output.contains("readonly.@/limit"));
}

#[test]
fn readonly_defined_global_renders_its_closed_initial_value() {
    let mut program = empty_program();
    insert_global(&mut program, 2, false, "limit");
    program.globals.get_mut(&2).unwrap().definition = GlobalDefinition::Defined {
        startup_value: StaticValue::UInt {
            bits: 64,
            value: U256::from(17u8),
        },
    };

    let output = render_program(&program).expect("render readonly initializer");

    assert!(output.contains("def g2Initial : BoundedNat (2^64) := (17 : BoundedNat (2^64))"));
    assert!(output.contains("def g2InitialRef : BoundedNat (2^64) := g2Ref g2Initial"));
    assert!(!output.contains("g2InitialRoot"));
}

#[test]
fn mutable_defined_global_exposes_an_explicit_initial_root_only() {
    let mut program = empty_program();
    insert_global(&mut program, 7, true, "counter");
    program.globals.get_mut(&7).unwrap().definition = GlobalDefinition::Defined {
        startup_value: StaticValue::UInt {
            bits: 64,
            value: U256::from(3u8),
        },
    };

    let output = render_program(&program).expect("render mutable initializer");

    assert!(output.contains("def g7Initial : BoundedNat (2^64) := (3 : BoundedNat (2^64))"));
    assert!(output.contains(
        "def g7InitialRoot {Key : Type} : Prover.Mutation.Mutation Key (BoundedNat (2^64)) :=\n  g7Root g7Initial"
    ));
    assert_eq!(output.matches("def g7InitialRoot").count(), 1);
    assert!(!output.contains("g7InitialRef"));
}

#[test]
fn repeat_initializer_renders_compactly_and_preserves_length() {
    let mut program = empty_program();
    insert_global(&mut program, 4, true, "cache");
    let global = program.globals.get_mut(&4).unwrap();
    global.ty = Type::Vector(Box::new(Type::UInt(32)));
    global.definition = GlobalDefinition::Defined {
        startup_value: StaticValue::Repeat {
            value: Box::new(StaticValue::UInt {
                bits: 32,
                value: U256::ZERO,
            }),
            count: 4096,
        },
    };

    let output = render_program(&program).expect("render repeated initializer");

    assert!(output.contains(
        "def g4Initial : (List (BoundedNat (2^32))) := (List.replicate 4096 (0 : BoundedNat (2^32)))"
    ));
    assert!(!output.contains("g4Initial : (List (BoundedNat (2^32))) := default"));
}

#[test]
fn scalar_initializers_must_fit_their_declared_width_even_when_nested() {
    let mut program = empty_program();
    insert_global(&mut program, 6, false, "narrow");
    let global = program.globals.get_mut(&6).unwrap();
    global.ty = Type::UInt(8);
    global.definition = GlobalDefinition::Defined {
        startup_value: StaticValue::UInt {
            bits: 8,
            value: U256::from(256_u16),
        },
    };
    assert!(matches!(
        validate_program(&program).unwrap_err().kind,
        ValidationErrorKind::GlobalInitializerScalarOutOfRange { global: 6, bits: 8 }
    ));

    let global = program.globals.get_mut(&6).unwrap();
    global.ty = Type::Vector(Box::new(Type::UInt(8)));
    global.definition = GlobalDefinition::Defined {
        startup_value: StaticValue::Vector(vec![StaticValue::UInt {
            bits: 8,
            value: U256::from(256_u16),
        }]),
    };
    assert!(matches!(
        validate_program(&program).unwrap_err().kind,
        ValidationErrorKind::GlobalInitializerScalarOutOfRange { global: 6, bits: 8 }
    ));

    let address_bound = BigUint::from(1_u8) << 256_usize;
    let global = program.globals.get_mut(&6).unwrap();
    global.ty = Type::Address;
    global.definition = GlobalDefinition::Defined {
        startup_value: StaticValue::Address(address_bound.clone()),
    };
    assert!(matches!(
        validate_program(&program).unwrap_err().kind,
        ValidationErrorKind::GlobalInitializerScalarOutOfRange {
            global: 6,
            bits: 256,
        }
    ));

    program.globals.get_mut(&6).unwrap().definition = GlobalDefinition::Defined {
        startup_value: StaticValue::Address(address_bound - BigUint::from(1_u8)),
    };
    validate_program(&program).expect("the largest 256-bit address must remain exact");

    let global = program.globals.get_mut(&6).unwrap();
    global.ty = Type::UInt(256);
    global.definition = GlobalDefinition::Defined {
        startup_value: StaticValue::UInt {
            bits: 256,
            value: U256::MAX,
        },
    };
    validate_program(&program).expect("the largest UInt256 initializer must remain exact");
}

#[test]
fn nested_initializer_shape_mismatch_is_rejected() {
    let mut program = empty_program();
    program.structs.insert(
        9,
        Struct {
            module_id: 0,
            name: "PairBox".into(),
            qualified_name: "m::PairBox".into(),
            type_params: vec![],
            fields: vec![Field {
                name: "pair".into(),
                field_type: Type::Tuple(vec![Type::UInt(8), Type::Bool]),
            }],
            variants: None,
            is_native: false,
        },
    );
    insert_global(&mut program, 5, false, "bad_pair");
    let global = program.globals.get_mut(&5).unwrap();
    global.ty = Type::Struct {
        struct_id: 9,
        type_args: vec![],
    };
    global.definition = GlobalDefinition::Defined {
        startup_value: StaticValue::Struct {
            struct_id: 9,
            variant: None,
            fields: vec![StaticValue::Tuple(vec![StaticValue::UInt {
                bits: 8,
                value: U256::ZERO,
            }])],
        },
    };

    assert!(matches!(
        validate_program(&program).unwrap_err().kind,
        ValidationErrorKind::GlobalInitializerArityMismatch {
            global: 5,
            aggregate: "Tuple",
            expected: 2,
            actual: 1,
        }
    ));
}

#[test]
fn initializer_struct_ids_must_resolve_even_when_the_expected_type_does() {
    let mut program = empty_program();
    program.structs.insert(
        9,
        Struct {
            module_id: 0,
            name: "Known".into(),
            qualified_name: "m::Known".into(),
            type_params: vec![],
            fields: vec![],
            variants: None,
            is_native: false,
        },
    );
    insert_global(&mut program, 5, false, "unknown_value_type");
    let global = program.globals.get_mut(&5).unwrap();
    global.ty = Type::Struct {
        struct_id: 9,
        type_args: vec![],
    };
    global.definition = GlobalDefinition::Defined {
        startup_value: StaticValue::Struct {
            struct_id: 999,
            variant: None,
            fields: vec![],
        },
    };

    assert_eq!(
        validate_program(&program).unwrap_err().kind,
        ValidationErrorKind::UnknownStructId(999)
    );
}

#[test]
fn threaded_mutable_global_renders_as_an_ordinary_mutation_parameter() {
    let mut program = empty_program();
    insert_global(&mut program, 7, true, "counter");
    program.external_global_borrows_certified = true;
    add_function(
        &mut program,
        0,
        func(
            "borrow_counter",
            sig(vec![], mutable_u64()),
            body(vec![], Expr::BorrowGlobal(7)),
            0,
        ),
    );

    thread_globals(&mut program).expect("thread globals");
    let output = render_program(&program).expect("render threaded globals");

    assert_eq!(program.function_globals[&0][0].global, 7);
    assert!(output.contains(
        "(__c2lean_global_7 : (Mutation (BoundedNat (2^64)))) : (Mutation (BoundedNat (2^64)))"
    ));
    assert!(output.contains("__c2lean_global_7"));
    assert!(!output.contains("BorrowGlobal"));
    assert!(!output.contains("GlobalRoot"));
}

#[test]
fn threaded_global_root_writeback_updates_the_hidden_mutation() {
    let mut program = empty_program();
    insert_global(&mut program, 7, true, "counter");
    program.external_global_borrows_certified = true;
    add_function(
        &mut program,
        0,
        func(
            "write_counter",
            sig(vec![param("child", mutable_u64())], mutable_u64()),
            body(
                vec![],
                Expr::WriteBack {
                    node: BorrowNode::GlobalRoot(7),
                    edge: BorrowEdge::Direct,
                    child: "child".into(),
                    world: None,
                },
            ),
            0,
        ),
    );

    thread_globals(&mut program).expect("thread globals");
    let output = render_program(&program).expect("render threaded writeback");

    assert!(output.contains("@Prover.Mutation.Mutation.set"));
    assert!(output.contains("__c2lean_global_7"));
    assert!(!output.contains("writeBackSpecGlobal"));
    assert!(!output.contains("render fallback"));
}

#[test]
fn invalid_recursive_global_types_fail_before_type_rendering() {
    let mut program = empty_program();
    insert_global(&mut program, 7, false, "bad");
    program.globals.get_mut(&7).unwrap().ty = Type::Vector(Box::new(Type::Struct {
        struct_id: 999,
        type_args: vec![],
    }));

    assert_eq!(
        render_program(&program),
        Err(RenderError::UnknownStructId { id: 999 })
    );

    program.structs.insert(
        999,
        Struct {
            module_id: 0,
            name: "Box".into(),
            qualified_name: "m::Box".into(),
            type_params: vec!["T".into()],
            fields: vec![],
            variants: None,
            is_native: false,
        },
    );
    assert_eq!(
        render_program(&program),
        Err(RenderError::InvalidGlobalStructTypeArity {
            global: 7,
            struct_id: 999,
            expected: 1,
            actual: 0,
        })
    );

    program.globals.get_mut(&7).unwrap().ty = Type::Tuple(vec![Type::Prop]);
    assert_eq!(
        render_program(&program),
        Err(RenderError::InvalidGlobalStorageType {
            global: 7,
            kind: "Prop",
        })
    );

    program.globals.get_mut(&7).unwrap().ty = Type::Struct {
        struct_id: 999,
        type_args: vec![Type::UInt(8)],
    };
    program.structs.get_mut(&999).unwrap().fields.push(Field {
        name: "nested_pointer".into(),
        field_type: Type::Reference(Box::new(Type::TypeParam(0))),
    });
    assert_eq!(
        render_program(&program),
        Err(RenderError::InvalidGlobalStorageType {
            global: 7,
            kind: "Reference",
        })
    );
}

#[test]
fn residual_borrow_global_is_a_program_level_error() {
    let mut program = empty_program();
    insert_global(&mut program, 7, true, "counter");
    add_function(
        &mut program,
        0,
        func(
            "unthreaded_read",
            sig(vec![], mutable_u64()),
            body(vec![], Expr::BorrowGlobal(7)),
            0,
        ),
    );

    assert_eq!(
        render_program(&program),
        Err(RenderError::UnthreadedGlobal {
            operation: "BorrowGlobal",
            id: 7,
        })
    );
}

#[test]
fn residual_global_root_writeback_is_a_program_level_error() {
    let mut program = empty_program();
    insert_global(&mut program, 7, true, "counter");
    add_function(
        &mut program,
        0,
        func(
            "unthreaded_write",
            sig(vec![param("child", mutable_u64())], Type::Unit),
            body(
                vec![],
                Expr::WriteBack {
                    node: BorrowNode::GlobalRoot(7),
                    edge: BorrowEdge::Direct,
                    child: "child".into(),
                    world: None,
                },
            ),
            0,
        ),
    );

    assert_eq!(
        render_program(&program),
        Err(RenderError::UnthreadedGlobal {
            operation: "GlobalRoot writeback",
            id: 7,
        })
    );
}
