use std::collections::BTreeMap;

use crate::ir::analysis::type_of::type_of;
use crate::ir::{
    BitOp, Block, BlockTail, BorrowEdge, BorrowNode, Const, Expr, Field, Struct, Type, VarId,
    Variant,
};
use crate::render::expr::{effective_types_equal, rendered_block_value_type, rendered_type_of};

use super::fixtures::{add_native, add_struct, body, empty_program, lit_u64, native, sig};

fn mutable_u64() -> Type {
    Type::MutableRef {
        inner: Box::new(Type::UInt(64)),
        root: Box::new(Type::UInt(64)),
    }
}

#[test]
fn native_calls_expose_distinct_ir_and_rendered_types() {
    let mut program = empty_program();
    add_native(
        &mut program,
        1,
        native(
            "ordinary_native",
            sig(vec![], mutable_u64()),
            0,
            crate::ir::Effects::PURE,
            true,
        ),
    );
    add_native(
        &mut program,
        2,
        native(
            "Mutation.uninit",
            sig(vec![], mutable_u64()),
            0,
            crate::ir::Effects::PURE,
            true,
        ),
    );
    let scope = BTreeMap::new();

    let ordinary = Expr::Call {
        fun: 1,
        type_args: vec![],
        args: vec![],
    };
    assert_eq!(type_of(&ordinary, &scope, &program).unwrap(), mutable_u64());
    assert_eq!(
        rendered_type_of(&ordinary, &program, &scope),
        Some(Type::UInt(64))
    );

    let uninit = Expr::Call {
        fun: 2,
        type_args: vec![],
        args: vec![],
    };
    assert_eq!(
        rendered_type_of(&uninit, &program, &scope),
        Some(mutable_u64())
    );
}

#[test]
fn generic_field_and_unpack_types_use_the_concrete_base_arguments() {
    let mut program = empty_program();
    add_struct(
        &mut program,
        1,
        Struct {
            module_id: 0,
            name: "Box".into(),
            qualified_name: "p::m::Box".into(),
            type_params: vec!["T".into()],
            fields: vec![Field {
                name: "value".into(),
                field_type: Type::TypeParam(0),
            }],
            variants: None,
            is_native: false,
        },
    );
    add_struct(
        &mut program,
        2,
        Struct {
            module_id: 0,
            name: "Carrier".into(),
            qualified_name: "p::m::Carrier".into(),
            type_params: vec!["T".into()],
            fields: Vec::new(),
            variants: Some(vec![Variant {
                name: "carry".into(),
                tag: 0,
                fields: vec![Field {
                    name: "payload".into(),
                    field_type: Type::TypeParam(0),
                }],
            }]),
            is_native: false,
        },
    );
    let scope = BTreeMap::from([
        (
            VarId::from("boxed"),
            Type::Struct {
                struct_id: 1,
                type_args: vec![Type::UInt(64)],
            },
        ),
        (
            VarId::from("carrier"),
            Type::Struct {
                struct_id: 2,
                type_args: vec![Type::Bool],
            },
        ),
    ]);

    let field = Expr::Field {
        struct_id: 1,
        field_index: 0,
        base: Box::new(Expr::Var(VarId::from("boxed"))),
    };
    assert_eq!(
        rendered_type_of(&field, &program, &scope),
        Some(Type::UInt(64))
    );

    let unpack = Expr::Unpack {
        struct_id: 2,
        variant: Some(0),
        value: Box::new(Expr::Var(VarId::from("carrier"))),
    };
    assert_eq!(
        rendered_type_of(&unpack, &program, &scope),
        Some(Type::Bool)
    );
}

#[test]
fn effective_type_equality_matches_lean_reference_erasure() {
    let value = Type::UInt(64);
    let reference = Type::Reference(Box::new(value.clone()));
    assert!(effective_types_equal(&reference, &value));

    let first_root = Type::MutableRef {
        inner: Box::new(value.clone()),
        root: Box::new(Type::Bool),
    };
    let second_root = Type::MutableRef {
        inner: Box::new(value),
        root: Box::new(Type::Address),
    };
    assert!(effective_types_equal(&first_root, &second_root));
}

#[test]
fn rendered_mutation_updates_promote_value_form_parents() {
    let program = empty_program();
    let mut scope = BTreeMap::new();
    scope.insert(VarId::from("parent"), mutable_u64());
    scope.insert(VarId::from("child"), Type::UInt(64));

    let write_ref = Expr::WriteRef {
        reference: Box::new(Expr::Var(VarId::from("parent"))),
        value: Box::new(lit_u64(1)),
    };
    assert_eq!(
        type_of(&write_ref, &scope, &program).unwrap(),
        mutable_u64()
    );
    assert_eq!(
        rendered_type_of(&write_ref, &program, &scope),
        Some(mutable_u64())
    );

    // WriteBack still supports the value-form parent that its path-update
    // lowering promotes into a Mutation at render time. WriteRef itself is
    // stricter: its target must already be a MutableRef.
    scope.insert(VarId::from("parent"), Type::UInt(64));
    let write_back = Expr::WriteBack {
        node: BorrowNode::Reference(VarId::from("parent")),
        edge: BorrowEdge::Direct,
        child: VarId::from("child"),
        world: None,
    };
    assert_eq!(
        type_of(&write_back, &scope, &program).unwrap(),
        Type::UInt(64)
    );
    assert_eq!(
        rendered_type_of(&write_back, &program, &scope),
        Some(mutable_u64())
    );
}

#[test]
fn rendered_if_type_matches_mutation_arm_coercion() {
    let program = empty_program();
    let mut scope = BTreeMap::new();
    scope.insert(VarId::from("mutation"), mutable_u64());
    scope.insert(VarId::from("value"), Type::UInt(64));
    let expression = Expr::If {
        cond: Box::new(Expr::Const(Const::Bool(true))),
        then_branch: Box::new(body(vec![], Expr::Var(VarId::from("value")))),
        else_branch: Box::new(body(vec![], Expr::Var(VarId::from("mutation")))),
    };

    assert_eq!(
        type_of(&expression, &scope, &program).unwrap(),
        Type::UInt(64)
    );
    assert_eq!(
        rendered_type_of(&expression, &program, &scope),
        Some(mutable_u64())
    );
}

#[test]
fn rendered_quantifier_body_uses_native_abi_type_in_branch_join() {
    let mut program = empty_program();
    add_native(
        &mut program,
        1,
        native(
            "native_value",
            sig(vec![], mutable_u64()),
            0,
            crate::ir::Effects::PURE,
            true,
        ),
    );
    let values = VarId::from("values");
    let scope = BTreeMap::from([(values.clone(), Type::Vector(Box::new(Type::UInt(64))))]);
    let mapped = Expr::Quantifier {
        kind: crate::ir::QuantifierKind::Map,
        binder: VarId::from("item"),
        binder_type: Type::UInt(64),
        domain: crate::ir::QuantDomain::Collection(Box::new(Expr::Var(values.clone()))),
        body: Box::new(body(
            vec![],
            Expr::Call {
                fun: 1,
                type_args: Vec::new(),
                args: Vec::new(),
            },
        )),
    };
    assert_eq!(
        type_of(&mapped, &scope, &program).unwrap(),
        Type::Vector(Box::new(mutable_u64()))
    );
    assert_eq!(
        rendered_type_of(&mapped, &program, &scope),
        Some(Type::Vector(Box::new(Type::UInt(64))))
    );

    let branch = Expr::If {
        cond: Box::new(Expr::Const(Const::Bool(true))),
        then_branch: Box::new(body(vec![], mapped)),
        else_branch: Box::new(body(vec![], Expr::Var(values))),
    };
    assert_eq!(
        rendered_type_of(&branch, &program, &scope),
        Some(Type::Vector(Box::new(Type::UInt(64))))
    );
}

#[test]
fn rendered_if_type_rejects_incompatible_known_arms() {
    let program = empty_program();
    let scope = BTreeMap::new();
    let expressions = [
        Expr::If {
            cond: Box::new(Expr::Const(Const::Bool(true))),
            then_branch: Box::new(body(
                vec![],
                Expr::Tuple(vec![lit_u64(1), Expr::Const(Const::Bool(true))]),
            )),
            else_branch: Box::new(body(vec![], lit_u64(2))),
        },
        Expr::If {
            cond: Box::new(Expr::Const(Const::Bool(true))),
            then_branch: Box::new(body(
                vec![],
                Expr::Tuple(vec![lit_u64(1), Expr::Const(Const::Bool(true))]),
            )),
            else_branch: Box::new(body(
                vec![],
                Expr::Tuple(vec![
                    lit_u64(2),
                    Expr::Const(Const::Address(num::BigUint::from(0u8))),
                ]),
            )),
        },
    ];

    for expression in expressions {
        assert_eq!(rendered_type_of(&expression, &program, &scope), None);
    }
}

#[test]
fn rendered_oracle_reuses_canonical_block_binding_rules() {
    let program = empty_program();
    let scope = BTreeMap::new();
    let singleton = Block {
        stmts: vec![crate::ir::Stmt::Let {
            pattern: vec![Some(VarId::from("x"))],
            value: Expr::Tuple(vec![lit_u64(1)]),
        }],
        tail: BlockTail::Value(Expr::Var(VarId::from("x"))),
    };
    assert_eq!(
        rendered_block_value_type(&singleton, &program, &scope),
        Some(Type::UInt(64))
    );

    let pair = Block {
        stmts: vec![crate::ir::Stmt::Let {
            pattern: vec![Some(VarId::from("x")), Some(VarId::from("y"))],
            value: Expr::Tuple(vec![lit_u64(1), Expr::Const(Const::Bool(true))]),
        }],
        tail: BlockTail::Value(Expr::Tuple(vec![
            Expr::Var(VarId::from("x")),
            Expr::Var(VarId::from("y")),
        ])),
    };
    assert_eq!(
        rendered_block_value_type(&pair, &program, &scope),
        Some(Type::Tuple(vec![Type::UInt(64), Type::Bool]))
    );
}

#[test]
fn rendered_oracle_explicitly_leaves_unclassified_forms_unknown() {
    let program = empty_program();
    let scope = BTreeMap::new();
    let expression = Expr::ToProp(Box::new(Expr::Const(Const::Bool(true))));

    assert_eq!(type_of(&expression, &scope, &program).unwrap(), Type::Prop);
    assert_eq!(rendered_type_of(&expression, &program, &scope), None);
}

#[test]
fn rendered_bit_operations_have_their_emitted_uint_widths() {
    let program = empty_program();
    let scope = BTreeMap::new();
    let u8_value = Expr::Const(Const::UInt {
        bits: 8,
        value: 1u8.into(),
    });

    let cases = [
        (
            Expr::BitOp(BitOp::Extract {
                high: 6,
                low: 3,
                operand: Box::new(u8_value.clone()),
            }),
            Type::UInt(4),
        ),
        (
            Expr::BitOp(BitOp::ZeroExtend {
                bits: 8,
                operand: Box::new(u8_value.clone()),
            }),
            Type::UInt(16),
        ),
        (
            Expr::BitOp(BitOp::SignExtend {
                bits: 24,
                operand: Box::new(u8_value.clone()),
            }),
            Type::UInt(32),
        ),
        (
            Expr::BitOp(BitOp::Concat {
                high: Box::new(u8_value.clone()),
                low: Box::new(u8_value),
            }),
            Type::UInt(16),
        ),
    ];

    for (expression, expected) in cases {
        assert_eq!(
            rendered_type_of(&expression, &program, &scope),
            Some(expected)
        );
    }
}
