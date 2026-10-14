use std::cell::RefCell;
use std::collections::BTreeMap;

use crate::ir::{
    Block, BlockTail, Effects, Expr, Field, Function, FunctionKind, MatchArm, Param, Signature,
    Stmt, Struct, Type, VarId, Variant,
};
use crate::render::expr::{with_match_arm_binding_types, ExprCtx};
use crate::render::{render_program, RenderError};

use super::fixtures::{add_function, add_struct, empty_program, lit_u64};

fn carrier_match(prefix: &str) -> Expr {
    let payload = VarId::from(format!("{prefix}_payload"));
    let left = VarId::from(format!("{prefix}_left"));
    let right = VarId::from(format!("{prefix}_right"));
    Expr::Match {
        struct_id: 7,
        selector: Box::new(Expr::Var(VarId::from("carrier"))),
        cases: vec![MatchArm {
            variant: 0,
            bindings: vec![payload.clone()],
            body: Box::new(Block {
                stmts: vec![Stmt::Let {
                    pattern: vec![Some(left.clone()), Some(right)],
                    value: Expr::Var(payload),
                }],
                tail: BlockTail::Value(Expr::Var(left)),
            }),
        }],
    }
}

fn carrier_tuple_match(prefix: &str) -> Expr {
    let payload = VarId::from(format!("{prefix}_payload"));
    let left = VarId::from(format!("{prefix}_left"));
    let right = VarId::from(format!("{prefix}_right"));
    Expr::Match {
        struct_id: 7,
        selector: Box::new(Expr::Var(VarId::from("carrier"))),
        cases: vec![MatchArm {
            variant: 0,
            bindings: vec![payload.clone()],
            body: Box::new(Block {
                stmts: vec![Stmt::Let {
                    pattern: vec![Some(left.clone()), Some(right.clone())],
                    value: Expr::Var(payload),
                }],
                tail: BlockTail::Value(Expr::Tuple(vec![Expr::Var(left), Expr::Var(right)])),
            }),
        }],
    }
}

fn carrier_function(name: &str, body: Block) -> Function {
    Function {
        module: 0,
        name: name.to_string(),
        signature: Signature {
            type_params: Vec::new(),
            params: vec![Param {
                name: "carrier".to_string(),
                var: VarId::from("carrier"),
                ty: Type::Struct {
                    struct_id: 7,
                    type_args: vec![Type::Tuple(vec![Type::UInt(64), Type::Bool])],
                },
            }],
            return_type: Type::UInt(64),
        },
        body,
        kind: FunctionKind::Source,
        effects: Effects::PURE,
        explicit_pure: true,
    }
}

fn target_typed_carrier_function() -> Function {
    let left = VarId::from("targeted_result_left");
    let right = VarId::from("targeted_result_right");
    let mut function = carrier_function(
        "targeted",
        Block {
            stmts: vec![Stmt::Let {
                pattern: vec![Some(left.clone()), Some(right.clone())],
                value: carrier_tuple_match("targeted"),
            }],
            tail: BlockTail::Value(Expr::Tuple(vec![Expr::Var(left), Expr::Var(right)])),
        },
    );
    function.signature.return_type = Type::Tuple(vec![Type::UInt(64), Type::Bool]);
    function
}

#[test]
fn generic_match_payload_uses_concrete_selector_type_in_both_render_paths() {
    let mut program = empty_program();
    add_struct(
        &mut program,
        7,
        Struct {
            module_id: 0,
            name: "Carrier".to_string(),
            qualified_name: "p::m::Carrier".to_string(),
            type_params: vec!["T".to_string()],
            fields: Vec::new(),
            variants: Some(vec![Variant {
                name: "Carry".to_string(),
                tag: 0,
                fields: vec![Field {
                    name: "payload".to_string(),
                    field_type: Type::TypeParam(0),
                }],
            }]),
            is_native: false,
        },
    );

    add_function(
        &mut program,
        0,
        carrier_function(
            "normal",
            Block {
                stmts: vec![Stmt::Let {
                    pattern: vec![Some(VarId::from("result"))],
                    value: carrier_match("normal"),
                }],
                tail: BlockTail::Value(Expr::Var(VarId::from("result"))),
            },
        ),
    );
    add_function(
        &mut program,
        1,
        carrier_function("coerced", Block::just(carrier_match("coerced"))),
    );
    add_function(&mut program, 2, target_typed_carrier_function());

    let output = render_program(&program).unwrap();
    for prefix in ["normal", "coerced"] {
        assert!(
            output.contains(&format!(
                "let ({prefix}_left, {prefix}_right) := {prefix}_payload"
            )),
            "{output}"
        );
        assert!(
            !output.contains(&format!("let {prefix}_left : Unit := ()")),
            "{output}"
        );
    }
    assert!(
        output.contains("let (targeted_left, targeted_right) := targeted_payload"),
        "{output}"
    );
    assert!(
        !output.contains("let targeted_left : Unit := ()"),
        "{output}"
    );
    assert!(
        output.contains("let (targeted_result_left, targeted_result_right) := match carrier with"),
        "{output}"
    );
    assert!(
        !output.contains("let targeted_result_left : Unit := ()"),
        "{output}"
    );
    assert!(
        !output.contains("let targeted_result_right : Unit := ()"),
        "{output}"
    );
}

#[test]
fn eval_match_flattens_every_arm_to_unit() {
    let mut program = empty_program();
    add_struct(
        &mut program,
        8,
        Struct {
            module_id: 0,
            name: "Choice".to_string(),
            qualified_name: "p::m::Choice".to_string(),
            type_params: Vec::new(),
            fields: Vec::new(),
            variants: Some(vec![
                Variant {
                    name: "value".to_string(),
                    tag: 3,
                    fields: vec![Field {
                        name: "payload".to_string(),
                        field_type: Type::UInt(64),
                    }],
                },
                Variant {
                    name: "empty".to_string(),
                    tag: 9,
                    fields: Vec::new(),
                },
            ]),
            is_native: false,
        },
    );
    add_function(
        &mut program,
        0,
        Function {
            module: 0,
            name: "discard_choice".to_string(),
            signature: Signature {
                type_params: Vec::new(),
                params: vec![Param {
                    name: "choice".to_string(),
                    var: "choice".into(),
                    ty: Type::Struct {
                        struct_id: 8,
                        type_args: Vec::new(),
                    },
                }],
                return_type: Type::UInt(64),
            },
            body: Block {
                stmts: vec![Stmt::Eval(Expr::Match {
                    struct_id: 8,
                    selector: Box::new(Expr::Var("choice".into())),
                    cases: vec![
                        MatchArm {
                            variant: 3,
                            bindings: vec!["payload".into()],
                            body: Box::new(Block::just(Expr::Var("payload".into()))),
                        },
                        MatchArm {
                            variant: 9,
                            bindings: Vec::new(),
                            body: Box::new(Block::just(Expr::Unit)),
                        },
                    ],
                })],
                tail: BlockTail::Value(lit_u64(7)),
            },
            kind: FunctionKind::Source,
            effects: Effects::PURE,
            explicit_pure: true,
        },
    );

    let output = render_program(&program).unwrap();
    assert!(output.contains("let _ := match choice with"), "{output}");
    assert!(output.contains("let _ := payload"), "{output}");
    assert!(
        !output.contains("| .value payload =>\n    payload"),
        "{output}"
    );
}

#[test]
fn value_match_coerces_scalar_value_arm_to_mutation() {
    let mut program = empty_program();
    add_struct(
        &mut program,
        8,
        Struct {
            module_id: 0,
            name: "Choice".to_string(),
            qualified_name: "p::m::Choice".to_string(),
            type_params: Vec::new(),
            fields: Vec::new(),
            variants: Some(vec![
                Variant {
                    name: "left".to_string(),
                    tag: 3,
                    fields: Vec::new(),
                },
                Variant {
                    name: "right".to_string(),
                    tag: 9,
                    fields: Vec::new(),
                },
            ]),
            is_native: false,
        },
    );
    let mutation = Type::MutableRef {
        inner: Box::new(Type::UInt(64)),
        root: Box::new(Type::UInt(64)),
    };
    add_function(
        &mut program,
        0,
        Function {
            module: 0,
            name: "coerce_choice".to_string(),
            signature: Signature {
                type_params: Vec::new(),
                params: vec![
                    Param {
                        name: "choice".to_string(),
                        var: "choice".into(),
                        ty: Type::Struct {
                            struct_id: 8,
                            type_args: Vec::new(),
                        },
                    },
                    Param {
                        name: "mutation".to_string(),
                        var: "mutation".into(),
                        ty: mutation,
                    },
                    Param {
                        name: "value".to_string(),
                        var: "value".into(),
                        ty: Type::UInt(64),
                    },
                ],
                return_type: Type::Unit,
            },
            body: Block {
                stmts: vec![Stmt::Let {
                    pattern: vec![Some("result".into())],
                    value: Expr::Match {
                        struct_id: 8,
                        selector: Box::new(Expr::Var("choice".into())),
                        cases: vec![
                            MatchArm {
                                variant: 3,
                                bindings: Vec::new(),
                                body: Box::new(Block::just(Expr::Var("mutation".into()))),
                            },
                            MatchArm {
                                variant: 9,
                                bindings: Vec::new(),
                                body: Box::new(Block::just(Expr::Var("value".into()))),
                            },
                        ],
                    },
                }],
                tail: BlockTail::Value(Expr::Unit),
            },
            kind: FunctionKind::Source,
            effects: Effects::PURE,
            explicit_pure: true,
        },
    );

    let output = render_program(&program).unwrap();
    assert!(output.contains("| .left =>\n      mutation"), "{output}");
    assert!(output.contains("Mutation.ofLocal"), "{output}");
    assert!(!output.contains("render fallback"), "{output}");
}

#[test]
fn match_binding_type_scope_restores_shadowed_entry_after_error() {
    let program = empty_program();
    let var_overrides = BTreeMap::new();
    let render_context = crate::render::context::RenderContext::new(
        &program,
        crate::render::loop_termination::LoopRenderContext::default(),
    );
    let world_type_overrides = crate::render::ty::WorldTypeOverrides::default();
    let binding = VarId::from("payload");
    let ctx = ExprCtx {
        render_context: &render_context,
        program: &program,
        current_module: None,
        type_params: None,
        function_return_type: None,
        world_param: None,
        var_overrides: &var_overrides,
        var_types: RefCell::new(BTreeMap::from([(binding.clone(), Type::Bool)])),
        borrow_sources: BTreeMap::new(),
        borrow_mut_origins: BTreeMap::new(),
        borrow_mut_derivatives: BTreeMap::new(),
        mutref_rebind_source: BTreeMap::new(),
        is_aborts: false,
        redundant_borrowloc: BTreeMap::new(),
        var_target_types: BTreeMap::new(),
        mutation_users: render_context.mutation_users(),
        world_type_overrides: &world_type_overrides,
        caller_is_lemma_pkg: false,
        caller_has_tycode_universe: false,
        caller_module_has_bag_struct: false,
        current_fn_id: 0,
    };
    let fields = [Field {
        name: "payload".to_string(),
        field_type: Type::TypeParam(0),
    }];

    let result = with_match_arm_binding_types(
        std::slice::from_ref(&binding),
        &fields,
        &[Type::UInt(64)],
        &ctx,
        || {
            assert_eq!(ctx.var_types.borrow().get(&binding), Some(&Type::UInt(64)));
            Err::<(), _>(RenderError::UnknownStructId { id: 999 })
        },
    );

    assert!(matches!(
        result,
        Err(RenderError::UnknownStructId { id: 999 })
    ));
    assert_eq!(ctx.var_types.borrow().get(&binding), Some(&Type::Bool));
}
