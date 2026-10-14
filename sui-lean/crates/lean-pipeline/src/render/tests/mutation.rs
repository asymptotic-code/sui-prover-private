//! End-to-end render tests for the new typed-Mutation IR variants
//! (`Expr::BorrowVecIndex`, `Expr::BorrowMapKey`, `Expr::IsParent`,
//! `Expr::WriteBack { edge: VecIndex | MapKey, .. }`).
//!
//! These are the variants stage 2's borrow-mut callsite recognizer
//! and `Operation::IsParent` lift produce. The renderer maps them to
//! `Prover.Mutation.*` prelude calls -- see
//! `plans/lean-pipeline/mutable-references.md`.

use crate::ir::{BorrowEdge, BorrowNode, Expr, Field, Stmt, Struct, Type, VarId, Variant};
use crate::render::render_program;

use super::fixtures::*;

fn boxed(e: Expr) -> Box<Expr> {
    Box::new(e)
}

fn add_variant_field_enum(prog: &mut crate::ir::Program) {
    add_struct(
        prog,
        7,
        Struct {
            module_id: 0,
            name: "Carrier".to_string(),
            qualified_name: "p::m::Carrier".to_string(),
            type_params: Vec::new(),
            fields: Vec::new(),
            variants: Some(vec![
                Variant {
                    name: "Other".to_string(),
                    tag: 3,
                    fields: vec![Field {
                        name: "flag".to_string(),
                        field_type: Type::Bool,
                    }],
                },
                Variant {
                    name: "Selected".to_string(),
                    tag: 9,
                    fields: vec![
                        Field {
                            name: "flag".to_string(),
                            field_type: Type::Bool,
                        },
                        Field {
                            name: "value".to_string(),
                            field_type: Type::UInt(64),
                        },
                    ],
                },
            ]),
            is_native: false,
        },
    );
}

/// Register a plain struct under `id`. A borrow edge names a datatype's
/// TAG now (`render::struct_idx`), so a fixture that borrows through an
/// unregistered `StructId` has no name to render.
fn add_plain_struct(prog: &mut crate::ir::Program, id: u32, name: &str) {
    add_struct(
        prog,
        id as usize,
        Struct {
            module_id: 0,
            name: name.to_string(),
            qualified_name: format!("p::m::{name}"),
            type_params: Vec::new(),
            fields: vec![Field {
                name: "f".to_string(),
                field_type: Type::UInt(64),
            }],
            variants: None,
            is_native: false,
        },
    );
}

fn carrier_type() -> Type {
    Type::Struct {
        struct_id: 7,
        type_args: Vec::new(),
    }
}

fn add_vec_map_payload_types(prog: &mut crate::ir::Program) -> (Type, Type) {
    prog.modules.insert(
        1,
        crate::ir::Module {
            name: "vec_map".to_string(),
            package_name: "Sui".to_string(),
            address: String::new(),
            required_imports: Vec::new(),
            is_native: true,
        },
    );
    add_struct(
        prog,
        8,
        Struct {
            module_id: 0,
            name: "Payload".to_string(),
            qualified_name: "p::m::Payload".to_string(),
            type_params: Vec::new(),
            fields: vec![Field {
                name: "amount".to_string(),
                field_type: Type::UInt(64),
            }],
            variants: None,
            is_native: false,
        },
    );
    add_struct(
        prog,
        9,
        Struct {
            module_id: 1,
            name: "VecMap".to_string(),
            qualified_name: "sui::vec_map::VecMap".to_string(),
            type_params: vec!["K".to_string(), "V".to_string()],
            fields: Vec::new(),
            variants: None,
            is_native: true,
        },
    );
    let payload = Type::Struct {
        struct_id: 8,
        type_args: Vec::new(),
    };
    let vec_map = Type::Struct {
        struct_id: 9,
        type_args: vec![Type::UInt(64), payload.clone()],
    };
    (payload, vec_map)
}

#[test]
fn borrow_variant_field_emits_tagged_mutation_selector() {
    let mut prog = empty_program();
    add_variant_field_enum(&mut prog);
    let carrier = carrier_type();
    add_function(
        &mut prog,
        0,
        func(
            "borrow_selected_value",
            sig(
                vec![param(
                    "carrier",
                    Type::MutableRef {
                        inner: Box::new(carrier.clone()),
                        root: Box::new(carrier.clone()),
                    },
                )],
                Type::MutableRef {
                    inner: Box::new(Type::UInt(64)),
                    root: Box::new(carrier),
                },
            ),
            body(
                Vec::new(),
                Expr::Borrow {
                    step: crate::ir::path::PathStep::VariantField {
                        struct_id: 7,
                        variant: 9,
                        field_index: 1,
                    },
                    base: boxed(var("carrier")),
                },
            ),
            0,
        ),
    );

    let out = render_program(&prog).expect("render");
    assert!(
        out.contains("Mutation.borrowEnumField AnyKey _ _ carrier StructIdx.p__p__m__Carrier 9 1"),
        "missing tagged enum-field borrow: {out}"
    );
    assert!(
        out.contains(
            "fun s : Carrier => match s with | .Selected __vf0 __vf1 => __vf1 | _ => default"
        ),
        "missing variant-aware selector: {out}"
    );
}

#[test]
fn update_variant_field_emits_variant_preserving_match() {
    let mut prog = empty_program();
    add_variant_field_enum(&mut prog);
    let carrier = carrier_type();
    add_function(
        &mut prog,
        0,
        func(
            "update_selected_value",
            sig(
                vec![
                    param("carrier", carrier.clone()),
                    param("replacement", Type::UInt(64)),
                ],
                carrier,
            ),
            body(
                Vec::new(),
                Expr::Update {
                    step: crate::ir::path::PathStep::VariantField {
                        struct_id: 7,
                        variant: 9,
                        field_index: 1,
                    },
                    base: boxed(var("carrier")),
                    value: boxed(var("replacement")),
                },
            ),
            0,
        ),
    );

    let out = render_program(&prog).expect("render");
    assert!(out.contains("match carrier with"), "missing match: {out}");
    assert!(
        out.contains("| .Selected __f0 __f1 => .Selected __f0 replacement"),
        "selected variant was not rebuilt: {out}"
    );
    assert!(
        out.contains("| other => other"),
        "non-selected variants must be preserved: {out}"
    );
}

#[test]
fn enum_field_writeback_does_not_capture_child_named_like_generated_binder() {
    let mut prog = empty_program();
    add_variant_field_enum(&mut prog);
    let carrier = carrier_type();
    add_function(
        &mut prog,
        0,
        func(
            "write_selected_value_without_capture",
            sig(
                vec![
                    param("carrier", carrier.clone()),
                    crate::ir::Param {
                        name: "__f0".to_string(),
                        var: VarId::from("$replacement"),
                        ty: Type::UInt(64),
                    },
                ],
                Type::Unit,
            ),
            body(
                vec![Stmt::Eval(Expr::WriteBack {
                    node: BorrowNode::LocalRoot(VarId::from("carrier")),
                    edge: BorrowEdge::EnumField {
                        struct_id: 7,
                        variant: 9,
                        field_index: 1,
                    },
                    child: VarId::from("$replacement"),
                    world: None,
                })],
                Expr::Unit,
            ),
            0,
        ),
    );

    let out = render_program(&prog).expect("render");
    assert!(
        out.contains("| .Selected __f1 __f2 => .Selected __f1 __f0"),
        "generated enum binders captured the outer __f0 child: {out}"
    );
    assert!(
        !out.contains("| .Selected __f0"),
        "the outer __f0 name was reused as a match binder: {out}"
    );
}

#[test]
fn enum_first_hyper_writeback_recurses_from_the_selected_payload() {
    for local_root in [false, true] {
        let mut prog = empty_program();
        add_variant_field_enum(&mut prog);
        add_struct(
            &mut prog,
            8,
            Struct {
                module_id: 0,
                name: "Payload".to_string(),
                qualified_name: "p::m::Payload".to_string(),
                type_params: Vec::new(),
                fields: vec![Field {
                    name: "amount".to_string(),
                    field_type: Type::UInt(64),
                }],
                variants: None,
                is_native: false,
            },
        );
        let payload = Type::Struct {
            struct_id: 8,
            type_args: Vec::new(),
        };
        prog.structs
            .get_mut(&7)
            .unwrap()
            .variants
            .as_mut()
            .unwrap()
            .iter_mut()
            .find(|variant| variant.tag == 9)
            .unwrap()
            .fields[1]
            .field_type = payload;
        let carrier = carrier_type();
        let parent_type = if local_root {
            carrier.clone()
        } else {
            Type::MutableRef {
                inner: Box::new(carrier.clone()),
                root: Box::new(carrier.clone()),
            }
        };
        let child_type = if local_root {
            Type::UInt(64)
        } else {
            Type::MutableRef {
                inner: Box::new(Type::UInt(64)),
                root: Box::new(carrier),
            }
        };
        let node = if local_root {
            BorrowNode::LocalRoot(VarId::from("parent"))
        } else {
            BorrowNode::Reference(VarId::from("parent"))
        };
        add_function(
            &mut prog,
            0,
            func(
                "write_selected_amount",
                sig(
                    vec![param("parent", parent_type), param("child", child_type)],
                    Type::Unit,
                ),
                body(
                    vec![Stmt::Eval(Expr::WriteBack {
                        node,
                        edge: BorrowEdge::Hyper(vec![
                            BorrowEdge::EnumField {
                                struct_id: 7,
                                variant: 9,
                                field_index: 1,
                            },
                            BorrowEdge::StructField {
                                struct_id: 8,
                                field_index: 0,
                            },
                        ]),
                        child: VarId::from("child"),
                        world: None,
                    })],
                    Expr::Unit,
                ),
                0,
            ),
        );

        let out = render_program(&prog).expect("render");
        assert!(out.contains("match parent"), "missing enum match: {out}");
        assert!(
            out.contains("| .Selected __f0 __f1 => .Selected __f0 { __f1 with amount :="),
            "selected payload was not used as the recursive parent: {out}"
        );
        assert!(
            !out.contains("render fallback"),
            "unexpected fallback: {out}"
        );
    }
}

#[test]
fn enum_first_hyper_writeback_reconstructs_an_intermediate_vec_map() {
    let mut prog = empty_program();
    let (payload, _) = add_vec_map_payload_types(&mut prog);
    add_struct(
        &mut prog,
        7,
        Struct {
            module_id: 0,
            name: "Carrier".to_string(),
            qualified_name: "p::m::Carrier".to_string(),
            type_params: vec!["K".to_string(), "V".to_string()],
            fields: Vec::new(),
            variants: Some(vec![
                Variant {
                    name: "Other".to_string(),
                    tag: 3,
                    fields: Vec::new(),
                },
                Variant {
                    name: "Selected".to_string(),
                    tag: 9,
                    fields: vec![Field {
                        name: "items".to_string(),
                        field_type: Type::Struct {
                            struct_id: 9,
                            type_args: vec![Type::TypeParam(0), Type::TypeParam(1)],
                        },
                    }],
                },
            ]),
            is_native: false,
        },
    );
    let carrier = Type::Struct {
        struct_id: 7,
        type_args: vec![Type::UInt(64), payload.clone()],
    };
    add_function(
        &mut prog,
        0,
        func(
            "write_selected_map_value",
            sig(
                vec![
                    param(
                        "parent",
                        Type::MutableRef {
                            inner: Box::new(carrier.clone()),
                            root: Box::new(carrier.clone()),
                        },
                    ),
                    param(
                        "child",
                        Type::MutableRef {
                            inner: Box::new(Type::UInt(64)),
                            root: Box::new(carrier),
                        },
                    ),
                ],
                Type::Unit,
            ),
            body(
                vec![Stmt::Eval(Expr::WriteBack {
                    node: BorrowNode::Reference(VarId::from("parent")),
                    edge: BorrowEdge::Hyper(vec![
                        BorrowEdge::EnumField {
                            struct_id: 7,
                            variant: 9,
                            field_index: 0,
                        },
                        BorrowEdge::MapKey {
                            key_type: Type::UInt(64),
                            value_type: Type::Struct {
                                struct_id: 8,
                                type_args: Vec::new(),
                            },
                        },
                        BorrowEdge::StructField {
                            struct_id: 8,
                            field_index: 0,
                        },
                    ]),
                    child: VarId::from("child"),
                    world: None,
                })],
                Expr::Unit,
            ),
            0,
        ),
    );

    let out = render_program(&prog).expect("render");
    assert!(
        out.contains("match parent.val with"),
        "missing enum match: {out}"
    );
    assert!(
        out.contains("_root_.Vec_map.get"),
        "missing VecMap lookup under enum payload: {out}"
    );
    assert!(
        out.contains("_root_.Vec_map.set"),
        "enum payload update collapsed to identity instead of rebuilding VecMap: {out}"
    );
    assert!(
        out.contains("AnyKey.k_u64"),
        "generic enum payload types were not substituted before map reconstruction: {out}"
    );
    assert!(
        out.contains("with amount := child.val"),
        "missing nested payload field update: {out}"
    );
}

#[test]
fn vector_first_hyper_writeback_reconstructs_an_intermediate_vec_map() {
    let mut prog = empty_program();
    let (payload, vec_map) = add_vec_map_payload_types(&mut prog);
    let container = Type::Vector(Box::new(vec_map));
    add_function(
        &mut prog,
        0,
        func(
            "write_vector_map_value",
            sig(
                vec![
                    param("parent", container.clone()),
                    param(
                        "child",
                        Type::MutableRef {
                            inner: Box::new(Type::UInt(64)),
                            root: Box::new(container),
                        },
                    ),
                ],
                Type::Unit,
            ),
            body(
                vec![Stmt::Eval(Expr::WriteBack {
                    node: BorrowNode::LocalRoot(VarId::from("parent")),
                    edge: BorrowEdge::Hyper(vec![
                        BorrowEdge::VecIndex,
                        BorrowEdge::MapKey {
                            key_type: Type::UInt(64),
                            value_type: Type::Struct {
                                struct_id: 8,
                                type_args: Vec::new(),
                            },
                        },
                        BorrowEdge::StructField {
                            struct_id: 8,
                            field_index: 0,
                        },
                    ]),
                    child: VarId::from("child"),
                    world: None,
                })],
                Expr::Unit,
            ),
            0,
        ),
    );

    let out = render_program(&prog).expect("render");
    assert!(
        out.contains("parent.set __hi0"),
        "missing outer vector reconstruction: {out}"
    );
    assert!(
        out.contains("_root_.Vec_map.get") && out.contains("_root_.Vec_map.set"),
        "vector element map update collapsed to identity: {out}"
    );
    assert!(
        out.contains("with amount := child.val"),
        "missing nested payload field update: {out}"
    );
}

#[test]
fn hyper_writeback_rejects_mismatched_typed_struct_path() {
    let mut prog = empty_program();
    let (payload, vec_map) = add_vec_map_payload_types(&mut prog);
    for (struct_id, name) in [(10, "ActualCarrier"), (11, "DeclaredCarrier")] {
        add_struct(
            &mut prog,
            struct_id,
            Struct {
                module_id: 0,
                name: name.to_string(),
                qualified_name: format!("p::m::{name}"),
                type_params: Vec::new(),
                fields: vec![Field {
                    name: "items".to_string(),
                    field_type: vec_map.clone(),
                }],
                variants: None,
                is_native: false,
            },
        );
    }
    let actual = Type::Struct {
        struct_id: 10,
        type_args: Vec::new(),
    };
    let container = Type::Vector(Box::new(actual));
    add_function(
        &mut prog,
        0,
        func(
            "reject_mismatched_hyper_path",
            sig(
                vec![
                    param("parent", container.clone()),
                    param(
                        "child",
                        Type::MutableRef {
                            inner: Box::new(Type::UInt(64)),
                            root: Box::new(container),
                        },
                    ),
                ],
                Type::Unit,
            ),
            body(
                vec![Stmt::Eval(Expr::WriteBack {
                    node: BorrowNode::LocalRoot(VarId::from("parent")),
                    edge: BorrowEdge::Hyper(vec![
                        BorrowEdge::VecIndex,
                        BorrowEdge::StructField {
                            struct_id: 11,
                            field_index: 0,
                        },
                        BorrowEdge::MapKey {
                            key_type: Type::UInt(64),
                            value_type: payload,
                        },
                        BorrowEdge::StructField {
                            struct_id: 8,
                            field_index: 0,
                        },
                    ]),
                    child: VarId::from("child"),
                    world: None,
                })],
                Expr::Unit,
            ),
            0,
        ),
    );

    let out = render_program(&prog).expect("render");
    assert!(
        out.contains("render fallback")
            && out.contains("typed edge does not match inferred parent type"),
        "mismatched Hyper metadata must fail closed: {out}"
    );
    assert!(
        !out.contains("with items := parent.getD"),
        "mismatched Hyper metadata silently collapsed to an identity update: {out}"
    );
}

#[test]
fn borrow_vec_index_emits_mutation_prelude_call() {
    // fn f(v: vector<u64>, i: u64): &mut u64 { vector::borrow_mut(&mut v, i) }
    // Stage 2 lifts this to `Expr::Borrow { step: crate::ir::path::PathStep::VecIndex(Var("i")), base: Var("v") }`.
    let mut prog = empty_program();
    let f = func(
        "f",
        sig(
            vec![
                param("v", Type::Vector(Box::new(Type::UInt(64)))),
                param("i", Type::UInt(64)),
            ],
            Type::MutableRef {
                inner: Box::new(Type::UInt(64)),
                root: Box::new(Type::Vector(Box::new(Type::UInt(64)))),
            },
        ),
        body(
            vec![],
            Expr::Borrow {
                step: crate::ir::path::PathStep::VecIndex(boxed(var("i"))),
                base: boxed(var("v")),
            },
        ),
        0,
    );
    add_function(&mut prog, 0, f);

    let out = render_program(&prog).expect("render");
    assert!(
        out.contains("Prover.Mutation.Mutation.borrowVecIndex"),
        "missing borrowVecIndex call: {out}"
    );
}

#[test]
fn borrow_map_key_emits_mutation_prelude_call_with_any_key_wrap() {
    let mut prog = empty_program();
    // Signature carries a `MutableRef` parameter. Primitive key types
    // still render with their concrete `AnyKey` constructor.
    let f = func(
        "f",
        sig(
            vec![
                param(
                    "t",
                    Type::MutableRef {
                        inner: Box::new(Type::UInt(64)),
                        root: Box::new(Type::UInt(64)),
                    },
                ), // placeholder, real shape is Table<K,V>
                param("k", Type::UInt(64)),
            ],
            Type::UInt(64),
        ),
        body(
            vec![],
            Expr::Borrow {
                step: crate::ir::path::PathStep::MapKey {
                    key: boxed(var("k")),
                    key_type: Type::UInt(64),
                    value_type: Type::UInt(64),
                    df_value: None,
                },
                base: boxed(var("t")),
            },
        ),
        0,
    );
    add_function(&mut prog, 0, f);

    let out = render_program(&prog).expect("render");
    assert!(
        out.contains("Prover.Mutation.Mutation.borrowMapKey"),
        "missing borrowMapKey call: {out}"
    );
    // Slice 2 of item B (plans/lean-pipeline/item-b-real-anykey-work-plan.md):
    // primitive `key_type` now emits the real `AnyKey.k_u64 <key>`
    // wrap; the placeholder `AnyKey.unit` only fires for non-
    // concrete keys (struct, TypeParam, etc.).
    assert!(
        out.contains("AnyKey.k_u64 k"),
        "expected real AnyKey.k_u64 wrap: {out}"
    );
    assert!(
        !out.contains("AnyKey.unit (fun _ _ => default)"),
        "leftover AnyKey.unit placeholder at borrowMapKey site: {out}"
    );
}

#[test]
fn is_parent_emits_mutation_prelude_call_with_edge_literal() {
    let mut prog = empty_program();
    // Signature uses Mutation and the structural-key placeholder emits as
    // `AnyKey.unit`.
    let f = func(
        "f",
        sig(
            vec![
                param(
                    "parent",
                    Type::MutableRef {
                        inner: Box::new(Type::UInt(64)),
                        root: Box::new(Type::UInt(64)),
                    },
                ),
                param("child", Type::UInt(64)),
            ],
            Type::Bool,
        ),
        body(
            vec![],
            Expr::IsParent {
                node: BorrowNode::Reference(VarId::from("parent")),
                edge: BorrowEdge::MapKey {
                    key_type: Type::Address,
                    value_type: Type::UInt(64),
                },
                child: VarId::from("child"),
            },
        ),
        0,
    );
    add_function(&mut prog, 0, f);

    let out = render_program(&prog).expect("render");
    assert!(
        out.contains("Prover.Mutation.Mutation.isParent"),
        "missing isParent call: {out}"
    );
    assert!(
        out.contains("Prover.Mutation.Edge.mapKey"),
        "missing Edge.mapKey literal: {out}"
    );
    // Slice 2 of item B (plans/lean-pipeline/item-b-real-anykey-work-plan.md):
    // concrete primitive `key_type` (Address here) now emits the
    // real `AnyKey.k_address <recovered_key>` wrap. The recovered
    // key is `default` because `child` isn't in `borrow_sources`
    // for this synthetic test fixture (no preceding BorrowMapKey
    // bound it), but the wrap shape is the real one.
    assert!(
        out.contains("AnyKey.k_address"),
        "expected real AnyKey.k_address wrap on Edge.mapKey: {out}"
    );
}

#[test]
fn is_parent_struct_field_edge_emits_struct_field_literal() {
    let mut prog = empty_program();
    add_plain_struct(&mut prog, 5, "Holder");
    // Signature uses Mutation so `key_slot` resolves to `AnyKey`
    // (vs `Unit`) and the `Edge.structField` literal carries
    // `AnyKey` in its first slot.
    let f = func(
        "f",
        sig(
            vec![
                param(
                    "parent",
                    Type::MutableRef {
                        inner: Box::new(Type::UInt(64)),
                        root: Box::new(Type::UInt(64)),
                    },
                ),
                param("child", Type::UInt(64)),
            ],
            Type::Bool,
        ),
        body(
            vec![],
            Expr::IsParent {
                node: BorrowNode::Reference(VarId::from("parent")),
                edge: BorrowEdge::StructField {
                    struct_id: 5,
                    field_index: 2,
                },
                child: VarId::from("child"),
            },
        ),
        0,
    );
    add_function(&mut prog, 0, f);

    let out = render_program(&prog).expect("render");
    assert!(
        out.contains("Prover.Mutation.Edge.structField AnyKey StructIdx.p__p__m__Holder 2"),
        "missing Edge.structField literal: {out}"
    );
}

#[test]
fn is_parent_hyper_edge_emits_is_parent_hyper_with_list_literal() {
    // Hyper chain (StructField then MapKey -- the canonical
    // `struct-field-on-Table` shape from navi/lending's
    // ValidatorSet) should lower to a `Mutation.isParentHyper`
    // call carrying a Lean `List (Edge Key)` literal, NOT a
    // single-edge `Mutation.isParent` and NOT a render error.
    let mut prog = empty_program();
    add_plain_struct(&mut prog, 7, "Holder");
    let f = func(
        "f",
        sig(
            vec![
                param(
                    "parent",
                    Type::MutableRef {
                        inner: Box::new(Type::UInt(64)),
                        root: Box::new(Type::UInt(64)),
                    },
                ),
                param("child", Type::UInt(64)),
            ],
            Type::Bool,
        ),
        body(
            vec![],
            Expr::IsParent {
                node: BorrowNode::Reference(VarId::from("parent")),
                edge: BorrowEdge::Hyper(vec![
                    BorrowEdge::StructField {
                        struct_id: 7,
                        field_index: 1,
                    },
                    BorrowEdge::MapKey {
                        key_type: Type::Address,
                        value_type: Type::UInt(64),
                    },
                ]),
                child: VarId::from("child"),
            },
        ),
        0,
    );
    add_function(&mut prog, 0, f);

    let out = render_program(&prog).expect("render");
    assert!(
        out.contains("Prover.Mutation.Mutation.isParentHyper"),
        "missing isParentHyper call: {out}"
    );
    // The list literal should hold both edges in chain order.
    assert!(
        out.contains("Prover.Mutation.Edge.structField AnyKey StructIdx.p__p__m__Holder 1"),
        "missing structField edge in chain: {out}"
    );
    assert!(
        out.contains("Prover.Mutation.Edge.mapKey"),
        "missing mapKey edge in chain: {out}"
    );
    // Crucially, no single-edge isParent fallback and no Hyper
    // unsupported-construct render error.
    assert!(
        !out.contains("Mutation.isParent AnyKey"),
        "unexpected single-edge isParent (should be isParentHyper): {out}"
    );
    assert!(
        !out.contains("IsParent on Hyper edge"),
        "unexpected Hyper render fallback: {out}"
    );
}

#[test]
fn is_parent_hyper_nested_flattens_to_single_list() {
    // Defensive: even though stage 2's `normalize_borrow_edge`
    // pre-flattens nested Hypers, the renderer flattens too. A
    // `Hyper([Hyper([SF1, SF2]), SF3])` input must emit a single
    // flat list with three elements, not a nested list literal
    // (which would type-mismatch against `List (Edge Key)`).
    let mut prog = empty_program();
    add_plain_struct(&mut prog, 1, "H1");
    add_plain_struct(&mut prog, 2, "H2");
    add_plain_struct(&mut prog, 3, "H3");
    let f = func(
        "f",
        sig(
            vec![
                param(
                    "parent",
                    Type::MutableRef {
                        inner: Box::new(Type::UInt(64)),
                        root: Box::new(Type::UInt(64)),
                    },
                ),
                param("child", Type::UInt(64)),
            ],
            Type::Bool,
        ),
        body(
            vec![],
            Expr::IsParent {
                node: BorrowNode::Reference(VarId::from("parent")),
                edge: BorrowEdge::Hyper(vec![
                    BorrowEdge::Hyper(vec![
                        BorrowEdge::StructField {
                            struct_id: 1,
                            field_index: 0,
                        },
                        BorrowEdge::StructField {
                            struct_id: 2,
                            field_index: 0,
                        },
                    ]),
                    BorrowEdge::StructField {
                        struct_id: 3,
                        field_index: 0,
                    },
                ]),
                child: VarId::from("child"),
            },
        ),
        0,
    );
    add_function(&mut prog, 0, f);

    let out = render_program(&prog).expect("render");
    assert!(
        out.contains("Prover.Mutation.Mutation.isParentHyper"),
        "missing isParentHyper call: {out}"
    );
    for (tag, fi) in [("H1", 0), ("H2", 0), ("H3", 0)] {
        let needle = format!(
            "Prover.Mutation.Edge.structField AnyKey StructIdx.p__p__m__{} {}",
            tag, fi
        );
        assert!(
            out.contains(&needle),
            "missing flattened entry {}: {}",
            needle,
            out
        );
    }
}

#[test]
fn writeback_vec_index_emits_mutation_writeback_call() {
    let mut prog = empty_program();
    let f = func(
        "f",
        sig(
            vec![
                param("parent", Type::Vector(Box::new(Type::UInt(64)))),
                param("child", Type::UInt(64)),
            ],
            Type::Unit,
        ),
        body(
            vec![Stmt::Eval(Expr::WriteBack {
                node: BorrowNode::LocalRoot(VarId::from("parent")),
                edge: BorrowEdge::VecIndex,
                child: VarId::from("child"),
                world: None,
            })],
            Expr::Unit,
        ),
        0,
    );
    add_function(&mut prog, 0, f);

    let out = render_program(&prog).expect("render");
    // LocalRoot variant uses bare List.set:
    assert!(out.contains(".set"), "missing List.set form: {out}");
}

#[test]
fn writeback_native_map_placeholder_structfield_then_mapkey_renders_native_set() {
    // The `&mut Table` two-step-borrow writeback shape from sui-system's
    // `candidate_validator_mut`: `let t = &mut self.candidates; let w = &t[k];
    // ...; write_back t`. Stage 2 emits the map-content borrow as
    // `Hyper([StructField(Table, <placeholder>), MapKey])` on the `&mut Table`
    // local. The leading StructField is a native-map CONTENT placeholder
    // (Table's real fields are id/size), NOT a literal field to descend into --
    // the write must go through `Table.set` on the map value itself. Before the
    // fix the composer descended the placeholder and hit `MapKey` with a
    // non-map (u64 `size`) parent, emitting the "MapKey writeback into a
    // non-native-map parent" render sorry. Regression pin for P1.
    let mut prog = empty_program();
    prog.modules.insert(
        1,
        crate::ir::Module {
            name: "table".to_string(),
            package_name: "Sui".to_string(),
            address: String::new(),
            required_imports: Vec::new(),
            is_native: true,
        },
    );
    add_struct(
        &mut prog,
        0,
        crate::ir::Struct {
            module_id: 1,
            name: "Table".to_string(),
            qualified_name: "sui::table::Table".to_string(),
            type_params: vec!["K".to_string(), "V".to_string()],
            // `sui::table::Table` real fields: id + size. The `size` field at
            // index 1 is what stage 2 uses as the map-content placeholder.
            fields: vec![
                crate::ir::Field {
                    name: "id".to_string(),
                    field_type: Type::UInt(64),
                },
                crate::ir::Field {
                    name: "size".to_string(),
                    field_type: Type::UInt(64),
                },
            ],
            variants: None,
            is_native: true,
        },
    );
    let table_ty = Type::Struct {
        struct_id: 0,
        type_args: vec![Type::Address, Type::UInt(64)],
    };
    let f = func(
        "f",
        sig(
            vec![
                param(
                    "parent",
                    Type::MutableRef {
                        inner: Box::new(table_ty.clone()),
                        root: Box::new(table_ty.clone()),
                    },
                ),
                // A Mutation child (already carries its own path) so the
                // writeback takes the `child_is_mut` Auto arm without needing
                // a `borrow_sources` key-recovery fixture.
                param(
                    "child",
                    Type::MutableRef {
                        inner: Box::new(Type::UInt(64)),
                        root: Box::new(Type::UInt(64)),
                    },
                ),
            ],
            Type::Unit,
        ),
        body(
            vec![Stmt::Eval(Expr::WriteBack {
                node: BorrowNode::Reference(VarId::from("parent")),
                edge: BorrowEdge::Hyper(vec![
                    BorrowEdge::StructField {
                        struct_id: 0,
                        field_index: 1,
                    },
                    BorrowEdge::MapKey {
                        key_type: Type::Address,
                        value_type: Type::UInt(64),
                    },
                ]),
                child: VarId::from("child"),
                world: None,
            })],
            Expr::Unit,
        ),
        0,
    );
    add_function(&mut prog, 0, f);

    let out = render_program(&prog).expect("render");
    assert!(
        out.contains("_root_.Table.set"),
        "native-map placeholder StructField should route the trailing MapKey \
         to Table.set on the map value, got:\n{out}"
    );
    assert!(
        !out.contains("non-native-map"),
        "must not fall to the non-native-map render sorry:\n{out}"
    );
}

#[test]
fn writeback_map_key_emits_typed_map_set() {
    let mut prog = empty_program();
    // Signature uses Mutation so the placeholder key emits as
    // `AnyKey.unit` rather than `()` -- see `key_unit_val`.
    let f = func(
        "f",
        sig(
            vec![
                param(
                    "parent",
                    Type::MutableRef {
                        inner: Box::new(Type::UInt(64)),
                        root: Box::new(Type::UInt(64)),
                    },
                ),
                param("child", Type::UInt(64)),
            ],
            Type::Unit,
        ),
        body(
            vec![Stmt::Eval(Expr::WriteBack {
                node: BorrowNode::LocalRoot(VarId::from("parent")),
                edge: BorrowEdge::MapKey {
                    key_type: Type::UInt(64),
                    value_type: Type::UInt(64),
                },
                child: VarId::from("child"),
                world: None,
            })],
            Expr::Unit,
        ),
        0,
    );
    add_function(&mut prog, 0, f);

    let out = render_program(&prog).expect("render");
    assert!(
        out.contains("TypedMap.set"),
        "missing TypedMap.set call: {out}"
    );
    // Slice 2 of item B (plans/lean-pipeline/item-b-real-anykey-work-plan.md):
    // primitive `key_type` now emits a real `AnyKey.k_u64 <key>`
    // wrap as the key argument to `TypedMap.set`. The recovered
    // key is `default` because `child` isn't bound by a preceding
    // `Expr::BorrowMapKey` in this synthetic fixture; the wrap
    // shape itself is the real one.
    assert!(
        out.contains("AnyKey.k_u64"),
        "expected real AnyKey.k_u64 wrap in TypedMap.set: {out}"
    );
}
