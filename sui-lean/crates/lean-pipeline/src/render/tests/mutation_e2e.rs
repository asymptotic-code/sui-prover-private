//! End-to-end render tests for the full Mutation-prelude migration.
//! Confirms the legacy `Mutable.mk` / `r.val` / `Mutable.set` emissions
//! all now lower to `Prover.Mutation.Mutation.*`.

use crate::ir::{
    BorrowEdge, BorrowNode, Expr, Field, Program, Signature, Stmt, Struct, Type, VarId, Variant,
};
use crate::render::render_program;

use super::fixtures::*;

fn add_uid_type(prog: &mut Program) -> Type {
    prog.modules.insert(
        1,
        crate::ir::Module {
            name: "object".to_string(),
            package_name: "Sui".to_string(),
            address: String::new(),
            required_imports: Vec::new(),
            is_native: true,
        },
    );
    add_struct(
        prog,
        12,
        Struct {
            module_id: 1,
            name: "UID".to_string(),
            qualified_name: "object::UID".to_string(),
            type_params: Vec::new(),
            fields: Vec::new(),
            variants: None,
            is_native: true,
        },
    );
    Type::Struct {
        struct_id: 12,
        type_args: Vec::new(),
    }
}

fn add_bag_type(prog: &mut Program) -> Type {
    prog.modules.insert(
        1,
        crate::ir::Module {
            name: "bag".to_string(),
            package_name: "Sui".to_string(),
            address: String::new(),
            required_imports: Vec::new(),
            is_native: true,
        },
    );
    add_struct(
        prog,
        12,
        Struct {
            module_id: 1,
            name: "Bag".to_string(),
            qualified_name: "bag::Bag".to_string(),
            type_params: Vec::new(),
            fields: Vec::new(),
            variants: None,
            is_native: true,
        },
    );
    Type::Struct {
        struct_id: 12,
        type_args: Vec::new(),
    }
}

#[test]
fn type_mutable_ref_renders_as_mutation_abbrev() {
    let mut prog = empty_program();
    let f = func(
        "f",
        sig(
            vec![param(
                "r",
                Type::MutableRef {
                    inner: Box::new(Type::UInt(64)),
                    root: Box::new(Type::UInt(64)),
                },
            )],
            Type::UInt(64),
        ),
        body(vec![], var("r")),
        0,
    );
    add_function(&mut prog, 0, f);
    let out = render_program(&prog).expect("render");
    assert!(
        out.contains("(Mutation (BoundedNat (2^64)))"),
        "Type::MutableRef should render to (Mutation T) abbrev: {out}"
    );
    assert!(
        !out.contains("(Mutable "),
        "legacy Mutable type spelling should be gone: {out}"
    );
}

#[test]
fn borrow_loc_emits_mutation_of_local() {
    let mut prog = empty_program();
    let f = func(
        "f",
        sig(
            vec![param("x", Type::UInt(64))],
            Type::MutableRef {
                inner: Box::new(Type::UInt(64)),
                root: Box::new(Type::UInt(64)),
            },
        ),
        body(vec![], Expr::BorrowLoc(VarId::from("x"))),
        0,
    );
    add_function(&mut prog, 0, f);
    let out = render_program(&prog).expect("render");
    assert!(
        out.contains("Prover.Mutation.Mutation.ofLocal"),
        "BorrowLoc should emit ofLocal: {out}"
    );
}

#[test]
fn read_ref_emits_val_accessor() {
    let mut prog = empty_program();
    let f = func(
        "f",
        sig(
            vec![param(
                "r",
                Type::MutableRef {
                    inner: Box::new(Type::UInt(64)),
                    root: Box::new(Type::UInt(64)),
                },
            )],
            Type::UInt(64),
        ),
        body(vec![], Expr::ReadRef(Box::new(var("r")))),
        0,
    );
    add_function(&mut prog, 0, f);
    let out = render_program(&prog).expect("render");
    // `.val` works against Mutation too (the prelude field is named
    // `val`); no Mutation.deref Call needed.
    assert!(out.contains(".val"), "ReadRef should emit .val: {out}");
}

#[test]
fn write_ref_emits_mutation_set() {
    let mut prog = empty_program();
    let f = func(
        "f",
        sig(
            vec![
                param(
                    "r",
                    Type::MutableRef {
                        inner: Box::new(Type::UInt(64)),
                        root: Box::new(Type::UInt(64)),
                    },
                ),
                param("v", Type::UInt(64)),
            ],
            Type::MutableRef {
                inner: Box::new(Type::UInt(64)),
                root: Box::new(Type::UInt(64)),
            },
        ),
        body(
            vec![],
            Expr::WriteRef {
                reference: Box::new(var("r")),
                value: Box::new(var("v")),
            },
        ),
        0,
    );
    add_function(&mut prog, 0, f);
    let out = render_program(&prog).expect("render");
    assert!(
        out.contains("Prover.Mutation.Mutation.set"),
        "WriteRef should emit Mutation.set: {out}"
    );
    assert!(
        !out.contains("Mutable.set"),
        "legacy Mutable.set should be gone: {out}"
    );
}

#[test]
fn writeback_local_root_struct_field_unchanged_shape() {
    // WriteBack { LocalRoot(x), StructField, child } -- emits the
    // `{ x with f := child.val }` direct-update form. Migration of
    // Mutable inner-only `.val` references didn't change this arm.
    let mut prog = empty_program();
    let s = Struct {
        module_id: 0,
        name: "S".to_string(),
        qualified_name: "p::m::S".to_string(),
        type_params: vec![],
        fields: vec![Field {
            name: "f".to_string(),
            field_type: Type::UInt(64),
        }],
        variants: None,
        is_native: false,
    };
    add_struct(&mut prog, 7, s);
    let f = func(
        "f",
        sig(
            vec![
                param(
                    "x",
                    Type::Struct {
                        struct_id: 7,
                        type_args: vec![],
                    },
                ),
                param("child", Type::UInt(64)),
            ],
            Type::Unit,
        ),
        body(
            vec![Stmt::Eval(Expr::WriteBack {
                node: BorrowNode::LocalRoot(VarId::from("x")),
                edge: BorrowEdge::StructField {
                    struct_id: 7,
                    field_index: 0,
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
        out.contains("with f"),
        "writeback to a struct field should use record-update syntax: {out}"
    );
}

#[test]
fn writeback_hyper_two_deep_struct_fields_composes_record_updates() {
    // WriteBack { LocalRoot(x), Hyper([StructField(Outer, 0), StructField(Inner, 0)]), child }
    // -- nested record-update: `{ x with f := { x.f with g := child.val } }`.
    let mut prog = empty_program();
    let inner = Struct {
        module_id: 0,
        name: "Inner".to_string(),
        qualified_name: "p::m::Inner".to_string(),
        type_params: vec![],
        fields: vec![Field {
            name: "g".to_string(),
            field_type: Type::UInt(64),
        }],
        variants: None,
        is_native: false,
    };
    let outer = Struct {
        module_id: 0,
        name: "Outer".to_string(),
        qualified_name: "p::m::Outer".to_string(),
        type_params: vec![],
        fields: vec![Field {
            name: "f".to_string(),
            field_type: Type::Struct {
                struct_id: 5,
                type_args: vec![],
            },
        }],
        variants: None,
        is_native: false,
    };
    add_struct(&mut prog, 5, inner);
    add_struct(&mut prog, 6, outer);
    let f = func(
        "f",
        sig(
            vec![
                param(
                    "x",
                    Type::Struct {
                        struct_id: 6,
                        type_args: vec![],
                    },
                ),
                param("child", Type::UInt(64)),
            ],
            Type::Unit,
        ),
        body(
            vec![Stmt::Eval(Expr::WriteBack {
                node: BorrowNode::LocalRoot(VarId::from("x")),
                edge: BorrowEdge::Hyper(vec![
                    BorrowEdge::StructField {
                        struct_id: 6,
                        field_index: 0,
                    },
                    BorrowEdge::StructField {
                        struct_id: 5,
                        field_index: 0,
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
    // Outer record-update wraps inner:
    assert!(
        out.contains("with f"),
        "outer StructField update missing: {out}"
    );
    assert!(
        out.contains("with g"),
        "inner StructField update missing: {out}"
    );
}

#[test]
fn writeback_hyper_struct_field_then_vec_index() {
    // WriteBack { LocalRoot(x), Hyper([StructField(S, 0), VecIndex]), child }
    // -- `{ x with f := x.f.set 0 child.val }`. The innermost VecIndex
    // defers to the single-edge handler which looks up the index in
    // borrow_sources (defaulting to `0` when child isn't a recognised
    // BorrowVecIndex var).
    let mut prog = empty_program();
    let s = Struct {
        module_id: 0,
        name: "S".to_string(),
        qualified_name: "p::m::S".to_string(),
        type_params: vec![],
        fields: vec![Field {
            name: "f".to_string(),
            field_type: Type::Vector(Box::new(Type::UInt(64))),
        }],
        variants: None,
        is_native: false,
    };
    add_struct(&mut prog, 7, s);
    let f = func(
        "f",
        sig(
            vec![
                param(
                    "x",
                    Type::Struct {
                        struct_id: 7,
                        type_args: vec![],
                    },
                ),
                param("child", Type::UInt(64)),
            ],
            Type::Unit,
        ),
        body(
            vec![Stmt::Eval(Expr::WriteBack {
                node: BorrowNode::LocalRoot(VarId::from("x")),
                edge: BorrowEdge::Hyper(vec![
                    BorrowEdge::StructField {
                        struct_id: 7,
                        field_index: 0,
                    },
                    BorrowEdge::VecIndex,
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
    assert!(out.contains("with f"), "StructField update missing: {out}");
    assert!(out.contains(".set"), "VecIndex `.set` form missing: {out}");
}

fn add_enum(prog: &mut Program, sid: usize) {
    let v0 = Variant {
        name: "A".to_string(),
        tag: 0,
        fields: vec![Field {
            name: "x".to_string(),
            field_type: Type::UInt(64),
        }],
    };
    let v1 = Variant {
        name: "B".to_string(),
        tag: 1,
        fields: vec![Field {
            name: "y".to_string(),
            field_type: Type::UInt(64),
        }],
    };
    let s = Struct {
        module_id: 0,
        name: "E".to_string(),
        qualified_name: "p::m::E".to_string(),
        type_params: vec![],
        fields: vec![],
        variants: Some(vec![v0, v1]),
        is_native: false,
    };
    add_struct(prog, sid, s);
}

#[test]
fn writeback_enum_field_emits_variant_match() {
    // WriteBack { LocalRoot(e), EnumField { sid, variant: 0, field: 0 }, child }
    // -> match e with | .A f0 => .A child.val | other => other
    fn build() -> Program {
        let mut prog = empty_program();
        add_enum(&mut prog, 9);
        let f = func(
            "f",
            sig(
                vec![
                    param(
                        "e",
                        Type::Struct {
                            struct_id: 9,
                            type_args: vec![],
                        },
                    ),
                    param("child", Type::UInt(64)),
                ],
                Type::Unit,
            ),
            body(
                vec![Stmt::Eval(Expr::WriteBack {
                    node: BorrowNode::LocalRoot(VarId::from("e")),
                    edge: BorrowEdge::EnumField {
                        struct_id: 9,
                        variant: 0,
                        field_index: 0,
                    },
                    child: VarId::from("child"),
                    world: None,
                })],
                Expr::Unit,
            ),
            0,
        );
        add_function(&mut prog, 0, f);
        prog
    }
    let prog = build();
    let out = render_program(&prog).expect("render");
    assert!(
        out.contains("match e"),
        "expected variant-aware match: {out}"
    );
    assert!(out.contains(".A"), "expected variant `.A` reference: {out}");
    assert!(
        out.contains("| other => other"),
        "expected variant fallthrough: {out}"
    );
}

#[test]
fn writeback_hyper_struct_then_enum_field() {
    // WriteBack { LocalRoot(s), Hyper([StructField(S, 0), EnumField(E, 0, 0)]), child }
    // -- struct's field is an enum; mutate the enum's variant-0 field.
    let mut prog = empty_program();
    add_enum(&mut prog, 9);
    let outer = Struct {
        module_id: 0,
        name: "Outer".to_string(),
        qualified_name: "p::m::Outer".to_string(),
        type_params: vec![],
        fields: vec![Field {
            name: "e".to_string(),
            field_type: Type::Struct {
                struct_id: 9,
                type_args: vec![],
            },
        }],
        variants: None,
        is_native: false,
    };
    add_struct(&mut prog, 10, outer);
    let f = func(
        "f",
        sig(
            vec![
                param(
                    "s",
                    Type::Struct {
                        struct_id: 10,
                        type_args: vec![],
                    },
                ),
                param("child", Type::UInt(64)),
            ],
            Type::Unit,
        ),
        body(
            vec![Stmt::Eval(Expr::WriteBack {
                node: BorrowNode::LocalRoot(VarId::from("s")),
                edge: BorrowEdge::Hyper(vec![
                    BorrowEdge::StructField {
                        struct_id: 10,
                        field_index: 0,
                    },
                    BorrowEdge::EnumField {
                        struct_id: 9,
                        variant: 0,
                        field_index: 0,
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
    assert!(out.contains("with e"), "outer StructField update: {out}");
    assert!(
        out.contains("match s.e"),
        "inner variant match on enum sub-field: {out}"
    );
    assert!(
        out.contains("| other => other"),
        "variant fallthrough: {out}"
    );
}

#[test]
fn writeback_spec_global_root_emits_ghost_stub() {
    // WriteBack { SpecGlobalRoot { type_args: [..] }, Direct, child }
    // -- the renderer emits a `Prover.Mutation.writeBackSpecGlobal`
    // call, returning Unit so the surrounding `Stmt::Eval` evaluates
    // cleanly. No client currently exercises this path; the prelude
    // helper is a no-op stub the verification harness can replace.
    use crate::ir::Variant;
    let _ = Variant {
        name: "_".to_string(),
        tag: 0,
        fields: vec![],
    };
    let mut prog = empty_program();
    let f = func(
        "f",
        sig(vec![param("child", Type::UInt(64))], Type::Unit),
        body(
            vec![Stmt::Eval(Expr::WriteBack {
                node: BorrowNode::SpecGlobalRoot {
                    type_args: vec![Type::UInt(64), Type::Bool],
                },
                edge: BorrowEdge::Direct,
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
        out.contains("Prover.Mutation.writeBackSpecGlobal"),
        "expected writeBackSpecGlobal stub call: {out}"
    );
    assert!(
        out.contains("SpecGlobalRoot writeback"),
        "expected mangle comment: {out}"
    );
}

#[test]
fn is_parent_spec_global_root_emits_false() {
    // IsParent { node: SpecGlobalRoot, edge: ..., child } -- ghost
    // vars never share a Loc with local-rooted Mutations, so the
    // renderer emits a literal `false` instead of `Mutation.isParent`.
    let mut prog = empty_program();
    let f = func(
        "f",
        sig(vec![param("child", Type::UInt(64))], Type::Bool),
        body(
            vec![],
            Expr::IsParent {
                node: BorrowNode::SpecGlobalRoot {
                    type_args: vec![Type::Address],
                },
                edge: BorrowEdge::Direct,
                child: VarId::from("child"),
            },
        ),
        0,
    );
    add_function(&mut prog, 0, f);
    let out = render_program(&prog).expect("render");
    assert!(
        out.contains("false"),
        "expected literal false for IsParent on SpecGlobalRoot: {out}"
    );
    assert!(
        !out.contains("isParent"),
        "should NOT emit isParent wrapper: {out}"
    );
}

#[test]
fn writeback_hyper_non_trailing_dynamic_edges_uses_path_match() {
    // WriteBack { LocalRoot(uid), Hyper([MapKey { K=u64, V=Vec<u64> }, VecIndex]), child }
    // -- a dynamic field `df<u64, Vector<u64>>::<key>[<index>]` writeback. The
    // MapKey edge is in non-trailing position; the renderer must
    // recover both the runtime key and the runtime vec-index from
    // `child.path` via a pattern-match on the path suffix.
    let mut prog = empty_program();
    let uid = add_uid_type(&mut prog);
    let f = func(
        "f",
        sig(
            vec![param("uid", uid), param("child", Type::UInt(64))],
            Type::Unit,
        ),
        body(
            vec![Stmt::Eval(Expr::WriteBack {
                node: BorrowNode::LocalRoot(VarId::from("uid")),
                edge: BorrowEdge::Hyper(vec![
                    BorrowEdge::MapKey {
                        key_type: Type::UInt(64),
                        value_type: Type::Vector(Box::new(Type::UInt(64))),
                    },
                    BorrowEdge::VecIndex,
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
    // Path-match form: pattern matches the dynamic-edge constructors
    // (mapKey + vecIndex), but the arm body collapses to identity on
    // the parent value, matching the single-level MapKey writeback
    // policy. See `render_nested_update_str`'s `BorrowEdge::MapKey`
    // branch for the rationale (AnyKey placeholder + Sui dynamic-
    // field root cannot recurse `TypedMap.set` through the parent
    // struct value).
    assert!(
        out.contains(".mapKey"),
        "expected .mapKey pattern in path match: {out}"
    );
    assert!(
        out.contains(".vecIndex"),
        "expected .vecIndex pattern in path match: {out}"
    );
    // After the identity collapse, the arm body should just be the
    // parent local (`uid`). No TypedMap.set / .get / vector .set
    // should appear inside this function body.
    let body_starts = out.find("def f").unwrap_or(0);
    let body = &out[body_starts..];
    assert!(
        !body.contains("TypedMap.set"),
        "MapKey arms should not emit TypedMap.set (identity collapse): {body}"
    );
    assert!(
        !body.contains("TypedMap.get"),
        "MapKey arms should not emit TypedMap.get (identity collapse): {body}"
    );
}

#[test]
fn writeback_hyper_mapkey_on_non_container_fails_closed() {
    let mut prog = empty_program();
    let f = func(
        "f",
        sig(
            vec![
                param("not_a_container", Type::UInt(64)),
                param("child", Type::UInt(64)),
            ],
            Type::Unit,
        ),
        body(
            vec![Stmt::Eval(Expr::WriteBack {
                node: BorrowNode::LocalRoot(VarId::from("not_a_container")),
                edge: BorrowEdge::Hyper(vec![
                    BorrowEdge::MapKey {
                        key_type: Type::UInt(64),
                        value_type: Type::Vector(Box::new(Type::UInt(64))),
                    },
                    BorrowEdge::VecIndex,
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
        out.contains("render fallback")
            && out.contains("MapKey container is not a supported map or dynamic-field root"),
        "arbitrary MapKey containers must fail closed: {out}"
    );
}

#[test]
fn writeback_hyper_bag_mapkey_keeps_intentional_identity() {
    let mut prog = empty_program();
    let bag = add_bag_type(&mut prog);
    let f = func(
        "f",
        sig(
            vec![param("bag", bag), param("child", Type::UInt(64))],
            Type::Unit,
        ),
        body(
            vec![Stmt::Eval(Expr::WriteBack {
                node: BorrowNode::LocalRoot(VarId::from("bag")),
                edge: BorrowEdge::Hyper(vec![
                    BorrowEdge::MapKey {
                        key_type: Type::UInt(64),
                        value_type: Type::Vector(Box::new(Type::UInt(64))),
                    },
                    BorrowEdge::VecIndex,
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
    assert!(out.contains(".mapKey"), "missing Bag path match: {out}");
    assert!(
        !out.contains("render fallback") && !out.contains("_root_.Bag.set"),
        "Bag writeback should retain its intentional identity step: {out}"
    );
}

#[test]
fn writeback_hyper_struct_field_then_two_dynamic_edges() {
    // WriteBack { LocalRoot(s), Hyper([StructField(S,0), MapKey, VecIndex]), child }
    // -- struct field is a UID; mutate its dynamic field value s.id[k][i]. Path
    // length is 3; only the trailing VecIndex would be lookup-able via
    // borrow_sources (and only for `child` directly). Non-trailing
    // MapKey forces the path-match form.
    let mut prog = empty_program();
    let uid = add_uid_type(&mut prog);
    let s = Struct {
        module_id: 0,
        name: "S".to_string(),
        qualified_name: "p::m::S".to_string(),
        type_params: vec![],
        fields: vec![Field {
            name: "id".to_string(),
            field_type: uid,
        }],
        variants: None,
        is_native: false,
    };
    add_struct(&mut prog, 11, s);
    let f = func(
        "f",
        sig(
            vec![
                param(
                    "s",
                    Type::Struct {
                        struct_id: 11,
                        type_args: vec![],
                    },
                ),
                param("child", Type::UInt(64)),
            ],
            Type::Unit,
        ),
        body(
            vec![Stmt::Eval(Expr::WriteBack {
                node: BorrowNode::LocalRoot(VarId::from("s")),
                edge: BorrowEdge::Hyper(vec![
                    BorrowEdge::StructField {
                        struct_id: 11,
                        field_index: 0,
                    },
                    BorrowEdge::MapKey {
                        key_type: Type::Address,
                        value_type: Type::Vector(Box::new(Type::UInt(64))),
                    },
                    BorrowEdge::VecIndex,
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
    // Outer StructField pattern, mid MapKey pattern, inner VecIndex pattern.
    assert!(
        out.contains(".structField"),
        "expected .structField pattern: {out}"
    );
    assert!(out.contains(".mapKey"), "expected .mapKey pattern: {out}");
    assert!(
        out.contains(".vecIndex"),
        "expected .vecIndex pattern: {out}"
    );
    // Outer struct-field is still rendered as a record update.
    // The MapKey collapse to identity propagates back through the
    // surrounding StructField -- `{ s with f := s.f }` is a no-op
    // record update on the outer struct. It's still legal Lean
    // (and what the renderer naturally produces); the prover's
    // chain-tracking via augmented `borrow_mut` returns carries
    // the actual update.
    assert!(out.contains("with id"), "outer field update: {out}");
    let body_starts = out.find("def f").unwrap_or(0);
    let body = &out[body_starts..];
    assert!(
        !body.contains("TypedMap.set"),
        "MapKey arms should not emit TypedMap.set (identity collapse): {body}"
    );
}

#[test]
fn writeback_hyper_flattens_nested_hyper() {
    // Hyper([Hyper([SF1, SF2]), SF3]) should flatten to [SF1, SF2, SF3]
    // and produce a 3-deep nested record update.
    let mut prog = empty_program();
    for (sid, fname, inner_ty) in [
        (
            3u32,
            "a",
            Type::Struct {
                struct_id: 4,
                type_args: vec![],
            },
        ),
        (
            4u32,
            "b",
            Type::Struct {
                struct_id: 5,
                type_args: vec![],
            },
        ),
        (5u32, "c", Type::UInt(64)),
    ] {
        let s = Struct {
            module_id: 0,
            name: format!("S{}", sid),
            qualified_name: format!("p::m::S{}", sid),
            type_params: vec![],
            fields: vec![Field {
                name: fname.to_string(),
                field_type: inner_ty,
            }],
            variants: None,
            is_native: false,
        };
        add_struct(&mut prog, sid as usize, s);
    }
    let f = func(
        "f",
        sig(
            vec![
                param(
                    "x",
                    Type::Struct {
                        struct_id: 3,
                        type_args: vec![],
                    },
                ),
                param("child", Type::UInt(64)),
            ],
            Type::Unit,
        ),
        body(
            vec![Stmt::Eval(Expr::WriteBack {
                node: BorrowNode::LocalRoot(VarId::from("x")),
                edge: BorrowEdge::Hyper(vec![
                    BorrowEdge::Hyper(vec![
                        BorrowEdge::StructField {
                            struct_id: 3,
                            field_index: 0,
                        },
                        BorrowEdge::StructField {
                            struct_id: 4,
                            field_index: 0,
                        },
                    ]),
                    BorrowEdge::StructField {
                        struct_id: 5,
                        field_index: 0,
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
    for name in ["with a", "with b", "with c"] {
        assert!(
            out.contains(name),
            "missing {} in flattened Hyper output: {}",
            name,
            out
        );
    }
}

#[test]
fn writeback_reference_struct_field_uses_single_underscore() {
    // Regression for the gamma bug in
    // plans/lean-pipeline/lake-build-remaining-errors.md:
    // `WriteBack { node: Reference(parent_mut), edge: StructField, child }`
    // must render `@Mutation.set AnyKey _ parent_mut <inner>` with
    // exactly one underscore between `AnyKey` and the parent. An
    // extra underscore makes Lean treat the parent as the value
    // argument, double-wrapping the result type and producing
    // `Mutation AnyKey (Mutation T)` errors when the inner update
    // expression is applied to it.
    let mut prog = empty_program();
    let s = Struct {
        module_id: 0,
        name: "S".to_string(),
        qualified_name: "p::m::S".to_string(),
        type_params: vec![],
        fields: vec![Field {
            name: "f".to_string(),
            field_type: Type::UInt(64),
        }],
        variants: None,
        is_native: false,
    };
    add_struct(&mut prog, 5, s);
    let f = func(
        "f",
        sig(
            vec![
                param(
                    "parent_mut",
                    Type::MutableRef {
                        inner: Box::new(Type::Struct {
                            struct_id: 5,
                            type_args: vec![],
                        }),
                        root: Box::new(Type::Struct {
                            struct_id: 5,
                            type_args: vec![],
                        }),
                    },
                ),
                param("child", Type::UInt(64)),
            ],
            Type::Unit,
        ),
        body(
            vec![Stmt::Eval(Expr::WriteBack {
                node: BorrowNode::Reference(VarId::from("parent_mut")),
                edge: BorrowEdge::StructField {
                    struct_id: 5,
                    field_index: 0,
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
        out.contains("Prover.Mutation.Mutation.set"),
        "Reference WriteBack should emit Mutation.set: {out}"
    );
    // The fully-applied form is `@Mutation.set AnyKey _ <parent> <inner>`.
    // Look for `AnyKey _ ` followed by parent_mut -- one underscore,
    // not two.
    assert!(
        out.contains("Mutation.set AnyKey _ parent_mut"),
        "expected one underscore between AnyKey and parent_mut: {out}"
    );
    assert!(
        !out.contains("Mutation.set AnyKey _ _"),
        "extra underscore double-wraps the result in Mutation: {out}"
    );
}

#[test]
fn tail_tuple_coerces_value_form_into_mutation_at_return() {
    // The augmented-return type bridge: a function whose return type
    // is `(R, Mutation T)` (after stage-3 mut-to-let augmenting an
    // `&mut T` param) but whose body tail builds the tuple from a
    // native call that returns value-form `(R, T)` (after the
    // renderer's `strip_mutable_ref_in_type` on native return types). The
    // renderer wraps the value-form slot in `Mutation.ofLocal 0 _`
    // so the tail typechecks against the declared return type.
    //
    // Shape modeled here: a non-native source function `f` with
    // body
    //   let (a, b) := some_native(ctx);
    //   (a, b)
    // and signature `(Mutation TxContext) -> (Address × Mutation TxContext)`.
    // Stage 2 + 3 would have produced this IR in real packages
    // (see Tx_context_spec.fresh_object_address_spec).
    let mut prog = empty_program();
    let s = Struct {
        module_id: 0,
        name: "TxContext".to_string(),
        qualified_name: "p::m::TxContext".to_string(),
        type_params: vec![],
        fields: vec![Field {
            name: "sender".to_string(),
            field_type: Type::Address,
        }],
        variants: None,
        is_native: false,
    };
    add_struct(&mut prog, 1, s);

    // Native callee: `(ctx: TxContext) -> (Address, Mutation TxContext)`.
    // Stage 2 + 3 would produce this signature after augmenting an
    // `&mut TxContext` param. The renderer's strip_mutable_ref_in_type will
    // strip the MutableRef back to TxContext at inference time, so
    // the destructure binds value-form.
    let native_callee = native(
        "fresh_addr",
        sig(
            vec![param(
                "ctx",
                Type::Struct {
                    struct_id: 1,
                    type_args: vec![],
                },
            )],
            Type::Tuple(vec![
                Type::Address,
                Type::MutableRef {
                    inner: Box::new(Type::Struct {
                        struct_id: 1,
                        type_args: vec![],
                    }),
                    root: Box::new(Type::Struct {
                        struct_id: 1,
                        type_args: vec![],
                    }),
                },
            ]),
        ),
        0,
        crate::ir::Effects::CONSERVATIVE,
        true,
    );
    add_native(&mut prog, 0, native_callee);

    // Source caller: `(ctx: Mutation TxContext) -> (Address × Mutation TxContext)`.
    let tx_ty = Type::Struct {
        struct_id: 1,
        type_args: vec![],
    };
    let tx_mut_ty = Type::MutableRef {
        inner: Box::new(tx_ty.clone()),
        root: Box::new(tx_ty.clone()),
    };
    let caller = func(
        "spec",
        sig(
            vec![param("ctx", tx_mut_ty.clone())],
            Type::Tuple(vec![Type::Address, tx_mut_ty.clone()]),
        ),
        body(
            vec![Stmt::Let {
                pattern: vec![Some(VarId::from("addr")), Some(VarId::from("ctx2"))],
                value: Expr::Call {
                    fun: 0,
                    type_args: vec![],
                    args: vec![var("ctx")],
                },
            }],
            Expr::Tuple(vec![var("addr"), var("ctx2")]),
        ),
        0,
    );
    add_function(&mut prog, 1, caller);

    let out = render_program(&prog).expect("render");
    // The tail tuple's second element should be wrapped in ofLocal
    // because `ctx2` is destructured as value-form `TxContext` but
    // the function's return type expects `Mutation TxContext` in
    // that slot.
    assert!(
        out.contains("ofLocal AnyKey _ 0 ctx2"),
        "expected ofLocal wrap on the second tuple slot: {out}"
    );
    // The first element (Address) is type-matched -- no wrap.
    // Look for the bare `(addr, (...ofLocal...))` shape.
    assert!(
        out.contains("(addr,"),
        "expected the first slot to be `addr` bare: {out}"
    );
}

#[test]
fn mutation_uninit_call_result_does_not_double_wrap_at_coercion() {
    // Companion to `tail_tuple_coerces_value_form_into_mutation_at_return`.
    // Most natives ship value-form returns (the renderer's
    // `strip_mutable_ref_in_type` on the signature's `MutableRef` slots is
    // correct), so a `MutableRef`-typed binding flowing into a
    // tail-tuple position legitimately gets coerced with
    // `Mutation.ofLocal`.
    //
    // `Mutation.uninit` is the exception: it's the synthetic native
    // registered by stage 2's `mutation_natives` to lower upstream
    // `Operation::Uninit`, and its hand-written Lean def already
    // ships its return value pre-wrapped in
    // `Prover.Mutation.Mutation`. Its IR signature carries
    // `MutableRef T`; its rendered effective type is `Mutation Key
    // T`. If `rendered_type_of` strips the `MutableRef` (the default
    // for natives), `render_expr_with_target_ty` sees an actual
    // `T` against a target `MutableRef T` at the tuple slot and
    // wraps with `Mutation.ofLocal` -- producing the spurious
    // `Mutation Key (Mutation Key T)` double-wrap that surfaces
    // downstream as a Prod.mk `Application type mismatch` in lake.
    //
    // The fix in `rendered_type_of`'s `Expr::Call` arm exempts
    // `callee.name() == "Mutation.uninit"` from the strip. This
    // test exercises that exemption.
    let mut prog = empty_program();

    // Synthetic native matching `mutation_natives::register`'s
    // signature exactly: `(i: u64) -> &mut T` (with `T` as a type
    // parameter). The name MUST be `Mutation.uninit` for the
    // exemption to fire.
    let t = Type::TypeParam(0);
    let uninit_native = crate::ir::NativeDecl {
        module: 0,
        name: "Mutation.uninit".to_string(),
        signature: Signature {
            type_params: vec!["T".to_string()],
            params: vec![param("i", Type::UInt(64))],
            return_type: Type::MutableRef {
                inner: Box::new(t.clone()),
                root: Box::new(t.clone()),
            },
        },
        effects: crate::ir::Effects::PURE,
        explicit_pure: false,
        is_framework: true,
        spec_target: None,
        user_native: None,
    };
    add_native(&mut prog, 0, uninit_native);

    // Source caller: `(real: &mut u64) -> (&mut u64 × &mut u64)`.
    // Body:
    //   let u := Mutation.uninit::<u64>(0);
    //   (u, real)
    //
    // After my fix `rendered_type_of` reports `var_types[u]` as
    // `MutableRef u64`, so the tail-tuple coercion at the first
    // slot sees actual=MutableRef u64 against target=MutableRef u64
    // and falls through without inserting `Mutation.ofLocal`.
    //
    // Before the fix `var_types[u]` was stripped to `u64`, so the
    // coercion saw actual=u64 against target=MutableRef u64,
    // matched the wrap arm, and emitted
    // `(Mutation.ofLocal AnyKey _ <slot> u)` -- producing
    // `Mutation Key (Mutation Key u64)` at runtime since `u`
    // already evaluates to a `Mutation Key u64`.
    let mut_ty = Type::MutableRef {
        inner: Box::new(Type::UInt(64)),
        root: Box::new(Type::UInt(64)),
    };
    let caller = func(
        "f",
        sig(
            vec![param("real", mut_ty.clone())],
            Type::Tuple(vec![mut_ty.clone(), mut_ty.clone()]),
        ),
        body(
            vec![Stmt::Let {
                pattern: vec![Some(VarId::from("u"))],
                value: Expr::Call {
                    fun: 0,
                    type_args: vec![Type::UInt(64)],
                    args: vec![lit_u64(0)],
                },
            }],
            Expr::Tuple(vec![var("u"), var("real")]),
        ),
        0,
    );
    add_function(&mut prog, 1, caller);

    let out = render_program(&prog).expect("render");

    // The Mutation.uninit call itself must still render via the
    // render_call special-case at expr.rs:2303 -- this is the
    // load-bearing rendering, unchanged by the inference fix.
    assert!(
        out.contains("Prover.Mutation.Mutation.uninit"),
        "missing Mutation.uninit call: {out}"
    );

    // The crucial assertion: `u` in the tail tuple's first slot
    // must NOT be wrapped in `Mutation.ofLocal`. Any text of the
    // shape `ofLocal AnyKey _ <slot> u` indicates the bug is back.
    assert!(
        !out.contains("ofLocal AnyKey _ 0 u)") && !out.contains("ofLocal AnyKey _ 1 u)"),
        "spurious double-wrap of Mutation.uninit-bound `u`: {out}"
    );

    // Sanity: `real` is already a `Mutation u64` (it's a parameter
    // with MutableRef type) so it also should not be wrapped. The
    // `(u, real)` shape is the canonical pass-through.
    assert!(
        !out.contains("ofLocal AnyKey _ 0 real)") && !out.contains("ofLocal AnyKey _ 1 real)"),
        "spurious wrap of already-Mutation `real`: {out}"
    );
}

fn mutable_uint(bits: u32) -> Type {
    Type::MutableRef {
        inner: Box::new(Type::UInt(bits)),
        root: Box::new(Type::UInt(bits)),
    }
}

fn call(fun: crate::ir::FunId, args: Vec<Expr>) -> Expr {
    Expr::Call {
        fun,
        type_args: vec![],
        args,
    }
}

#[test]
fn translated_call_arguments_cover_the_four_coercion_transitions() {
    let mut prog = empty_program();
    add_function(
        &mut prog,
        0,
        func(
            "accept_value",
            sig(vec![param("x", Type::UInt(64))], Type::UInt(64)),
            body(vec![], var("x")),
            0,
        ),
    );
    add_function(
        &mut prog,
        1,
        func(
            "accept_mut",
            sig(vec![param("x", mutable_uint(64))], mutable_uint(64)),
            body(vec![], var("x")),
            0,
        ),
    );
    let value_to_mut = crate::ir::Param {
        name: "vm".to_string(),
        var: VarId::from("$t7"),
        ty: Type::UInt(64),
    };
    add_function(
        &mut prog,
        2,
        func(
            "matrix",
            sig(
                vec![
                    param("vv", Type::UInt(64)),
                    value_to_mut,
                    param("mv", mutable_uint(64)),
                    param("mm", mutable_uint(64)),
                ],
                Type::Tuple(vec![
                    Type::UInt(64),
                    mutable_uint(64),
                    Type::UInt(64),
                    mutable_uint(64),
                ]),
            ),
            body(
                vec![],
                Expr::Tuple(vec![
                    call(0, vec![var("vv")]),
                    call(1, vec![var("$t7")]),
                    call(0, vec![var("mv")]),
                    call(1, vec![var("mm")]),
                ]),
            ),
            0,
        ),
    );

    let out = render_program(&prog).expect("render");
    assert!(out.contains("accept_value vv"), "value pass-through: {out}");
    assert!(
        out.contains("accept_mut (@Prover.Mutation.Mutation.ofLocal AnyKey _ 7 vm)"),
        "value-to-Mutation wrap: {out}"
    );
    assert!(
        out.contains("accept_value mv.val"),
        "Mutation-to-value unwrap: {out}"
    );
    assert!(
        out.contains("accept_mut mm"),
        "Mutation pass-through: {out}"
    );
}

#[test]
fn singleton_mutation_shapes_use_the_same_call_coercion_policy() {
    let mut prog = empty_program();
    add_function(
        &mut prog,
        0,
        func(
            "accept_value",
            sig(vec![param("x", Type::UInt(64))], Type::UInt(64)),
            body(vec![], var("x")),
            0,
        ),
    );
    add_function(
        &mut prog,
        1,
        func(
            "accept_singleton_mut",
            sig(
                vec![param("x", Type::Tuple(vec![mutable_uint(64)]))],
                Type::Tuple(vec![mutable_uint(64)]),
            ),
            body(vec![], var("x")),
            0,
        ),
    );
    add_function(
        &mut prog,
        2,
        func(
            "produce_singleton_mut",
            sig(
                vec![param("r", mutable_uint(64))],
                Type::Tuple(vec![mutable_uint(64)]),
            ),
            body(vec![], Expr::Tuple(vec![var("r")])),
            0,
        ),
    );
    let singleton_value = crate::ir::Param {
        name: "sv".to_string(),
        var: VarId::from("$t8"),
        ty: Type::UInt(64),
    };
    add_function(
        &mut prog,
        3,
        func(
            "singleton_matrix",
            sig(
                vec![singleton_value, param("r", mutable_uint(64))],
                Type::Tuple(vec![mutable_uint(64), Type::UInt(64)]),
            ),
            body(
                vec![],
                Expr::Tuple(vec![
                    call(1, vec![var("$t8")]),
                    call(0, vec![call(2, vec![var("r")])]),
                ]),
            ),
            0,
        ),
    );

    let out = render_program(&prog).expect("render");
    assert!(
        out.contains("accept_singleton_mut (@Prover.Mutation.Mutation.ofLocal AnyKey _ 8 sv)"),
        "singleton target should wrap: {out}"
    );
    assert!(
        out.contains("produce_singleton_mut r)).val"),
        "singleton call result should unwrap: {out}"
    );
}

#[test]
fn native_mutable_ref_parameters_still_use_the_value_form_abi() {
    let mut prog = empty_program();
    add_native(
        &mut prog,
        0,
        native(
            "native_take",
            sig(vec![param("x", mutable_uint(64))], Type::UInt(64)),
            0,
            crate::ir::Effects::PURE,
            true,
        ),
    );
    add_function(
        &mut prog,
        1,
        func(
            "caller",
            sig(vec![param("r", mutable_uint(64))], Type::UInt(64)),
            body(vec![], call(0, vec![var("r")])),
            0,
        ),
    );

    let out = render_program(&prog).expect("render");
    assert!(
        out.contains("native_take r.val"),
        "native ABI should receive the value form: {out}"
    );
}

#[test]
fn mismatched_mutation_inner_types_are_left_for_lean_to_reject() {
    let mut prog = empty_program();
    add_function(
        &mut prog,
        0,
        func(
            "accept_u8_mut",
            sig(vec![param("x", mutable_uint(8))], mutable_uint(8)),
            body(vec![], var("x")),
            0,
        ),
    );
    add_function(
        &mut prog,
        1,
        func(
            "caller",
            sig(vec![param("r64", mutable_uint(64))], mutable_uint(8)),
            body(vec![], call(0, vec![var("r64")])),
            0,
        ),
    );

    let out = render_program(&prog).expect("render");
    assert!(
        out.contains("accept_u8_mut r64"),
        "Mutation should pass through without representation churn: {out}"
    );
    assert!(!out.contains("r64.val"), "must not unwrap: {out}");
    assert!(
        !out.contains("ofLocal AnyKey _ 0 r64"),
        "must not re-wrap: {out}"
    );
    assert!(!out.contains("sorry"), "must fail closed in Lean: {out}");
}
