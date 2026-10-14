//! Type rendering coverage.

use super::super::ty::type_to_string;
use crate::ir::{Field, Module, Struct, Type};

use super::fixtures::*;

#[test]
fn unit_renders_as_unit() {
    let prog = empty_program();
    assert_eq!(type_to_string(&Type::Unit, &prog, Some("M"), None), "Unit");
}

#[test]
fn bool_renders_as_bool() {
    let prog = empty_program();
    assert_eq!(type_to_string(&Type::Bool, &prog, Some("M"), None), "Bool");
}

#[test]
fn uint64_renders_as_bounded_nat() {
    let prog = empty_program();
    assert_eq!(
        type_to_string(&Type::UInt(64), &prog, Some("M"), None),
        "BoundedNat (2^64)"
    );
}

#[test]
fn tuple_pair_renders_with_product() {
    let prog = empty_program();
    let t = Type::Tuple(vec![Type::UInt(64), Type::Bool]);
    assert_eq!(
        type_to_string(&t, &prog, Some("M"), None),
        "(BoundedNat (2^64) \u{00D7} Bool)"
    );
}

#[test]
fn empty_tuple_renders_as_unit() {
    let prog = empty_program();
    let t = Type::Tuple(vec![]);
    assert_eq!(type_to_string(&t, &prog, Some("M"), None), "Unit");
}

#[test]
fn singleton_tuple_renders_as_inner() {
    let prog = empty_program();
    let t = Type::Tuple(vec![Type::Bool]);
    assert_eq!(type_to_string(&t, &prog, Some("M"), None), "Bool");
}

#[test]
fn vector_renders_with_list_paren() {
    let prog = empty_program();
    let t = Type::Vector(Box::new(Type::UInt(64)));
    // Inner BoundedNat is multi-token; must be paren-wrapped or Lean
    // parses `List BoundedNat (2^64)` as application of `(2^64)` to
    // `(List BoundedNat)`.
    assert_eq!(
        type_to_string(&t, &prog, Some("M"), None),
        "(List (BoundedNat (2^64)))"
    );
}

#[test]
fn mutable_ref_renders_as_mutation_prelude_type() {
    // Per `plans/lean-pipeline/mutable-references.md`, `Type::MutableRef`
    // now renders to the typed-Mutation prelude. `Mutation` is the
    // per-package abbreviation (`Mutation := Prover.Mutation.Mutation AnyKey`).
    // The legacy `root` field at the Lean type level is gone -- the
    // runtime root lives in the value's `loc`.
    let prog = empty_program();
    let t = Type::MutableRef {
        inner: Box::new(Type::UInt(64)),
        root: Box::new(Type::UInt(64)),
    };
    assert_eq!(
        type_to_string(&t, &prog, Some("M"), None),
        "(Mutation (BoundedNat (2^64)))"
    );
}

#[test]
fn immutable_ref_is_erased() {
    let prog = empty_program();
    let t = Type::Reference(Box::new(Type::Bool));
    assert_eq!(type_to_string(&t, &prog, Some("M"), None), "Bool");
}

#[test]
fn borrow_loc_of_immutable_reference_infers_mutable_ref_of_value() {
    // Render-side mirror of the `ir::analysis::type_of` regression:
    // `rendered_type_of` for `BorrowLoc(v)` where `v : &vector<u8>` (an
    // erased immutable-ref value stored into a local by upstream
    // EliminateImmRefs) must report `MutableRef { Vector }`, so the
    // following `vector::borrow_mut` renders as `Mutation u8` -- NOT
    // `MutableRef { Reference(Vector) }`, a `&mut &T` with no Lean form.
    // sui-system `metadata_invalid_equal_both_pubkey_next_epoch`.
    use crate::ir::{Expr, VarId};
    use crate::render::expr::rendered_type_of;
    use std::collections::BTreeMap;

    let prog = empty_program();
    let pk: VarId = "pk".into();
    let vec_u8 = Type::Vector(Box::new(Type::UInt(8)));
    let mut var_types: BTreeMap<VarId, Type> = BTreeMap::new();
    var_types.insert(pk.clone(), Type::Reference(Box::new(vec_u8.clone())));

    match rendered_type_of(&Expr::BorrowLoc(pk), &prog, &var_types) {
        Some(Type::MutableRef { inner, root }) => {
            assert_eq!(*inner, vec_u8);
            assert_eq!(*root, vec_u8);
        }
        other => panic!("expected MutableRef of the erased value, got {other:?}"),
    }
}

#[test]
fn type_param_uses_declared_name() {
    let prog = empty_program();
    let params = vec!["T".to_string(), "U".to_string()];
    assert_eq!(
        type_to_string(&Type::TypeParam(0), &prog, Some("M"), Some(&params)),
        "T"
    );
    assert_eq!(
        type_to_string(&Type::TypeParam(1), &prog, Some("M"), Some(&params)),
        "U"
    );
}

#[test]
fn type_param_unbound_falls_back_to_wildcard() {
    let prog = empty_program();
    let params: Vec<String> = vec![];
    assert_eq!(
        type_to_string(&Type::TypeParam(0), &prog, Some("M"), Some(&params)),
        "_"
    );
}

#[test]
fn same_module_struct_skips_namespace() {
    // User-package modules now render to package-qualified
    // namespaces (`p.M` for the fixture's package `"p"`). The
    // `current_module` param must match the qualified namespace
    // for the renderer to skip the prefix on intra-module struct
    // references.
    let mut prog = empty_program();
    let s = simple_struct(0, "Pool", vec![("x", Type::UInt(64))]);
    add_struct(&mut prog, 0, s);
    let t = Type::Struct {
        struct_id: 0,
        type_args: vec![],
    };
    assert_eq!(type_to_string(&t, &prog, Some("p.M"), None), "Pool");
}

#[test]
fn cross_module_struct_uses_namespace() {
    // From `Other`, the fixture struct lives in `p.M`, so cross-
    // module references emit the fully-qualified `_root_.p.M.Pool`.
    // The `_root_.` prefix bypasses local-parameter shadows on the
    // package's first-segment name (e.g. a function param named `p`
    // would otherwise turn `p.M.Pool` into `(p).M.Pool`, a field
    // access on the parameter).
    let mut prog = empty_program();
    let s = simple_struct(0, "Pool", vec![("x", Type::UInt(64))]);
    add_struct(&mut prog, 0, s);
    let t = Type::Struct {
        struct_id: 0,
        type_args: vec![],
    };
    assert_eq!(
        type_to_string(&t, &prog, Some("Other"), None),
        "_root_.p.M.Pool"
    );
}

#[test]
fn types_file_cross_module_wit_table_uses_root_qualified_namespace() {
    let mut prog = empty_program();
    prog.modules.insert(
        1,
        Module {
            name: "wit_table".to_string(),
            package_name: "X".to_string(),
            address: String::new(),
            required_imports: Vec::new(),
            is_native: false,
        },
    );
    add_struct(
        &mut prog,
        1,
        Struct {
            module_id: 1,
            name: "WitTable".to_string(),
            qualified_name: "X::wit_table::WitTable".to_string(),
            type_params: Vec::new(),
            fields: vec![Field {
                name: "x".to_string(),
                field_type: Type::UInt(64),
            }],
            variants: None,
            is_native: false,
        },
    );
    let t = Type::Struct {
        struct_id: 1,
        type_args: vec![],
    };
    assert_eq!(
        type_to_string(&t, &prog, Some("X.Reserve_Types"), None),
        "_root_.X.Wit_table.WitTable"
    );
}
