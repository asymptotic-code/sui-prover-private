//! BCS `serialize` emitter goldens. These pin the EXACT byte encoding
//! the generated `TyCode.serialize` / `BagU.serialize` arms produce, so
//! Phase 2's hand-written Lean decoder has a stable contract to mirror.
//!
//! The encoding is documented atop
//! `render::dyn_type_universe::serialize_field_expr`. Worked golden
//! bytes for the `Meta` struct below (verified by `#eval` under the real
//! Prelude, Lean 4.32.0):
//!
//!   let m : Meta := { addr := <0x0102>, data := [0xAA, 0xBB],
//!                     maybe := some 7 }
//!   bcs(m) = bcsUIntBe 32 0x0102            -- 32 bytes: 30 x 0x00, 0x01, 0x02
//!         ++ (bcsUleb128 2 ++ [0xAA,0xBB])  -- 0x02, 0xAA, 0xBB
//!         ++ (1 :: [7])                     -- 0x01, 0x07  (Option "some")
//!
//! i.e. `[0x00 * 30, 0x01, 0x02,  0x02, 0xAA, 0xBB,  0x01, 0x07]`
//! (and with `maybe := none` the tail is a single `0x00`).

use crate::ir::{Field, Struct, Type, Variant};
use crate::render::dyn_type_universe::{
    bcs_serialize_body, bcs_serialize_wrapping_body, NativeBcs, WrappingStruct, NATIVE_BCS,
};
use crate::stage_02_ir_cfg::natives::is_native_struct;

use super::fixtures::{empty_program, module};

const OPTION_ID: usize = 10;
const BAG_ID: usize = 12;
const STRING_ID: usize = 14;
const ID_ID: usize = 16;
const UID_ID: usize = 18;
const TABLE_ID: usize = 20;
const VEC_SET_ID: usize = 22;

fn opt(inner: Type) -> Type {
    Type::Struct {
        struct_id: OPTION_ID,
        type_args: vec![inner],
    }
}

fn field(name: &str, ty: Type) -> Field {
    Field {
        name: name.to_string(),
        field_type: ty,
    }
}

fn plain_struct(id: usize, qualified: &str, name: &str, fields: Vec<Field>) -> Struct {
    Struct {
        module_id: 0,
        name: name.to_string(),
        qualified_name: qualified.to_string(),
        type_params: Vec::new(),
        fields,
        variants: None,
        is_native: false,
    }
}

/// A `Program` carrying `option::Option`, `bag::Bag`, and any extra
/// structs the caller supplies. Returns the leaf `Type` for struct `id`.
fn program_with(structs: Vec<Struct>) -> crate::ir::Program {
    let mut prog = empty_program();
    prog.modules.insert(0, module("m"));
    // option::Option<T> = { vec : vector<T> }
    prog.structs.insert(
        OPTION_ID,
        Struct {
            module_id: 0,
            name: "MoveOption".to_string(),
            qualified_name: "option::Option".to_string(),
            type_params: vec!["T".to_string()],
            fields: vec![field("vec", Type::Vector(Box::new(Type::TypeParam(0))))],
            variants: None,
            is_native: true,
        },
    );
    // bag::Bag = { id, size, storage } (projections are hard-coded; the
    // recorded field list is only needed so the struct resolves).
    prog.structs
        .insert(BAG_ID, plain_struct(BAG_ID, "bag::Bag", "Bag", vec![]));
    // std::string::String = { bytes : vector<u8> }. REGISTERED NATIVE
    // (`stage_02_ir_cfg::natives::NATIVE_STRUCTS`), unlike `ascii::String`
    // -- the field is nevertheless real, so BCS is the vector rule.
    prog.structs.insert(
        STRING_ID,
        Struct {
            module_id: 0,
            name: "MoveString".to_string(),
            qualified_name: "string::String".to_string(),
            type_params: Vec::new(),
            fields: vec![field("bytes", Type::Vector(Box::new(Type::UInt(8))))],
            variants: None,
            is_native: true,
        },
    );
    // The four registered natives whose Move fields the Lean prelude
    // really does expose (`NATIVE_BCS`'s `Walk` rows), spelled exactly
    // as `stage_02_ir_cfg::module_lift::lift_struct` records them from
    // the sui-framework sources.
    //   object::ID  = { bytes : address }
    //   object::UID = { id : ID }               (Lean adds a model-only `key`)
    //   table::Table<phantom K, phantom V> = { id : UID, size : u64 }
    //   vec_set::VecSet<K> = { contents : vector<K> }
    prog.structs.insert(
        ID_ID,
        native_struct(
            "ID",
            "object::ID",
            Vec::new(),
            vec![field("bytes", Type::Address)],
        ),
    );
    prog.structs.insert(
        UID_ID,
        native_struct(
            "UID",
            "object::UID",
            Vec::new(),
            vec![field(
                "id",
                Type::Struct {
                    struct_id: ID_ID,
                    type_args: vec![],
                },
            )],
        ),
    );
    prog.structs.insert(
        TABLE_ID,
        native_struct(
            "Table",
            "table::Table",
            vec!["K".to_string(), "V".to_string()],
            vec![
                field(
                    "id",
                    Type::Struct {
                        struct_id: UID_ID,
                        type_args: vec![],
                    },
                ),
                field("size", Type::UInt(64)),
            ],
        ),
    );
    prog.structs.insert(
        VEC_SET_ID,
        native_struct(
            "VecSet",
            "vec_set::VecSet",
            vec!["K".to_string()],
            vec![field(
                "contents",
                Type::Vector(Box::new(Type::TypeParam(0))),
            )],
        ),
    );
    for s in structs {
        let id = prog.structs.len() + 100; // avoid clashing with OPTION_ID/BAG_ID
        prog.structs.insert(id, s);
    }
    prog
}

fn native_struct(
    name: &str,
    qualified: &str,
    type_params: Vec<String>,
    fields: Vec<Field>,
) -> Struct {
    Struct {
        module_id: 0,
        name: name.to_string(),
        qualified_name: qualified.to_string(),
        type_params,
        fields,
        variants: None,
        is_native: true,
    }
}

fn leaf(prog: &crate::ir::Program, id: usize) -> String {
    let ty = Type::Struct {
        struct_id: id,
        type_args: vec![],
    };
    bcs_serialize_body(&ty, prog, "TyCode.serialize")
}

#[test]
fn serializes_leaf_struct_address_vector_option() {
    let meta = plain_struct(
        200,
        "validator::Meta",
        "Meta",
        vec![
            field("addr", Type::Address),
            field("data", Type::Vector(Box::new(Type::UInt(8)))),
            field("maybe", opt(Type::UInt(8))),
        ],
    );
    let prog = program_with(vec![meta]);
    // The single extra struct lands at id 100 + current len.
    let id = *prog
        .structs
        .iter()
        .find(|(_, s)| s.qualified_name == "validator::Meta")
        .map(|(id, _)| id)
        .unwrap();
    let got = leaf(&prog, id);
    let expected = "fun v => (bcsUIntBe 32 v.addr.bytes.val) ++ (bcsUleb128 v.data.length ++ v.data) ++ ((match v.maybe.vec with | [] => [(0 : BoundedNat (2^8))] | x0 :: _ => (1 : BoundedNat (2^8)) :: ([x0])))";
    assert_eq!(got, expected, "\n  got: {}\n want: {}", got, expected);
}

#[test]
fn serializes_vector_of_non_u8_with_flatmap() {
    let s = plain_struct(
        200,
        "m::VecHolder",
        "VecHolder",
        vec![field("xs", Type::Vector(Box::new(Type::UInt(16))))],
    );
    let prog = program_with(vec![s]);
    let id = *prog
        .structs
        .iter()
        .find(|(_, s)| s.qualified_name == "m::VecHolder")
        .map(|(id, _)| id)
        .unwrap();
    let got = leaf(&prog, id);
    let expected =
        "fun v => (bcsUleb128 v.xs.length ++ (v.xs.flatMap (fun x0 => bcsUIntLe 2 x0.val)))";
    assert_eq!(got, expected);
}

#[test]
fn serializes_bag_field_as_uid_and_size() {
    let s = plain_struct(
        200,
        "m::WithBag",
        "WithBag",
        vec![field(
            "b",
            Type::Struct {
                struct_id: BAG_ID,
                type_args: vec![],
            },
        )],
    );
    let prog = program_with(vec![s]);
    let id = *prog
        .structs
        .iter()
        .find(|(_, s)| s.qualified_name == "m::WithBag")
        .map(|(id, _)| id)
        .unwrap();
    let got = leaf(&prog, id);
    let expected = "fun v => (bcsUIntBe 32 v.b.id.id.bytes.bytes.val ++ bcsUIntLe 8 v.b.size.val)";
    assert_eq!(got, expected);
}

/// `std::string::String` is a REGISTERED native, so before the explicit
/// arm in `serialize_struct_value` it fell into the opaque-native
/// catch-all and every Move `String` serialized to NOTHING -- no faithful
/// BCS decode was possible for a struct with String fields (sui-system's
/// `ValidatorMetadata` lost 6 String fields and encoded 4 `Option<String>`
/// as bare tags). It must emit the vector rule: uleb128 length ++ bytes.
#[test]
fn serializes_string_leaf_with_uleb128_length() {
    let prog = program_with(vec![]);
    let got = leaf(&prog, STRING_ID);
    assert_eq!(got, "fun v => bcsUleb128 v.bytes.length ++ v.bytes");
}

/// The same bytes when `String` sits inside a struct, and `Option<String>`
/// must compose: the Option arm's 0/1 tag followed by the String payload
/// (NOT a bare tag). `ascii::String` is not a registered native and rides
/// the generic field walk, which already emitted the prefix -- pinned here
/// so the two spellings stay byte-identical.
#[test]
fn serializes_string_and_option_string_fields() {
    let string_ty = Type::Struct {
        struct_id: STRING_ID,
        type_args: vec![],
    };
    let ascii = plain_struct(
        201,
        "ascii::String",
        "MoveString",
        vec![field("bytes", Type::Vector(Box::new(Type::UInt(8))))],
    );
    let prog = program_with(vec![ascii]);
    let ascii_id = *prog
        .structs
        .iter()
        .find(|(_, s)| s.qualified_name == "ascii::String")
        .map(|(id, _)| id)
        .unwrap();
    let holder = plain_struct(
        202,
        "validator::Meta",
        "Meta",
        vec![
            field("name", string_ty.clone()),
            field("maybe_name", opt(string_ty)),
            field(
                "url",
                Type::Struct {
                    struct_id: ascii_id,
                    type_args: vec![],
                },
            ),
        ],
    );
    let mut prog = prog;
    prog.structs.insert(500, holder);
    let got = leaf(&prog, 500);
    let expected = "fun v => (bcsUleb128 v.name.bytes.length ++ v.name.bytes) \
++ ((match v.maybe_name.vec with | [] => [(0 : BoundedNat (2^8))] \
| x0 :: _ => (1 : BoundedNat (2^8)) :: (bcsUleb128 x0.bytes.length ++ x0.bytes))) \
++ ((bcsUleb128 v.url.bytes.length ++ v.url.bytes))";
    assert_eq!(got, expected, "\n  got: {}\n want: {}", got, expected);
}

/// The opaque natives (synthetic `dummy_field` placeholders that do not
/// exist on the rendered Lean type) must still serialize to `[]` -- the
/// String arm is a targeted exemption, not a general un-gating of
/// `is_native`.
#[test]
fn keeps_empty_for_opaque_native_struct() {
    let g1 = Struct {
        module_id: 0,
        name: "G1".to_string(),
        qualified_name: "bls12381::G1".to_string(),
        type_params: Vec::new(),
        fields: vec![field("dummy_field", Type::Bool)],
        variants: None,
        is_native: true,
    };
    let prog = program_with(vec![g1]);
    let id = *prog
        .structs
        .iter()
        .find(|(_, s)| s.qualified_name == "bls12381::G1")
        .map(|(id, _)| id)
        .unwrap();
    assert_eq!(leaf(&prog, id), "fun v => []");
}

/// `object::ID` is Move's `{ bytes: address }`, so its BCS is exactly
/// the 32 big-endian address bytes -- NOT `[]`, which is what the
/// `is_native` catch-all produced before `NATIVE_BCS` classified it
/// `Walk`. The Lean path is `bytes`(Address)`.bytes`(BoundedNat)`.val`.
#[test]
fn serializes_object_id_as_32_be_address_bytes() {
    let prog = program_with(vec![]);
    assert_eq!(
        leaf(&prog, ID_ID),
        "fun v => (bcsUIntBe 32 v.bytes.bytes.val)"
    );
}

/// `object::UID` wraps a single `ID`, so it is the same 32 bytes one
/// projection deeper. The prelude's `UID` also carries `key : Nat :=
/// id.bytes.bytes.val` -- a MODEL-ONLY map key that is not a Move field
/// and must never reach the wire; the walk iterates the IR field list,
/// so it cannot.
#[test]
fn serializes_object_uid_as_its_inner_id_only() {
    let prog = program_with(vec![]);
    assert_eq!(
        leaf(&prog, UID_ID),
        "fun v => ((bcsUIntBe 32 v.id.bytes.bytes.val))"
    );
}

/// `table::Table` is Move's `{ id: UID, size: u64 }` -- byte-identical
/// to `bag::Bag`, whose hard-coded arm above spells the same projection
/// path. Its entries live in dynamic-field storage, so the Lean-only
/// `dynamic_fields` is NOT serialized (mirroring Bag's `storage`).
#[test]
fn serializes_table_as_uid_and_size_like_bag() {
    let prog = program_with(vec![]);
    let w = WrappingStruct {
        struct_id: TABLE_ID,
        arity: 2,
    };
    let got = bcs_serialize_wrapping_body(&w, &prog, "TyCode.serialize");
    let expected =
        "fun v => (((bcsUIntBe 32 v.id.id.bytes.bytes.val))) ++ (bcsUIntLe 8 v.size.val)";
    assert_eq!(got, expected, "\n  got: {}\n want: {}", got, expected);
}

/// `vec_set::VecSet<K>` is `{ contents: vector<K> }`, and unlike
/// `option::Option` (whose Move layout is also a vector) BCS really does
/// treat it as one: uleb128 count ++ elements, recursing on the element
/// code `a0`.
#[test]
fn serializes_vec_set_as_its_contents_vector() {
    let prog = program_with(vec![]);
    let w = WrappingStruct {
        struct_id: VEC_SET_ID,
        arity: 1,
    };
    let got = bcs_serialize_wrapping_body(&w, &prog, "TyCode.serialize");
    let expected = "fun v => (bcsUleb128 v.contents.length ++ (v.contents.flatMap (fun x0 => TyCode.serialize a0 x0)))";
    assert_eq!(got, expected, "\n  got: {}\n want: {}", got, expected);
}

/// The composite case that motivated the fix: sui-system's `StakedSui`
/// is `{ id: UID, pool_id: ID, stake_activation_epoch: u64, principal:
/// Balance<SUI> }`, and its first two slots used to encode as NOTHING,
/// making a faithful decode impossible. Both are now 32 bytes.
#[test]
fn serializes_uid_and_id_fields_of_a_user_struct() {
    let staked_sui = plain_struct(
        200,
        "staking_pool::StakedSui",
        "StakedSui",
        vec![
            field(
                "id",
                Type::Struct {
                    struct_id: UID_ID,
                    type_args: vec![],
                },
            ),
            field(
                "pool_id",
                Type::Struct {
                    struct_id: ID_ID,
                    type_args: vec![],
                },
            ),
            field("stake_activation_epoch", Type::UInt(64)),
        ],
    );
    let prog = program_with(vec![staked_sui]);
    let id = *prog
        .structs
        .iter()
        .find(|(_, s)| s.qualified_name == "staking_pool::StakedSui")
        .map(|(id, _)| id)
        .unwrap();
    let got = leaf(&prog, id);
    let expected = "fun v => (((bcsUIntBe 32 v.id.id.bytes.bytes.val))) \
++ ((bcsUIntBe 32 v.pool_id.bytes.bytes.val)) \
++ (bcsUIntLe 8 v.stake_activation_epoch.val)";
    assert_eq!(got, expected, "\n  got: {}\n want: {}", got, expected);
}

/// Drift guard: a `Walk` row is only honored while the type still HAS
/// Move fields. If the upstream framework ever empties one, move_model
/// hands us the compiler's synthetic `dummy_field : bool`, which the
/// prelude's hand-written structure does not have -- fall back to `[]`
/// rather than emitting an accessor that cannot elaborate.
#[test]
fn keeps_empty_for_walkable_native_reduced_to_a_placeholder_field() {
    let mut prog = program_with(vec![]);
    prog.structs.insert(
        VEC_SET_ID,
        native_struct(
            "VecSet",
            "vec_set::VecSet",
            vec!["K".to_string()],
            vec![field("dummy_field", Type::Bool)],
        ),
    );
    let w = WrappingStruct {
        struct_id: VEC_SET_ID,
        arity: 1,
    };
    let got = bcs_serialize_wrapping_body(&w, &prog, "TyCode.serialize");
    assert_eq!(got, "fun v => []");
}

/// Every row of `NATIVE_BCS` must name a struct that is actually
/// registered in `stage_02_ir_cfg::natives::NATIVE_STRUCTS` -- the table
/// is a classification OF that list, and a typo'd or retired row would
/// silently classify nothing.
#[test]
fn native_bcs_rows_are_all_registered_natives() {
    for (qualified, _) in NATIVE_BCS {
        let (module, name) = qualified
            .split_once("::")
            .unwrap_or_else(|| panic!("`{}` is not `<module>::<Name>`", qualified));
        assert!(
            is_native_struct("MoveStdlib", module, name) || is_native_struct("Sui", module, name),
            "`{}` is classified in NATIVE_BCS but is not in NATIVE_STRUCTS",
            qualified
        );
    }
}

/// The classification is a census, not a sample: it covers every entry
/// of `NATIVE_STRUCTS` (39 at the time of writing), and the per-verdict
/// split is pinned so a re-classification cannot slip in unnoticed. A
/// registered native with NO row falls back to `[]` -- exactly the
/// silent-empty-BCS bug this table exists to prevent -- so bump these
/// only together with the rows themselves.
#[test]
fn native_bcs_classifies_every_registered_native() {
    assert_eq!(NATIVE_BCS.len(), 39);
    let mut names: Vec<&str> = NATIVE_BCS.iter().map(|(n, _)| *n).collect();
    names.sort_unstable();
    names.dedup();
    assert_eq!(names.len(), NATIVE_BCS.len(), "duplicate NATIVE_BCS row");

    let count = |want: NativeBcs| NATIVE_BCS.iter().filter(|(_, s)| *s == want).count();
    // ID, UID, Table, ObjectTable, VecSet, VecMap, Entry.
    assert_eq!(count(NativeBcs::Walk), 7);
    // string::String, bag::Bag, object_bag::ObjectBag.
    assert_eq!(count(NativeBcs::Special), 3);
    // integer, real, bls12381 x5, config x3, zklogin x2.
    assert_eq!(count(NativeBcs::Opaque), 12);
    // Real-fielded, still `[]` pending their own validation pass.
    assert_eq!(count(NativeBcs::Deferred), 17);
}

/// The `Walk` set, spelled out (rather than counted) so flipping a
/// `Deferred` row to `Walk` is a deliberate, reviewed edit and not a
/// one-word slip.
///
/// "Validated" means the prelude `structure` was read against the Move
/// field list and the corpora that render the arm were regenerated and
/// rebuilt green -- NOT that some obligation pins the new bytes. For the
/// `vec_map` pair no such obligation exists anywhere: the corpus-wide
/// `Bcs.to_bytes` sweep found no concrete instantiation that reaches a
/// `VecMap`-bearing arm, so the flip is unobservable by construction and
/// its evidence is the field-list match plus a byte-identical proof
/// outcome.
#[test]
fn native_bcs_walk_set_is_exactly_the_validated_types() {
    let mut walk: Vec<&str> = NATIVE_BCS
        .iter()
        .filter(|(_, s)| *s == NativeBcs::Walk)
        .map(|(n, _)| *n)
        .collect();
    walk.sort_unstable();
    assert_eq!(
        walk,
        vec![
            "object::ID",
            "object::UID",
            "object_table::ObjectTable",
            "table::Table",
            "vec_map::Entry",
            "vec_map::VecMap",
            "vec_set::VecSet",
        ]
    );
}

#[test]
fn keeps_empty_for_self_recursive_struct() {
    // Node { children : vector<Node> } -- vector-mediated self recursion.
    // Cannot be inlined without a `partial def`, so the arm stays `[]`.
    let mut prog = empty_program();
    prog.modules.insert(0, module("m"));
    prog.structs.insert(
        300,
        Struct {
            module_id: 0,
            name: "Node".to_string(),
            qualified_name: "m::Node".to_string(),
            type_params: Vec::new(),
            fields: vec![field(
                "children",
                Type::Vector(Box::new(Type::Struct {
                    struct_id: 300,
                    type_args: vec![],
                })),
            )],
            variants: None,
            is_native: false,
        },
    );
    let got = leaf(&prog, 300);
    assert_eq!(got, "fun _ => []");
}

#[test]
fn serializes_enum_with_uleb128_tag() {
    let color = Struct {
        module_id: 0,
        name: "Color".to_string(),
        qualified_name: "m::Color".to_string(),
        type_params: Vec::new(),
        fields: Vec::new(),
        variants: Some(vec![
            Variant {
                name: "Red".to_string(),
                tag: 0,
                fields: Vec::new(),
            },
            Variant {
                name: "Blue".to_string(),
                tag: 1,
                fields: vec![field("b", Type::UInt(8))],
            },
        ]),
        is_native: false,
    };
    let prog = program_with(vec![color]);
    let id = *prog
        .structs
        .iter()
        .find(|(_, s)| s.qualified_name == "m::Color")
        .map(|(id, _)| id)
        .unwrap();
    let got = leaf(&prog, id);
    let expected =
        "fun v => (match v with | .Red => bcsUleb128 0 | .Blue x0 => bcsUleb128 1 ++ ([x0]))";
    assert_eq!(got, expected);
}

#[test]
fn wrapping_option_recurses_through_the_element_code() {
    let prog = program_with(vec![]);
    let w = WrappingStruct {
        struct_id: OPTION_ID,
        arity: 1,
    };
    let got = bcs_serialize_wrapping_body(&w, &prog, "TyCode.serialize");
    let expected = "fun v => (match v.vec with | [] => [(0 : BoundedNat (2^8))] | x0 :: _ => (1 : BoundedNat (2^8)) :: (TyCode.serialize a0 x0))";
    assert_eq!(got, expected);
}
