use ethnum::U256;

use crate::ir::{Const, Type};
use crate::render::writer::LeanWriter;

fn u8_const(value: u8) -> Const {
    Const::UInt {
        bits: 8,
        value: U256::from(value),
    }
}

fn vector(elems: Vec<Const>) -> Const {
    Const::Vector {
        elem_type: Type::UInt(8),
        elems,
    }
}

fn render_const(value: &Const) -> String {
    let mut writer = LeanWriter::new(String::new());
    super::super::expr::render_const(value, &mut writer).expect("constant renders");
    writer.into_inner()
}

#[test]
fn homogeneous_nontrivial_vector_uses_list_replicate() {
    assert_eq!(
        render_const(&vector(vec![u8_const(7); 4])),
        "(List.replicate 4 (7 : BoundedNat (2^8)))"
    );
}

#[test]
fn compact_vector_recursively_uses_the_constant_renderer() {
    let inner = Const::Vector {
        elem_type: Type::Bool,
        elems: vec![Const::Bool(true), Const::Bool(false)],
    };
    let outer = Const::Vector {
        elem_type: Type::Vector(Box::new(Type::Bool)),
        elems: vec![inner; 4],
    };

    assert_eq!(render_const(&outer), "(List.replicate 4 [true, false])");
}

#[test]
fn empty_and_small_vectors_keep_list_literal_rendering() {
    assert_eq!(render_const(&vector(vec![])), "[]");
    assert_eq!(
        render_const(&vector(vec![u8_const(7); 3])),
        "[(7 : BoundedNat (2^8)), (7 : BoundedNat (2^8)), (7 : BoundedNat (2^8))]"
    );
}

#[test]
fn heterogeneous_vector_keeps_list_literal_rendering() {
    assert_eq!(
        render_const(&vector(vec![
            u8_const(7),
            u8_const(7),
            u8_const(8),
            u8_const(7),
        ])),
        "[(7 : BoundedNat (2^8)), (7 : BoundedNat (2^8)), (8 : BoundedNat (2^8)), (7 : BoundedNat (2^8))]"
    );
}
